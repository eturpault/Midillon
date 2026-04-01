"""
-------------------------------------------------------------------------------
 Name:        Midillon
 Purpose:     MIDI carillon permitting to play a virtual carillon from a MIDI file or a MIDI keyboard, using carillon bells audio samples

 Author:      Eric Turpault (France, Châtellerault)
 Copyright:   open source
 Licence:     GNU General Public License v3.0, please share the modifications with the author

 Versions history :
   v1 - 02 April 2026 - initial version


-------------------------------------------------------------------------------
"""

import os
import re
import time
import math
import struct
import datetime
import threading
import tkinter as tk
from   tkinter import ttk, filedialog

import mido          # library for working with MIDI ports/messages/files
import sounddevice   # library providing bindings for the PortAudio library

APP_NAME = 'Midillon'

ABOUT_MSG = """Version 1 - 02 Avril 2026
Eric Turpault - Châtellerault
eric.turpault@gmail.com

Fichier de définition de carillon : fichier pouvant contenir la définitions du clavier / pédalier et/ou du jeu automatique d'un carillon.

Répertoire d'échantillon sonores : répertoire contenant les échantillons sonores de cloches au format .wav, un fichier par cloche. Le nom des fichiers peut contenir un nom de note ou un numéro de note MIDI.

Un double-click sur le curseur de volume ou de vitesse remet sa position à 100%.
"""

# logs activation flags
LOG_wav_decode = False
LOG_wav_player = False
LOG_midi_messages = False

# name of the file in which are saved the data of the application
app_data_file_name = 'Midillon.ini'

# keys to identify the data of the application which are saved
midi_file_name_sel_key = 'Fichier MIDI utilisé'
midi_file_name_key = 'Fichier MIDI'
definition_file_name_sel_key = 'Fichier de définition du carillon utilisé'
definition_file_name_key = 'Fichier de définition du carillon'
samples_dir_sel_key = "Répertoire d'échantillons sonores utilisé"
samples_dir_key = "Répertoire d'échantillons sonores"

# keys to identify the data of the carillon definition file
carillon_name_key       = 'Nom'
keyboard_transpose_key  = 'Transposition clavier'
manual_first_key        = 'Clavier première touche'
manual_last_key         = 'Clavier dernière touche'
manual_missings_key     = 'Clavier touches manquantes'
manual_inactives_key    = 'Clavier touches inactives'
pedal_first_key         = 'Pédalier première touche'
pedal_last_key          = 'Pédalier dernière touche'
pedal_missings_key      = 'Pédalier touches manquantes'
pedal_inactives_key     = 'Pédalier touches inactives'
autoplayer_marks_nb_key = 'Nombre de repères'
autoplayer_rev_time_key = 'Temps de révolution'
autoplayer_lever_key    = 'Levier'

# minimum time in seconds (float) which is accepted between two activations of one lever of the autoplayer
lever_time_constant = 0.5

# latency in seconds (float) to set to the audio stream
audio_latency = 0.05

default_midi_velocity = 70
default_keyboard_first_key_midi_note = 36
default_keyboard_last_key_midi_note= 108

# colors of the keyboard keys when they are not pressed
color_key_active = "grey30"
color_key_inactive = "grey60"
color_key_active_pressed = "blue"
color_key_inactive_pressed = "red"

# global function to call in order to display logs in the application
logs_display_fct = None


#-------------------------------------------------------------------------------------------------
class C_WAV_PLAYER:
    # class to play wav files and mix several one in parallel

    # directory of the currently loaded audio samples
    loaded_samples_dir = None

    # flags indicating the functioning states
    samples_loading_in_progress = False
    samples_recording_in_progress = False

    recording_file = None
    recording_file_name = None

    # dictionnary containing the audio samples to play for each MIDI note
    #     key : MIDI note
    #     value : list of audio samples for playing the MIDI note in integer/float format
    samples_dic = {}

    # dictionnary containing the data of the streams that the player is currently rendering
    # key : MIDI note
    # value : list with following data [0: current playing position in the samples buffer, 1: number of samples in the buffer, 2: audio samples buffer, 3: audio volume]
    streams_dic = {}

    # semaphore indicating when the dictionary streams_dic is currently used in the audio_stream_loop function
    # used to prevent its modification at the same time in the start or stop functions
    streams_dic_in_use = False

    # PortAudio stream managed by the SoundDevice library
    stream = None

    # number of audio samples to manage at each loop of the SoundDevice stream
    # if 1 channel and sampling frequency 44100Hz, 1024 samples means a loop each 1024 / 44100 = 23ms
    samples_nb_per_loop = 512

    # properties of the audio samples (recovered from the first sample)
    sampling_frequency = 0
    bytes_per_sample = 0
    nb_of_channels = 0
    time_per_loop = 0
    struct_format = ''   # format to use with the struct functions to pack/unpack bytes samples

    audio_volume_factor = 1.0  # float value

    first_samples_emitted = False

    #-------------------------------------------------------------------------------------------------
    def wav_file_read(self, file_name):
        # return in a dictionary the metadata of the given .wav file (wave or wavpack format)
        # source code recovered from the OdfEdit.py file with parts removed for unused chunks

        # the returned keys are :
        #   file_format : "wave" or "wavpack" or None if error
        #   error_msg   : message describing an error occured during the file processing, empty string if no error
        #   metadata_recovered : True if the metadata of the file have been recovered successfully
        #   nb_of_channels   : 1=mono, 2=stereo
        #   sampling_rate    : for example 44100 (Hz)
        #   bits_per_sample  : for example 16 (bits)
        #   bytes_per_sample : for example 2 (if 16 bits)
        #   compression_code : 1='Microsoft PCM', 3='Microsoft IEEE float', several other...
        #   sample_data_type : 'uint8', 'int16', 'int24' or 'int32' if PCM format, 'float32' or 'float64' if IEEE format, None if not supported format
        #   nb_of_samples    : number of audio samples
        #   audio_data_size  : size in bytes of the sampled audio data
        #   audio_duration   : the duration in seconds (with two decimals) of the sampled data
        #   sampled_data     : bytes buffer containing the sampled audio data

        metadata_dic = {}
        metadata_dic['error_msg'] = ''
        metadata_dic['metadata_recovered'] = False
        metadata_dic['sampled_data'] = []

        if not os.path.isfile(file_name):
            # the provided file doesn't exist
            metadata_dic['error_msg'] = f'The file "{file_name}" does not exist.'
            return metadata_dic

        # open the given file
        file_obj = open(file_name, 'rb')

        file_format = None
        data_type = None        # can be : 'chunk' (Wav file), 'block' or 'sub_block' or 'sub_block_chunk' (WavPack file)
        chunk_data_size = 0     # Wav or WavPack file
        block_data_size = 0     # WavPack file
        sub_block_data_size = 0 # WavPack file

        while file_obj.read(1):
            # scan the file while the end of file is not reached and no error has occured
            file_obj.seek(-1, 1)   # move the file pointer one byte back to compensate the read(1) of the while instruction

            if file_format is None:
                # identification of the file format from the first 4 bytes of the file
                file_type_str = file_obj.read(4)
                file_obj.seek(-4, 1)  # rewind at the beginning of the file
                if file_type_str == b'wvpk':
                    file_format = 'wavpack'
                    data_type = 'block'
                    print(f'WavPack file {file_name}') if LOG_wav_decode else None
                elif file_type_str == b'RIFF':
                    file_format = 'wave'
                    data_type = 'chunk'
                    print(f'Wave file {file_name}') if LOG_wav_decode else None
                else:
                    metadata_dic['error_msg'] = f'Unsupported format in file {file_name}, Wave or WavPack format is expected'
                    print(f'Unsupported format in file {file_name}') if LOG_wav_decode else None
                    file_obj.close()
                    return metadata_dic

                metadata_dic['file_format'] = file_format

            if data_type == 'block':
                # start of a WavPack block

                # read the data of the block header
                file_obj.read(4)      # skip the ID "wvpk"
                block_data_size = int.from_bytes(file_obj.read(4), 'little')   # size of the entire block minus 8 bytes
                version = int.from_bytes(file_obj.read(2), 'little')           # 0x402 to 0x410 are valid for decode
                block_index_u8 = int.from_bytes(file_obj.read(1), 'little')    # upper 8 bits  of 40-bit block index
                total_samples_u8 = int.from_bytes(file_obj.read(1), 'little')  # upper 8 bits  of 40-bit total samples
                total_samples_l32 = int.from_bytes(file_obj.read(4), 'little') # lower 32 bits of 40-bit total samples
                block_index_l32 = int.from_bytes(file_obj.read(4), 'little')   # lower 32 bits of 40-bit block index
                nb_of_samples_in_block = int.from_bytes(file_obj.read(4), 'little') # number of samples in this block, 0=non-audio block
                flags  = int.from_bytes(file_obj.read(4), 'little')            # flags for id and decoding
                file_obj.read(4)      # skip the CRC for actual decoded data
                block_data_size -= 24 # entire block size -8 bytes -24 bytes read in the block header

                block_index = (block_index_u8 << 32) + block_index_l32
                nb_of_samples = (total_samples_u8 << 32) + total_samples_l32
                print(f"  block : version = 0x{version:03X}, size = {block_data_size+32}, data size = {block_data_size} bytes, first sample index = {block_index}, nb of samples in the block = {nb_of_samples_in_block}, total number of samples = {nb_of_samples}, flags = 0x{flags:08X}") if LOG_wav_decode else None

                # get metadata from flags of the first block
                if block_index == 0:
                    metadata_dic['nb_of_samples'] = nb_of_samples
                    metadata_dic['bits_per_sample'] = ((flags & 0b11) + 1) * 8

                    if ((flags >> 2) & 0b1) == 0:
                        metadata_dic['nb_of_channels'] = 2
                    else:
                        metadata_dic['nb_of_channels'] = 1

                    metadata_dic['sampling_rate'] = self.wavpack_sample_rates[(flags >> 23) & 0b1111]
                    metadata_dic['compression_code'] = (flags >> 3) & 0b1  # 0 = losslessaudio, 1 = hybrid mode
                    metadata_dic['audio_data_size'] = metadata_dic['nb_of_samples'] * metadata_dic['nb_of_channels'] * (metadata_dic['bits_per_sample'] // 8)

                    print(f"  block : nb of channels = {metadata_dic['nb_of_channels']}, bits per sample = {metadata_dic['bits_per_sample']}, sampling rate = {metadata_dic['sampling_rate']}, compression code = {metadata_dic['compression_code']}") if LOG_wav_decode else None

                if block_data_size > 0:
                    # the block contains data, a sub-block is going to follow in the file
                    data_type = 'sub_block'
                else:
                    print('  no data inside') if LOG_wav_decode else None

            if data_type == 'sub_block':
                # start of a WavPack metadata sub-block

                sub_block_id = int.from_bytes(file_obj.read(1), 'little')
                block_data_size -= 1
                sub_block_func_id = sub_block_id & 0x3f

                # read the size of the sub-block (in bytes)
                if sub_block_id & 0x80:
                    # it is a large block, its size is encoded on 3 bytes
                    sub_block_data_size = int.from_bytes(file_obj.read(3), 'little') * 2  # x2 to convert the size from words to bytes
                    block_data_size -= 3
                    large_block = True
                else:
                    sub_block_data_size = int.from_bytes(file_obj.read(1), 'little') * 2
                    block_data_size -= 1
                    large_block = False

                print(f'    sub-block : ID = 0x{sub_block_id:X}, function ID = 0x{sub_block_func_id:X}, large block = {large_block}, data size = {sub_block_data_size} bytes') if LOG_wav_decode else None

                if sub_block_func_id in (0x21, 0x22): # 0x21 = ID_RIFF_HEADER, 0x22 = ID_RIFF_TRAILER
                    # RIFF chunks are present in this sub-block
                    data_type = 'sub_block_chunk'
                    print('      RIFF chunks inside') if LOG_wav_decode else None

                if sub_block_data_size == 0:
                    print('      no data inside') if LOG_wav_decode else None

            if data_type in ('chunk', 'sub_block_chunk'):
                # start of a Wave chunk (in a Wav or WavPack file)

                chunk_id = file_obj.read(4).decode('utf-8', 'ignore')  # string of 4 characters
                chunk_data_size = int.from_bytes(file_obj.read(4), 'little')

                chunk_read_data_size = 0

                if chunk_data_size % 2:
                    # the chunk size has an odd number of bytes, a word padding byte is present after it
                    # increment the chunk size by 1 to cover this padding byte
                    chunk_data_size += 1

                if chunk_id == 'RIFF':
                    print(f'      chunk : [{chunk_id}], wave file size = {chunk_data_size + 8} bytes') if LOG_wav_decode else None
                else:
                    print(f'      chunk : [{chunk_id}], size = {chunk_data_size} bytes') if LOG_wav_decode else None

                if chunk_id == 'RIFF':
                    # RIFF chunk descriptor
                    if file_obj.read(4) == b'WAVE':  # RIFF type ID
                        # the RIFF type ID is WAVE, it is a valid .wav file
                        print('        RIFF type ID = "WAVE"') if LOG_wav_decode else None
                    else:
                        metadata_dic['error_msg'] = 'RIFF chunk has not the "WAVE" type ID, unsuported file format'
                        print('        RIFF chunk has not the "WAVE" type ID, unsuported file format') if LOG_wav_decode else None
                        file_obj.close()
                        return metadata_dic

                    chunk_data_size = 4  # in the RIFF chunk the data size value is the size of the file - 8 bytes
                                         # there are only 4 bytes of data in this chunk (the RIFF type ID)
                    chunk_read_data_size += 4

                elif chunk_id == 'fmt ':
                    # format chunk
                    metadata_dic['compression_code'] = int.from_bytes(file_obj.read(2), 'little')
                    metadata_dic['nb_of_channels'] = int.from_bytes(file_obj.read(2), 'little')
                    metadata_dic['sampling_rate'] = int.from_bytes(file_obj.read(4), 'little')
                    file_obj.read(4) # skip the bytes per second
                    file_obj.read(2) # skip the block align
                    metadata_dic['bits_per_sample'] = int.from_bytes(file_obj.read(2), 'little')
                    print(f"        compression code = {metadata_dic['compression_code']}, nb of channels = {metadata_dic['nb_of_channels']}, sampling rate = {metadata_dic['sampling_rate']}, bits per sample = {metadata_dic['bits_per_sample']}") if LOG_wav_decode else None

                    chunk_read_data_size += 16

                elif chunk_id == 'data':
                    # data chunk
                    metadata_dic['audio_data_size'] = chunk_data_size    # size in bytes of the sampled audio data
                    metadata_dic['nb_of_samples'] = int(chunk_data_size / (metadata_dic['nb_of_channels'] * metadata_dic['bits_per_sample'] // 8))
                    print(f"        nb of samples = {metadata_dic['nb_of_samples']}, audio data size = {metadata_dic['audio_data_size']}") if LOG_wav_decode else None
                    if data_type == 'chunk':
                        # get the buffer of raw sampled audio data in case of Wav file only
                        metadata_dic['sampled_data'] = file_obj.read(chunk_data_size)
                        chunk_read_data_size += chunk_data_size
                    else:  # data_type is 'sub_block_chunk'
                        # if WavPack file, there are no audio samples in the data chunk
                        chunk_data_size = 0

                else:
                    print("        none data recovered") if LOG_wav_decode else None

                # move the file pointer at the end of the chunk if it is not already there
                if chunk_data_size - chunk_read_data_size > 0:
                    file_obj.seek(chunk_data_size - chunk_read_data_size, 1)
                    print(f'        file pointer moved at the end of the chunk by {chunk_data_size - chunk_read_data_size} bytes') if LOG_wav_decode else None

                if data_type == 'sub_block_chunk':
                    # update the remaining size of data not read in the parents sub-block and block
                    block_data_size -= 8 + chunk_data_size  # 8 is the size of chunk ID and size fields at the start of the chunk
                    sub_block_data_size -= 8 + chunk_data_size

                    if sub_block_data_size <= 0:
                        # the end of the sub-block with RIFF chunks inside is reached
                        data_type = 'sub_block'

            if data_type == 'sub_block' and sub_block_data_size > 0:
                # sub-block with unread data inside
                # move the file pointer at the end of the sub-block
                file_obj.seek(sub_block_data_size, 1)
                print(f'      {sub_block_data_size} bytes skipped') if LOG_wav_decode else None  # noqa: E701
                block_data_size -= sub_block_data_size
                sub_block_data_size = 0

            if data_type == 'sub_block' and block_data_size <= 0:
                # block end is reached
                data_type = 'block'

            if data_type == 'block' and block_data_size > 0:
                # block with unread data inside
                # move the file pointer at the end of the block
                file_obj.seek(block_data_size, 1)
                print(f'  {block_data_size} bytes skipped') if LOG_wav_decode else None
                block_data_size = 0

        # close the given file
        file_obj.close()

        metadata_dic['audio_duration'] = 0
        if file_format is not None:
            if 'audio_data_size' not in metadata_dic.keys():
                # audio file without data chunk inside
                metadata_dic['error_msg'] = f'The file "{file_name}" has no audio samples inside.'
            else:
                # compute the duration of the audio samples in seconds (float with 2 decimals)
                metadata_dic['audio_duration'] = int(metadata_dic['audio_data_size'] * 1000 / (metadata_dic['sampling_rate'] * metadata_dic['nb_of_channels'] * metadata_dic['bits_per_sample'] / 8)) / 1000

        metadata_dic['bytes_per_sample'] = metadata_dic['bits_per_sample'] // 8

        if metadata_dic['compression_code'] == 1:  # WAVE_FORMAT_PCM
            if metadata_dic['bytes_per_sample'] == 1:
                metadata_dic['sample_data_type'] = 'uint8'
            elif metadata_dic['bytes_per_sample'] == 2:
                metadata_dic['sample_data_type'] = 'int16'
            elif metadata_dic['bytes_per_sample'] == 3:
                metadata_dic['sample_data_type'] = 'int24'
            elif metadata_dic['bytes_per_sample'] == 4:
                metadata_dic['sample_data_type'] = 'int32'
            else:
                metadata_dic['sample_data_type'] = None
                metadata_dic['error_msg'] = f"Not supported bytes number per sample {metadata_dic['bytes_per_sample']}"

        elif metadata_dic['compression_code'] == 3:  # WAVE_FORMAT_IEEE_FLOAT
            if metadata_dic['bytes_per_sample'] == 4:
                metadata_dic['sample_data_type'] = 'float32'
            elif metadata_dic['bytes_per_sample'] == 8:
                metadata_dic['sample_data_type'] = 'float64'
            else:
                metadata_dic['sample_data_type'] = None
                metadata_dic['error_msg'] = f"Not supported bytes number per sample {metadata_dic['bytes_per_sample']}"
        else:
            metadata_dic['sample_data_type'] = None
            metadata_dic['error_msg'] = f"Not supported compression code {metadata_dic['compression_code']}"

        metadata_dic['metadata_recovered'] = True

        return metadata_dic

    #-------------------------------------------------------------------------------------------------
    def wav_file_record(self, file_name=None, samples_bytes_buffer=None):
        # open a wav file for recording audio samples data of the audio_stream_loop function inside it
        # for the first call the file_name must be given, the samples buffer (in bytes format) is not mandatory
        # for the next calls, the file_name is not requested, the samples buffer (in bytes format) must be given
        # once there are no more data to write, wav_file_record_end must be called

        if len(self.samples_dic) == 0:
            return False

        if self.recording_file_name is None and file_name is not None:
            # first writting, create the file and its header

            header = b'RIFF'                       # ChunkID
            header += struct.pack('<I', 36 + 0)    # ChunkSize = 36 + SubChunk2Size. It will be updated at end of the recording
            header += b'WAVE'                      # Format
            header += b'fmt '                      # Subchunk1ID
            header += struct.pack('<I', 16)        # Subchunk1Size : 16 for PCM format
            if self.sample_data_type == 'float32':
                header += struct.pack('<H', 3)         # AudioFormat : 3 for WAVE_FORMAT_IEEE_FLOAT
            else:
                header += struct.pack('<H', 1)         # AudioFormat : 1 for PCM (i.e. linear quantization, no compression)
            header += struct.pack('<H', self.nb_of_channels)      # NumChannels : 1 = mono, 2 = stereo
            header += struct.pack('<I', self.sampling_frequency)  # SampleRate : 8000, 44100, etc...
            header += struct.pack('<I', self.sampling_frequency * self.nb_of_channels * self.bits_per_sample // 8)  # ByteRate = SampleRate * NumChannels * BitsPerSample / 8
            header += struct.pack('<H', self.nb_of_channels * self.bits_per_sample // 8)                            # BlockAlign = NumChannels * BitsPerSample / 8
            header += struct.pack('<H', self.bits_per_sample)     # BitsPerSample : 8, 16, etc...
            header += b'data'                                     # SubChunk2ID
            header += struct.pack('<I', 0)                        # SubChunk2Size = NumSamples * NumChannels * BitsPerSample / 8
                                                                  # number of bytes of the audio samples. It will be updated at end of the recording
            # write the header of the wav file
            self.recording_file = open(file_name, 'wb')
            self.recording_file.write(header)

            self.recording_file_name = file_name
            self.samples_recording_in_progress = True
            self.first_samples_emitted = False
            self.output_wav_file_data_size = 0

        if self.samples_recording_in_progress and samples_bytes_buffer is not None:
            # add bytes data at the end of the wav file
            self.recording_file.write(samples_bytes_buffer)

            self.output_wav_file_data_size += len(samples_bytes_buffer)

        return True

    #-------------------------------------------------------------------------------------------------
    def wav_file_record_end(self):

        if self.samples_recording_in_progress:

            self.samples_recording_in_progress = False

            # Update the header with the final data sizes
            self.recording_file.seek(4)
            self.recording_file.write(struct.pack('<I', 36 + self.output_wav_file_data_size))    # ChunkSize
            self.recording_file.seek(40)
            self.recording_file.write(struct.pack('<I', self.output_wav_file_data_size))         # Subchunk2Size
            self.recording_file.close()

##            self.wav_file_header_print(self.recording_file_name)

            logs_display_fct(f'\nFichier audio généré : {self.recording_file_name}\n')

            self.recording_file_name = None

    #------------------------------------------------------------------------
    def wav_file_header_print(self, file_path):

        with open(file_path, 'rb') as f:
            header = f.read(44)
            riff = header[0:4].decode()
            chunk_size = int.from_bytes(header[4:8], 'little')
            wave = header[8:12].decode()
            fmt = header[12:16].decode()
            subchunk1_size = int.from_bytes(header[16:20], 'little')
            audio_format = int.from_bytes(header[20:22], 'little')
            num_channels = int.from_bytes(header[22:24], 'little')
            sample_rate = int.from_bytes(header[24:28], 'little')
            byte_rate = int.from_bytes(header[28:32], 'little')
            block_align = int.from_bytes(header[32:34], 'little')
            bits_per_sample = int.from_bytes(header[34:36], 'little')
            data_str = header[36:40].decode()
            subchunk2_size = int.from_bytes(header[40:44], 'little')

            print(f"RIFF:           {riff}")
            print(f"ChunkSize:      {chunk_size}")
            print(f"WAVE:           {wave}")
            print(f"fmt :           {fmt}")
            print(f"Subchunk1Size:  {subchunk1_size}")
            print(f"AudioFormat:    {audio_format}")
            print(f"NumChannels:    {num_channels}")
            print(f"SampleRate:     {sample_rate}")
            print(f"ByteRate:       {byte_rate}")
            print(f"BlockAlign:     {block_align}")
            print(f"BitsPerSample:  {bits_per_sample}")
            print(f"data:           {data_str}")
            print(f"Subchunk2Size:  {subchunk2_size}")
            print(f"Duration (calc): {subchunk2_size / byte_rate:.2f} seconds")

    #------------------------------------------------------------------------
    def audio_samples_gen(self, midi_note_first, midi_note_last):
        # load in memory audio samples generated for the MIDI notes of the given range

        logs_display_fct('\nGénération d\'échantillons sonores...\n')

        # stop any playback in progress
        self.midi_note_stop(-1)

        self.loaded_samples_dir = None
        self.samples_loading_in_progress = True

        self.samples_dic.clear()
        self.sampling_frequency = 48000  # Hz
        self.sample_data_type = 'int16'  # 16 bits signed integer
        self.bytes_per_sample = 2        # 16 bits = 2 bytes
        self.bits_per_sample = 16        # 16 bits
        self.nb_of_channels = 1          # mono
        self.sample_data_max = int(pow(2, self.bits_per_sample) / 2 - 1)
        self.is_int_data = True

        fs = self.sampling_frequency
        notes_nb = midi_note_last - midi_note_first + 1

        for midi_note in range(midi_note_first, midi_note_last + 1):

            progress_nb = round((midi_note - midi_note_first + 1) / notes_nb * 50)
            logs_display_fct(f"{'█' * progress_nb}{'░' * (50 - progress_nb)}", True)

            freq = midi_nb_to_freq(midi_note)  # frequency of the audio signal

            note_duration = (midi_note - 36) / (108 - 36) * (2 - 5) + 5  # duration of the audio signal from 5 to 2 seconds for MIDI note from 36 to 108

            # compute the total number of samples for playing the current MIDI note
            samples_nb = int(fs * note_duration)

            # create the buffer to store the audio samples of the current MIDI note
            samples_values_lst = self.samples_dic[midi_note] = [0] * samples_nb

            # generates the audio samples
            factor = 2 * math.pi * freq / fs
            factor2 = -10 / samples_nb
            for n in range(samples_nb):
                samples_values_lst[n] = math.sin(n * factor) * 10000 * math.exp(n * factor2)

                if not self.samples_loading_in_progress:
                    # the generation has to be interrupted
                    self.samples_dic.clear()
                    return True

            print(f'WAV_PLAYER gen : MIDI note {midi_note} frequency {freq:.3f}') if LOG_wav_player else None

        logs_display_fct(f"{notes_nb} notes générées du {midi_nb_to_note(midi_note_first, 'fra')} au {midi_nb_to_note(midi_note_last, 'fra')}\n", True)

        # create an audio output stream with raw data to be ready to play a note as soon as requested by midi_note_play()
        try:
            self.stream = sounddevice.RawOutputStream(samplerate=self.sampling_frequency,
                                                      channels=self.nb_of_channels,
                                                      dtype=self.sample_data_type,
                                                      blocksize=self.samples_nb_per_loop,
                                                      latency=audio_latency,
                                                      callback=self.audio_stream_loop)
            self.stream.start()

            print(f'WAV_PLAYER gen : audio stream started, latency {round(self.stream.latency * 1000)} milliseconds') if LOG_wav_player else None

        except (sounddevice.PortAudioError, OSError) as err:
            # an error has occurred while opening the PortAudio stream
            logs_display_fct(f"PROBLEME : échec à l'ouverture du flux audio : {format(err)}\n")
            self.stream = None

        self.samples_loading_in_progress = False

        return self.stream is not None

    #------------------------------------------------------------------------
    def audio_samples_load(self, folder_name):
        # load in memory the .wav audio samples present in the given folder
        # the files names must contain the name of the note of the samples, for example 056-G3#.wav (english or french notation)

        if not os.path.isdir(folder_name):
            # the given folder doesn't exist
            logs_display_fct(f'PROBLEME : le répertoire "{folder_name}" n\'existe pas')
            return False

        # count the number of .wav files present in the given folder
        wav_files_nb = 0
        for file_name in os.listdir(folder_name):
            if file_name.endswith(".wav"):
                wav_files_nb += 1
        if wav_files_nb == 0:
            logs_display_fct(f'PROBLEME : le répertoire "{folder_name}" ne contient aucun fichier .wav\n')
            return False

        logs_display_fct(f'\nChargement des échantillons sonores du répertoire "{folder_name}"...\n')

        self.samples_loading_in_progress = True

        # stop any playback in progress
        self.midi_note_stop(-1)

        # initialize the data
        self.sample_data_type = None
        self.samples_dic.clear()
        midi_note_min = 999
        midi_note_max = 0
        current_wav_file_nb = 0
        loading_errors_msg = ''

        for file_name in os.listdir(folder_name):
            if not self.samples_loading_in_progress:
                # the loading has to be interrupted
                break
            if file_name.endswith(".wav"):
                # the current file of the directory is a .wav file
                current_wav_file_nb += 1

                progress_nb = round(current_wav_file_nb/wav_files_nb * 50)
                logs_display_fct(f"{'█' * progress_nb}{'░' * (50 - progress_nb)}", True)

                # get the MIDI note of the current file from its name
                midi_note = note_to_midi_nb(file_name)

                if midi_note is None:
                    # no note name identified in the file name, check if there is a number from 36 to 108 (a MIDI note hopefully)
                    rs = re.search(r"(3[6-9]|[4-9][0-9]|10[0-8])", file_name)
                    if rs is not None and rs.groups()[0].isdigit():
                        midi_note = int(rs.groups()[0])

                if midi_note is not None:
                    print(f'WAV_PLAYER load : MIDI {midi_note} for {file_name}') if LOG_wav_player else None

                    # recover the data of the .wav file (metadata and audio samples)
                    data_dic = self.wav_file_read(folder_name + os.path.sep + file_name)
                    if data_dic['metadata_recovered'] and data_dic['sample_data_type'] is not None:
                        if self.sample_data_type is None:
                            self.nb_of_channels = data_dic['nb_of_channels']       # 1 (mono) or 2 (stereo) channels
                            self.sampling_frequency = data_dic['sampling_rate']    # in Hz
                            self.bits_per_sample = data_dic['bits_per_sample']     # 8, 16, 24 , 32 or 64 bits
                            self.bytes_per_sample = data_dic['bytes_per_sample']   # 1,  2,  3 ,  4 or  8 bytes
                            self.sample_data_type = data_dic['sample_data_type']   # 'uint8', 'int16', 'int24', 'int32', 'float32', 'float64'
                            self.time_per_loop = self.samples_nb_per_loop / self.sampling_frequency

                            if 'int' in self.sample_data_type:
                                self.sample_data_max = int(pow(2, self.bits_per_sample) / 2 - 1)
                                self.is_int_data = True
                            elif self.sample_data_type == 'float32':
                                self.struct_format = '<f'  # little endian (<) with 4 (f) bytes signed float
                                self.is_int_data = False
                            elif self.sample_data_type == 'float64':
                                self.struct_format = '<d'  # little endian (<) with 8 (f) bytes signed float
                                self.is_int_data = False
                            print(f"WAV_PLAYER load : {file_name} has sampling frequency {self.sampling_frequency}Hz, nb of channels {self.nb_of_channels}, data type {self.sample_data_type}, loop duration {round(self.time_per_loop*1000)}ms") if LOG_wav_player else None

                        file_is_ok = True
                        if data_dic['sample_data_type'] == 'float64':
                            loading_errors_msg += f"PROBLEME : le fichier {file_name} utilise une taille d'échantillons {data_dic['sample_data_type']} non supportée, il n'a pas été chargé\n"
                            file_is_ok = False
                        if self.sample_data_type != data_dic['sample_data_type']:
                            loading_errors_msg += f"PROBLEME : le fichier {file_name} utilise une taille d'échantillons {data_dic['sample_data_type']} différente de celle du premier fichier {self.sample_data_type}, il n'a pas été chargé\n"
                            file_is_ok = False
                        if self.sampling_frequency != data_dic['sampling_rate']:
                            loading_errors_msg += f"PROBLEME : le fichier {file_name} utilise une fréquence d'échantillonnage {data_dic['sampling_rate']}Hz différente de celle du premier fichier {self.sampling_frequency}Hz, il n'a pas été chargé\n"
                            file_is_ok = False
                        if self.nb_of_channels != data_dic['nb_of_channels']:
                            loading_errors_msg += f"PROBLEME : le fichier {file_name} utilise un nombre de canaux {data_dic['nb_of_channels']} différent de celui du premier fichier {self.nb_of_channels}, il n'a pas été chargé\n"
                            file_is_ok = False
                        if midi_note in self.samples_dic.keys():
                            loading_errors_msg += f"PROBLEME : des échantillons sonores ont déjà été chargés depuis un autre fichier pour la note {midi_nb_to_note(midi_note, 'fra')} / {midi_nb_to_note(midi_note)}, le fichier {file_name} n'a pas été chargé\n"
                            file_is_ok = False

                        if file_is_ok:
                            # convert the samples of the current file from byte to integer/float format and store them in memory for the MIDI note
                            midi_note_min = min(midi_note_min, midi_note)
                            midi_note_max = max(midi_note_max, midi_note)

                            samples_bytes_lst = data_dic['sampled_data']
                            samples_values_lst = self.samples_dic[midi_note] = [0] * data_dic['nb_of_samples'] * self.nb_of_channels
                            i = 0  # index in source bytes buffer of the samples
                            j = 0  # index in destination integer/float buffer
                            while j < data_dic['nb_of_samples'] * self.nb_of_channels:
                                if self.is_int_data:
                                    if self.sample_data_type[0] == 'u':
                                        samples_values_lst[j] = int.from_bytes(samples_bytes_lst[i:i+self.bytes_per_sample], byteorder='little', signed=False) - 128
                                    else:
                                        samples_values_lst[j] = int.from_bytes(samples_bytes_lst[i:i+self.bytes_per_sample], byteorder='little', signed=True)
                                else:  # float data
                                    samples_values_lst[j] = struct.unpack_from(self.struct_format, samples_bytes_lst, i)[0]
##                                samples_values_lst[j] = struct.unpack_from(self.struct_format, samples_bytes_lst, i)[0]
                                i += self.bytes_per_sample
                                j += 1
                                if not self.samples_loading_in_progress:
                                    # the loading has to be interrupted (this loop is the most CPU consuming part of this function)
                                    break
                    else:
                        loading_errors_msg += f"PROBLEME : échec de chargement du contenu du fichier {file_name} : {data_dic['error_msg']}\n"
                else:
                    loading_errors_msg += f"PROBLEME : note non identifiable à partir du nom du fichier {file_name} (problème de nommage ?)\n"

        if not self.samples_loading_in_progress:
            # the loading has to be interrupted
            self.samples_dic.clear()
            return True

        # display the error messages which may have happen during the samples loading
        if len(loading_errors_msg) > 0:
            logs_display_fct(loading_errors_msg, True)

        if len(self.samples_dic) > 0:
            # audio samples have been loaded

            if len(self.samples_dic) == 1:
                logs_display_fct(f"{len(self.samples_dic)} note chargée {midi_nb_to_note(midi_note_min, 'fra')}\n", True)
            else:
                logs_display_fct(f"{len(self.samples_dic)} notes chargées du {midi_nb_to_note(midi_note_min, 'fra')} au {midi_nb_to_note(midi_note_max, 'fra')}\n", True)

            # check if there are MIDI notes without audio samples between the min and max loaded MIDI notes
            missing_notes_lst = []
            for midi_note in range(midi_note_min, midi_note_max + 1):
                if midi_note not in self.samples_dic.keys():
                    missing_notes_lst.append(f"{midi_nb_to_note(midi_note, 'fra')}")

            if len(missing_notes_lst) == 1:
                logs_display_fct(f"Pas d'échantillons sonores trouvés pour la note {missing_notes_lst[0]}\n")
            elif len(missing_notes_lst) > 1:
                logs_display_fct(f"Pas d'échantillons sonotres trouvés pour les notes {' '.join(missing_notes_lst)}\n")

            # create an audio output stream with raw data to be ready to play a note as soon as requested by midi_note_play()
            try:
                self.stream = sounddevice.RawOutputStream(samplerate=self.sampling_frequency,
                                                          channels=self.nb_of_channels,
                                                          dtype=self.sample_data_type,
                                                          blocksize=self.samples_nb_per_loop,
                                                          latency=audio_latency,
                                                          callback=self.audio_stream_loop)
                self.stream.start()

                print(f'WAV_PLAYER load : audio stream started, latency {round(self.stream.latency * 1000)} milliseconds') if LOG_wav_player else None

            except (sounddevice.PortAudioError, OSError) as err:
                # an error has occurred while opening the PortAudio stream
                logs_display_fct(f"PROBLEME : échec à l'ouverture du flux audio : {format(err)}\n")
                self.stream = None
        else:
            logs_display_fct("PROBLEME : aucun échantillon audio n'a pu être chargé\n")
            self.stream = None

        self.samples_loading_in_progress = False

        if self.stream is not None:
            self.loaded_samples_dir = folder_name
        else:
            self.loaded_samples_dir = None

        return self.stream is not None

    #------------------------------------------------------------------------
    def audio_samples_load_abort(self):
        # request to abort the samples loading in progress if any

        self.samples_loading_in_progress = False

    #------------------------------------------------------------------------
    def audio_volume_set(self, audio_volume_factor):
        # set the audio volume to apply compared to the MIDI file velocity, a float value, 1.0 means not change

        self.audio_volume_factor = audio_volume_factor

    #------------------------------------------------------------------------
    def midi_note_play(self, midi_note, midi_velocity=default_midi_velocity):
        # start the playback of the audio samples of the given MIDI note, at the given MIDI velocity which is a volume level (0 to 127, 0 for no sound, 127 for max volume)
        # return True or False whether the note playback has been started

        if self.samples_loading_in_progress:
            return

        if self.stream is None:
            print("WAV_PLAYER stream is not existing") if LOG_wav_player else None
            return False

        if midi_note not in self.samples_dic.keys():
            print(f'WAV_PLAYER cannot play the MIDI note {midi_note} : there are no audio samples for it') if LOG_wav_player else None
            return False

        if midi_velocity > 127:
            midi_velocity = 127

        while self.streams_dic_in_use:
            # wait until the dictionary streams_dic is unused
            time.sleep(0.01)

        # set the data of the stream which is created for the given MIDI note, with playing position at 0
        #                              [0: playing position, 1: number of samples, 2: audio samples buffer, 3: audio volume factor]
        self.streams_dic[midi_note] = [0, len(self.samples_dic[midi_note]), self.samples_dic[midi_note], midi_velocity / 127]

        print(f"WAV_PLAYER >> Starting playback of MIDI note {midi_note} {midi_nb_to_note(midi_note)} with velocity {midi_velocity}, {len(self.streams_dic)} streams active") if LOG_wav_player else None

        return True

    #------------------------------------------------------------------------
    def midi_note_stop(self, midi_note):
        # stop the playback of the samples of the given MIDI note, or of all MIDI notes if midi_note = -1

        while self.streams_dic_in_use:
            # wait until the dictionary streams_dic is unused
            time.sleep(0.01)

        if midi_note == -1:
            # stop all MIDI notes
            self.streams_dic.clear()
            if self.stream is not None and self.stream.active:
                self.stream.abort()
                print("WAV_PLAYER all notes stopped") if LOG_wav_player else None
        elif midi_note in self.streams_dic.keys():
            # stop the given MIDI note
            self.streams_dic.pop(midi_note)
            print(f"WAV_PLAYER stopping MIDI note {midi_note}, {len(self.streams_dic)} streams still active") if LOG_wav_player else None
        else:
            print(f'WAV_PLAYER cannot stop the MIDI note {midi_note} : there is no started stream for it') if LOG_wav_player else None

    #------------------------------------------------------------------------
    def audio_stream_loop(self, outdata, frames, time, status):
        # callback function called by the PortAudio stream to get the next audio buffer to play

        # list containing the MIDI notes which the playback will be completed in this loop
        midi_notes_completed_lst = []

        # buffer which is mixing the active streams samples before to be converted in Bytes and given to PortAudio
        playback_buffer = [0.0] * self.samples_nb_per_loop * self.nb_of_channels

        self.streams_dic_in_use = True
        for midi_note, player_stream in self.streams_dic.items():
            # player_stream content : [0:playing position, 1:buffer length, 2:buffer of audio samples, 3:audio volume factor]
            next_playback_pos = player_stream[0] + self.samples_nb_per_loop * self.nb_of_channels
            i = player_stream[0]  # index in the source samples data
            j = 0                 # index in the target playback buffer
            audio_samples_buffer = player_stream[2]
            audio_volume = player_stream[3] * self.audio_volume_factor
            while i < min(next_playback_pos, player_stream[1]):
                playback_buffer[j] += audio_samples_buffer[i] * audio_volume   # apply the audio volume factor to the sample
                i += 1
                j += 1
            player_stream[0] = i
            if i == player_stream[1]:
                # end of samples buffer reached for the current MIDI note
                midi_notes_completed_lst.append(midi_note)
        self.streams_dic_in_use = False

        # convert the integers/float buffer into a bytes buffer
        i = 0  # index in the source samples buffer
        j = 0  # index in the target bytes buffer
        while i < self.samples_nb_per_loop * self.nb_of_channels:
            # check the range of the sample value in case of an integer format
            if self.is_int_data:
                # the data are integer value, with maximum values to not exceed
                if playback_buffer[i] > self.sample_data_max:
                    playback_buffer[i] = self.sample_data_max
                elif playback_buffer[i] < -self.sample_data_max:
                    playback_buffer[i] = -self.sample_data_max
                else:
                    playback_buffer[i] = int(playback_buffer[i])  # applying the audio volume has set float values

                if self.sample_data_type[0] == 'u':
                    outdata[j:j+self.bytes_per_sample] = (playback_buffer[i] + 128).to_bytes(self.bytes_per_sample, byteorder='little', signed=False)
                else:
                    outdata[j:j+self.bytes_per_sample] = playback_buffer[i].to_bytes(self.bytes_per_sample, byteorder='little', signed=True)
            else:
                struct.pack_into(self.struct_format, outdata, j, playback_buffer[i])

##            if self.is_int_data:
##                if self.sample_data_type[0] == 'u':
##                    samples_values_lst[j] = int.from_bytes(samples_bytes_lst[i:i+self.bytes_per_sample], byteorder='little', signed=False) - 128
##                else:
##                    samples_values_lst[j] = int.from_bytes(samples_bytes_lst[i:i+self.bytes_per_sample], byteorder='little', signed=True)
##            else:  # float data
##                samples_values_lst[j] = struct.unpack_from(self.struct_format, samples_bytes_lst, i)[0]

            # convert the float/integer value into bytes inside the PortAudio buffer
##            struct.pack_into(self.struct_format, outdata, j, playback_buffer[i])
            i += 1
            j += self.bytes_per_sample

        self.streams_dic_in_use = True
        for midi_note in midi_notes_completed_lst:
            # remove from the streams dictionary the MIDI notes which the playback is completed
            self.streams_dic.pop(midi_note)
            print(f"WAV_PLAYER << Ended playback of MIDI note {midi_note}, {len(self.streams_dic)} streams still active") if LOG_wav_player else None
        self.streams_dic_in_use = False

        if len(self.streams_dic) > 0:
            self.first_samples_emitted = True

        if self.samples_recording_in_progress and self.first_samples_emitted:
            # audio samples have to be recorded in an audio file, and audio samples are emitted since the output file has been opened
            self.wav_file_record(None, outdata)


#-------------------------------------------------------------------------------------------------
class C_AUTO_PLAYER:
    # class to do operations about a carillon auto player

    #------------------------------------------------------------------------
    def get_levers_to_play(self, autoplayer_levers_to_midi_dic,  midi_notes_to_play_lst):
        # define which lever number has to be activated to play each of the given MIDI notes
        # according to the given autoplayer levers definition (lever number to one MIDI note)

        # build the dictionary giving the MIDI note to levers number and other information
        autoplayer_midi_to_levers_dic = {}
        for lever_nb, midi_note in autoplayer_levers_to_midi_dic.items():
            if midi_note is not None:
                if midi_note not in autoplayer_midi_to_levers_dic.keys():
                    autoplayer_midi_to_levers_dic[midi_note] = {"levers_lst":[], "levers_nb":0, "last_lever_idx":-1}

                autoplayer_midi_to_levers_dic[midi_note]["levers_lst"].append(lever_nb)
                autoplayer_midi_to_levers_dic[midi_note]["levers_nb"] += 1

        if len(autoplayer_midi_to_levers_dic) == 0:
            # there are no levers in the autoplayer
            return []

        levers_nb_to_play_lst = []

        for playback_step_nb in range(len(midi_notes_to_play_lst)):

            levers_nb_to_play_lst.append([])
            curr_levers_to_play_lst = levers_nb_to_play_lst[-1]

            for midi_note, midi_veloc in midi_notes_to_play_lst[playback_step_nb]['midi_lst']:

                if midi_note not in autoplayer_midi_to_levers_dic.keys() or autoplayer_midi_to_levers_dic[midi_note]["levers_nb"] == 0:
                    curr_levers_to_play_lst.append(None)    # there is no lever to play this MIDI note
                else:
                    # if several levers are playing the MIDI note, use the next one compared to the last one used
                    lever_dic = autoplayer_midi_to_levers_dic[midi_note]
                    lever_idx = lever_dic["last_lever_idx"] + 1
                    if lever_idx == lever_dic["levers_nb"]:
                        lever_idx = 0
                    lever_nb = lever_dic["levers_lst"][lever_idx]
                    curr_levers_to_play_lst.append(lever_nb)

                    lever_dic["last_lever_idx"] = lever_idx

        return levers_nb_to_play_lst

    #------------------------------------------------------------------------
    def prog_file_generate(self, carillon_name, prog_file_name, midi_file_name, midi_notes_to_play_lst, levers_nb_to_play_lst, autoplayer_marks_nb, autoplayer_rev_time, playback_speed_factor):
        # generate a programming file for the autoplayer, from the given MIDI notes and levers nb to play lists

        midi_file_duration = midi_notes_to_play_lst[-1]["time"] / playback_speed_factor

        autoplayer_time_per_pos = autoplayer_rev_time / autoplayer_marks_nb

        prog_file = open(prog_file_name, 'w', encoding='utf_8_sig')

        prog_file.write(f'{carillon_name}\n')
        prog_file.write(f'Fichier de programmation du jeu automatique, généré le {datetime.datetime.now().strftime("%d-%m-%Y")} à {datetime.datetime.now().strftime("%Hh%M")}\n')
        prog_file.write( '\n')
        prog_file.write(f'   fichier MIDI : {os.path.basename(midi_file_name)}\n')
        prog_file.write(f'          durée : {round(midi_file_duration, 1)} secondes\n')
        prog_file.write(f' cadran à noter : {autoplayer_marks_nb} repères par tour, {autoplayer_rev_time} secondes par tour --> {round(autoplayer_time_per_pos * 1000)} millisecondes par repère\n')
        prog_file.write( '\n')
        prog_file.write( ' Nro  | Temps sec | + msec | + rep. | Numéro leviers      | Notes                   \n')
        prog_file.write( '------|-----------|--------|--------|---------------------|-------------------------\n')

        lever_last_time_used_dic = {}

        for playback_step_nb in range(len(midi_notes_to_play_lst)):

            midi_notes_dic = midi_notes_to_play_lst[playback_step_nb]
            # dictionary with keys : 'dtime' : delta playback time, 'time' : absolute playback time, 'midi_lst' : list of tuples (midi note, midi velocity)

            levers_nb_lst = levers_nb_to_play_lst[playback_step_nb]
            # list of levers nb to play

            playback_time = midi_notes_dic['time'] / playback_speed_factor
            playback_dtime = midi_notes_dic['dtime'] / playback_speed_factor

            markers_increment = round(playback_dtime / autoplayer_time_per_pos)

            # prepare the string with the list of the MIDI notes to play
            midi_notes_lst = []
            for midi_note, midi_veloc in midi_notes_dic['midi_lst']:
                midi_notes_lst.append(midi_note)
            notes_names_to_play_str = ''
            for midi_note in sorted(midi_notes_lst):
                notes_names_to_play_str += f" {midi_nb_to_note(midi_note, 'fra'):5}"

            # prepare the string with list of the lever numbers to activate
            levers_nb_to_play_str = ''
            levers_time_warning_lst = []
            for lever_nb in sorted(levers_nb_lst):
                if lever_nb is None:
                    levers_nb_to_play_str += ' XXX'  # there is no lever to play this MIDI note
                else:
                    levers_nb_to_play_str += f' {lever_nb:3}'

                    if lever_nb in lever_last_time_used_dic.keys():
                        if playback_time - lever_last_time_used_dic[lever_nb] < lever_time_constant:
                            levers_time_warning_lst.append(lever_nb)
                    lever_last_time_used_dic[lever_nb] = playback_time

            disp_text =  f'{playback_step_nb + 1:5} | {playback_time:9.3f} | {round(playback_dtime*1000):6} | {round(markers_increment):6} |'
            disp_text += f'{levers_nb_to_play_str:20} |'
            disp_text += f'{notes_names_to_play_str:20}'

            if len(levers_time_warning_lst) == 1:
                disp_text += f'/!\\ Répétition trop rapide du levier {levers_time_warning_lst[0]}'
            elif len(levers_time_warning_lst) > 1:
                warning_msg = ' '.join(levers_time_warning_lst)
                disp_text += f'/!\\ Répétition trop rapide des leviers {warning_msg}'

            prog_file.write(disp_text + '\n')

        prog_file.close()


#-------------------------------------------------------------------------------------------------
class C_MIDI_FILE:
    # class to recover from a MIDI file the sequences of notes to play

    #------------------------------------------------------------------------
    def get_notes_to_play(self, midi_file_name):
        # get all notes to play from the given MIDI file
        # the notes to play at the same time are in a list, each item is a dictionary with the keys 'dtime', 'time', 'midi_lst'

        midi_notes_to_play_lst = []

        # MIDI tempo, value in microseconds per beat (one beat is a quarter note -> "noire" in French)
        # assume a default 120 BPM tempo (beats per minute) until it is overridden by a set_tempo meta message
        # 1 minute = 60 seconds / 120 = 0.5 sec = 500 000 µs
        midi_tempo = 500000

        # open the given MIDI file and recover the messages of all tracks merged together
        midi_file = mido.MidiFile(midi_file_name)
        messages_lst = mido.merge_tracks(midi_file.tracks)
        messages_nb = len(messages_lst)

        msg_idx = 0
        playback_time = 0  # in seconds
        last_playback_time = 0

        while msg_idx < messages_nb:
            # parse all the messages of the merged tracks of the MIDI file

            # recover the attributes of the current message
            msg = messages_lst[msg_idx]
            print(f'    {messages_lst[msg_idx].dict()}') if LOG_midi_messages else None

            if msg.type == 'set_tempo':
                # set_tempo meta message, defining / changing the tempo value of the track (in µs / beat)
                # tempo in number of quarter notes per minute is : 60 / msg.tempo * 1000000
                midi_tempo = msg.tempo

            elif msg.type == 'time_signature':
                # time_signature meta message, defining / changing the time signature of the track
                # it is msg.dict()['numerator'] / msg.dict()['denominator']
                pass

            elif msg.type.startswith('note') or msg.type == 'end_of_track':
                # note_on or note_off message or end of track (to recover its time for the playback position)

                # set the new playback position time from the time attribute of the message (in ticks, it is the delta time from the previous message)
                playback_time += mido.tick2second(msg.time, midi_file.ticks_per_beat, midi_tempo)

                if (msg.type == 'note_on' and msg.dict()['velocity'] > 0):
                    # note_on message with a not null velocity
                    # note_on with velocity = 0 means note_off
                    # there is no action to do on note_off message (the sound of a bell cannot be stopped)

                    midi_notes_to_play_lst.append({'dtime': playback_time - last_playback_time, 'time':playback_time, 'midi_lst':[]})
                    last_playback_time = playback_time
                    curr_notes_to_play_dic = midi_notes_to_play_lst[-1]
                    added_midi_notes_lst = []

                    # recover the notes to play and their velocity from the current MIDI message and the next messages having the same timing
                    curr_notes_to_play_dic['midi_lst'].append((msg.dict()['note'], msg.dict()['velocity']))
                    added_midi_notes_lst.append(msg.dict()['note'])

                    while msg_idx < messages_nb - 1 and messages_lst[msg_idx + 1].time == 0:
                        msg_idx += 1
                        msg = messages_lst[msg_idx]
                        print(f'    {messages_lst[msg_idx].dict()}') if LOG_midi_messages else None
                        if msg.type == 'note_on' and msg.dict()['velocity'] > 0 and msg.dict()['note'] not in added_midi_notes_lst:
                            curr_notes_to_play_dic['midi_lst'].append((msg.dict()['note'], msg.dict()['velocity']))
                            added_midi_notes_lst.append(msg.dict()['note'])

            msg_idx += 1

        if len(midi_notes_to_play_lst) > 0:
            logs_display_fct(f'\nFichier "{midi_file_name}" chargé. Durée {round(midi_notes_to_play_lst[-1]["time"], 1)} secondes\n')
        else:
            logs_display_fct('\nPas de notes à jouer trouvées dans le fichier "{midi_file_name}"\n')

        return midi_notes_to_play_lst


#-----------------------------------------------------------------------------------------------------
# class to manage the application (GUI and behaviors triggered by the GUI)
class C_APP():

    # flags permitting to control the background thread of the application
    app_is_running = False
    midi_file_playback_in_progress = False
    keyboard_test_in_progress = False
    autoplayer_test_in_progress = False
    audio_samples_load_in_progress = False
    playback_scale_moving = False

    recording_file_name = None

    carillon_def_file_name = None
    carillon_name = ''
    manual_keys_dic = {}      # dictionary with key : MIDI note of one key of the manual
                              #               value : MIDI note controlled by this key
    pedal_keys_dic = {}       # dictionary with key : MIDI note of one key of the pedal
                              #               value : MIDI note controlled by this key
    autoplayer_levers_to_midi_dic = {}  # dictionary with key : lever number of one lever of the autoplayer
                                        #               value : MIDI note controlled by this lever
    autoplayer_marks_nb = 0
    autoplayer_rev_time = 0

    midi_notes_to_play_lst = []
    levers_nb_to_play_lst = []

    playback_speed_factor = 1.0

    midi_port = None

    #-------------------------------------------------------------------------------------------------
    def wnd_main_build(self):
        # build the main window of the application with all his GUI widgets

        #--- create the main window using Tkinter library
        self.wnd_main = tk.Tk(className='Midillonn')
        self.wnd_main.title(APP_NAME)
        self.wnd_main.geometry('1350x600')
        self.wnd_main.protocol("WM_DELETE_WINDOW", self.wnd_main_quit) # callback to save the data of the application before to close the main window

        # assign an icon to the window
        photo = tk.PhotoImage(file = os.path.dirname(__file__) + os.path.sep + 'Midillon.png')
        self.wnd_main.iconphoto(False, photo)


        #---------- FRAME 1 -------------
        # horizontal frame with a label for presenting the application and an ABOUT button
        frame1 = ttk.Frame(self.wnd_main)
        frame1.pack(side=tk.TOP, fill=tk.X)

        tk.Label(frame1, text="Carillon MIDI permettant de jouer un carillon virtuellement depuis un clavier MIDI ou un fichier MIDI, et de générer un fichier de programmation de jeu automatique de carillon à partir d'un fichier MIDI.", fg="black").pack(side=tk.LEFT, expand=True)

        # button for opening an about dialog box
        self.about_btn = tk.Button(frame1, text = " ? ", fg="black", width=3, command=self.btn_about_app)
        self.about_btn.pack(side=tk.RIGHT, padx=(5,5), pady=2)
        self.about_btn.config(font=(self.about_btn["font"], 9, "bold"))


        #---------- FRAME 2 -------------
        # horizontal frame with widgets for the MIDI file selection
        frame2 = ttk.Frame(self.wnd_main)
        frame2.pack(side=tk.TOP, fill=tk.X)

        tk.Label(frame2, text="Fichier MIDI", fg="black", anchor=tk.E, width=30).pack(side=tk.LEFT)

        # combobox list showing the list of last opened MIDI files
        self.midi_files_cmb = ttk.Combobox(frame2, state="readonly")
        self.midi_files_cmb.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5,0))
        self.midi_files_cmb.bind('<Button-1>', lambda event, widget=self.midi_files_cmb: self.cmb_on_click(event, widget))
        self.midi_files_cmb.bind('<<ComboboxSelected>>', lambda event, widget=self.midi_files_cmb: self.cmb_on_selected(event, widget))

        # button for opening the file selection dialogbox
        self.midi_file_sel_btn = tk.Button(frame2, text = "...", fg="black", width=3, command=lambda widget=self.midi_files_cmb: self.btn_file_select(widget))
        self.midi_file_sel_btn.pack(side=tk.RIGHT, padx=(5,5), pady=2)

        #---------- FRAME 3 -------------
        # horizontal frame with widgets for the carillon definition file selection
        frame3 = ttk.Frame(self.wnd_main)
        frame3.pack(side=tk.TOP, fill=tk.X)

        tk.Label(frame3, text="Fichier de définition de carillon", fg="black", anchor=tk.E, width=30).pack(side=tk.LEFT)

        # combobox showing the list of last opened definition files
        self.carillon_def_files_cmb = ttk.Combobox(frame3, state="readonly")
        self.carillon_def_files_cmb.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5,0))
        self.carillon_def_files_cmb.bind('<Button-1>', lambda event, widget=self.carillon_def_files_cmb: self.cmb_on_click(event, widget))
        self.carillon_def_files_cmb.bind('<<ComboboxSelected>>', lambda event, widget=self.carillon_def_files_cmb: self.cmb_on_selected(event, widget))

        # button for opening the file selection dialogbox
        self.carillon_def_file_sel_btn = tk.Button(frame3, text = "...", fg="black", width=3, command=lambda widget=self.carillon_def_files_cmb: self.btn_file_select(widget))
        self.carillon_def_file_sel_btn.pack(side=tk.RIGHT, padx=(5,5), pady=2)

        #---------- FRAME 4 -------------
        # horizontal frame with widgets for the audio samples directory selection
        frame4 = ttk.Frame(self.wnd_main)
        frame4.pack(side=tk.TOP, fill=tk.X)

        tk.Label(frame4, text="Répertoire d'échantillons sonores", fg="black", anchor=tk.E, width=30).pack(side=tk.LEFT)

        # combobox showing the list of last opened definition files
        self.samples_dir_cmb = ttk.Combobox(frame4, state="readonly")
        self.samples_dir_cmb.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5,0))
        self.samples_dir_cmb.bind('<Button-1>', lambda event, widget=self.samples_dir_cmb: self.cmb_on_click(event, widget))
        self.samples_dir_cmb.bind('<<ComboboxSelected>>', lambda event, widget=self.samples_dir_cmb: self.cmb_on_selected(event, widget))

        # button for opening the file selection dialogbox
        self.samples_dir_sel_btn = tk.Button(frame4, text = "...", fg="black", width=3, command=lambda widget=self.samples_dir_cmb: self.btn_file_select(widget))
        self.samples_dir_sel_btn.pack(side=tk.RIGHT, padx=(5,5), pady=2)

        #---------- FRAME 5 -------------
        # horizontal frame with widgets for selection the actions to perform
        self.choices_frame = ttk.Frame(self.wnd_main)
        self.choices_frame.pack(side=tk.TOP, fill=tk.X)

        tk.Label(self.choices_frame, text="Que faire avec le fichier MIDI ?", fg="black", anchor=tk.E, width=30).pack(side=tk.LEFT)

        # integer variable to know which of the three radio buttons has been selected
        self.playback_choice = tk.IntVar()
        self.playback_choice_keyboard_rad = tk.Radiobutton(self.choices_frame, text = "Le jouer\nau clavier", fg="black", anchor='center', indicatoron=0,
                                                           offrelief='groove', overrelief='ridge', width=10, variable=self.playback_choice, value=1)
        self.playback_choice_keyboard_rad.pack(side=tk.LEFT, padx=(5,0))

        self.playback_choice_autoplayer_rad = tk.Radiobutton(self.choices_frame, text = "Le jouer au\njeu automatique", fg="black", anchor='center', indicatoron=0,
                                                             offrelief='groove', overrelief='ridge', width=15, variable=self.playback_choice, value=2)
        self.playback_choice_autoplayer_rad.pack(side=tk.LEFT, padx=(5,0))

        self.playback_choice_prog_gen_rad = tk.Radiobutton(self.choices_frame, text = "Générer un fichier de program-\nmation de jeu automatique", fg="black", anchor='center', indicatoron=0,
                                                           offrelief='groove', overrelief='ridge', width=25, variable=self.playback_choice, value=3)
        self.playback_choice_prog_gen_rad.pack(side=tk.LEFT, padx=(5,0))

        # button to launch the MIDI file playback
        self.midi_play_btn = tk.Button(self.choices_frame, text="C'est parti !", fg='black', width=12, height=2, command=self.midi_file_playback_start_stop)
        self.midi_play_btn.pack(side=tk.LEFT, padx=(10,20), pady=2)
        self.midi_play_btn.config(font=(self.midi_play_btn["font"], 9, "bold"))

        # button to launch the test of the keyboard
        self.test_keyboard_btn = tk.Button(self.choices_frame, text="Tester\nclavier", fg='black', width=12, height=2, command=self.keyboard_test_start_stop)
        self.test_keyboard_btn.pack(side=tk.LEFT, padx=(10,0))

        # button to launch the test of the autoplayer
        self.test_autoplayer_btn = tk.Button(self.choices_frame, text="Tester jeu\nautomatique", fg='black', width=12, height=2, command=self.autoplayer_test_start_stop)
        self.test_autoplayer_btn.pack(side=tk.LEFT, padx=(10,20))

        # check button to record the sound generated by the application
        self.record_wav = tk.IntVar()
        self.record_wav_chkbtn = tk.Checkbutton(self.choices_frame, text = "Enregistrer\nle son", fg="black", width=12, anchor='center', indicatoron=0,
                                                           offrelief='groove', overrelief='ridge', variable=self.record_wav, command=self.audio_record_start_stop)
        self.record_wav_chkbtn.pack(side=tk.LEFT, padx=(10,10))

        tk.Label(self.choices_frame, text="Transpositeur\n(demi-tons)", fg="black", anchor=tk.E).pack(side=tk.RIGHT)

        #---------- FRAME 6 -------------
        # horizontal frame with the autoplayer canvas
        self.autoplayer_frame = ttk.Frame(self.wnd_main)
        self.autoplayer_frame.pack(side=tk.TOP, fill=tk.X)

        tk.Label(self.autoplayer_frame, text="Jeu automatique", fg="black", anchor=tk.E, width=30).pack(side=tk.LEFT)

        self.levers_canvas = tk.Canvas(self.autoplayer_frame, height=70)
        self.levers_canvas.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5,0))
        self.levers_canvas.bind('<Button-1>', self.autoplayer_lever_click_left)

        self.autoplayer_trans_value = tk.IntVar(value=0)
        self.autoplayer_trans_spn = tk.Spinbox(self.autoplayer_frame, from_=-10, to=10, justify=tk.CENTER, width=5, format='%+0.0f',
                                             textvariable=self.autoplayer_trans_value, command=self.autoplayer_trans_changed_evt)
        self.autoplayer_trans_spn.pack(side=tk.RIGHT, padx=(5,5), pady=2)

        #---------- FRAME 7 -------------
        # horizontal frame with the manual keyboard canvas
        self.keyboard_frame = ttk.Frame(self.wnd_main)
        self.keyboard_frame.pack(side=tk.TOP, fill=tk.X)

        tk.Label(self.keyboard_frame, text="Clavier", fg="black", anchor=tk.E, width=30).pack(side=tk.LEFT)

        self.keyboard_canvas = tk.Canvas(self.keyboard_frame, height=70)
        self.keyboard_canvas.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5,0))
        self.keyboard_canvas.bind('<Button-1>', lambda event, widget=self.keyboard_canvas: self.keyboard_key_click_left_evt(event, widget))

        self.keyboard_trans_value = tk.IntVar(value=0)
        self.keyboard_trans_spn = tk.Spinbox(self.keyboard_frame, from_=-10, to=10, justify=tk.CENTER, width=5, format='%+0.0f',
                                             textvariable=self.keyboard_trans_value, command=self.keyboard_trans_changed_evt)
        self.keyboard_trans_spn.pack(side=tk.RIGHT, padx=(5,5), pady=2)

        #---------- FRAME 8 -------------
        # horizontal frame with the pedal keyboard canvas
        self.pedal_frame = ttk.Frame(self.wnd_main)
        self.pedal_frame.pack(side=tk.TOP, fill=tk.X)

        tk.Label(self.pedal_frame, text="Pédalier", fg="black", anchor=tk.E, width=30).pack(side=tk.LEFT)

        self.pedalboard_canvas = tk.Canvas(self.pedal_frame, height=70)
        self.pedalboard_canvas.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5,0))
        self.pedalboard_canvas.bind('<Button-1>', lambda event, widget=self.pedalboard_canvas: self.keyboard_key_click_left_evt(event, widget))

        #---------- FRAME 9 -------------
        # horizontal frame with the playback controls
        frame9 = ttk.Frame(self.wnd_main)
        frame9.pack(side=tk.TOP, fill=tk.X)

        self.clear_logs_btn = tk.Button(frame9, text="Effacer ↓", fg="black", command=self.logs_clear)
        self.clear_logs_btn.pack(side=tk.LEFT, padx=(5,0), pady=2)

        # label to show the playback position
        self.playback_position_label = tk.Label(frame9, text="00.00 / 00.00", fg="black", width=15, anchor=tk.E)
        self.playback_position_label.pack(side=tk.LEFT, padx=(120,0))

        # scale to show/change the playback position
        self.playback_position_value = tk.DoubleVar()
        self.playback_position_scale = ttk.Scale(frame9, from_=0, to=100, orient='horizontal', variable=self.playback_position_value, command=self.playback_position_changing_evt)
        self.playback_position_scale.pack(side=tk.LEFT, padx=(5,0))
        self.playback_position_scale.bind("<ButtonRelease-1>", self.playback_position_changed_evt)

        # integer variable and associated check button to put the playback in pause
        self.play_pause_status = tk.IntVar()
        self.play_pause_chkbtn = tk.Checkbutton(frame9, text = "PAUSE", fg="black", width=7, anchor='center', indicatoron=0, variable=self.play_pause_status)
        self.play_pause_chkbtn.pack(side=tk.LEFT, padx=(5,0))

        # label to show the playback speed setting
        self.playback_speed_label = tk.Label(frame9, text="Vitesse 100%", fg="black", width=15,anchor=tk.E)
        self.playback_speed_label.pack(side=tk.LEFT, padx=(5,0))

        # scale to show/change the playback speed
        self.playback_speed_scale = ttk.Scale(frame9, from_=50, to=150, orient='horizontal', command=self.playback_speed_changing_evt)
        self.playback_speed_scale.pack(side=tk.LEFT, padx=(5,0))
        self.playback_speed_scale.bind('<Double-1>', lambda event: self.playback_speed_scale.set(100))
        self.playback_speed_scale.bind("<ButtonRelease-1>", self.playback_speed_changed_evt)

        # label to show the audio volume setting
        self.audio_volume_label = tk.Label(frame9, text="Volume 100%", fg="black", width=15, anchor=tk.E)
        self.audio_volume_label.pack(side=tk.LEFT, padx=(5,0))

        # scale to show/change the audio volume
        self.audio_volume_scale = ttk.Scale(frame9, from_=1, to=200, orient='horizontal', command=self.audio_volume_changing)
        self.audio_volume_scale.pack(side=tk.LEFT, padx=(5,0))
        self.audio_volume_scale.bind('<Double-1>', lambda event: self.audio_volume_scale.set(100))

        #---------- FRAME 10 -------------
        # frame filling the bottom of the application's window with text box and vertical slider to show logs and messages
        frame9 = ttk.Frame(self.wnd_main)
        frame9.pack(side=tk.TOP, fill=tk.BOTH)

        scrollbarv = ttk.Scrollbar(frame9, orient=tk.VERTICAL)
        scrollbarv.pack(side=tk.RIGHT, fill=tk.Y, padx=2, pady=3)

        self.logs_text = tk.Text(frame9, fg="black", bg='snow2', bd=3, wrap="none", selectbackground="grey", font='Calibri 11', state=tk.DISABLED)
        self.logs_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5,0), pady=3)
        self.logs_text.config(yscrollcommand=scrollbarv.set)
        scrollbarv.config(command=self.logs_text.yview)


        global logs_display_fct
        logs_display_fct = self.logs_display

        # create an instance of the audio player
        self.wav_player = C_WAV_PLAYER()

        # create an instance of the auto player
        self.auto_player = C_AUTO_PLAYER()

        # create an instance of the audio player
        self.midi_file = C_MIDI_FILE()

        # recover the saved data
        self.app_data_load()
        self.playback_choice.set(True)

        try:
            self.midi_port = mido.open_input(callback=self.midi_input_message)
        except OSError:
            # no MIDI device connected
            self.midi_port = None

        # update the status and value of some widgets
        self.audio_volume_scale.set(100)
        self.playback_speed_scale.set(100)
        self.widgets_status_update()

        # start the background thread of the application
        self.app_is_running = True
        self.background_thread = threading.Thread(target=self.background_thread_fct)
        self.background_thread.start()

        return self.wnd_main

##    #-------------------------------------------------------------------------------------------------
##    def wnd_main_configure(self, event):
##        # (GUI event callback) the main window configuration has changed
##
##        if not self.app_is_running:
##            return
##
##        if str(event.widget) == '.':
##            # configure event of the main window
##            # resize some widgets so that they follow the size of the main window
##
##            self.midi_files_cmb.place(width=int(event.width) - self.midi_files_cmb.winfo_x() - 40)
##            self.midi_file_sel_btn.place(x=int(event.width) - self.samples_dir_sel_btn.winfo_width() - 10)
##
##            self.carillon_def_files_cmb.place(width=int(event.width) - self.carillon_def_files_cmb.winfo_x() - 40)
##            self.carillon_def_file_sel_btn.place(x=int(event.width) - self.carillon_def_file_sel_btn.winfo_width() - 10)
##
##            self.samples_dir_cmb.place(width=int(event.width) - self.samples_dir_cmb.winfo_x() - 40)
##            self.samples_dir_sel_btn.place(x=int(event.width) - self.samples_dir_sel_btn.winfo_width() - 10)
##
##            self.about_btn.place(x=int(event.width) - self.about_btn.winfo_width() - 10)
##
##            self.levers_canvas.place(width=int(event.width) - self.levers_canvas.winfo_x() - 20)
##
##            self.keyboard_canvas.place(width=int(event.width) - self.keyboard_canvas.winfo_x() - 100)
##            self.keyboard_trans_lbl.place(x=int(event.width) - 90)
##            self.keyboard_trans_spn.place(x=int(event.width) - 75)
##
##            self.pedalboard_canvas.place(width=int(event.width) - self.keyboard_canvas.winfo_x() - 100)
##
##            # logs frame resize
##            self.logs_frm.place(width=int(event.width) - 10 - 10, height=int(event.height) - self.logs_frm.winfo_y() - 10)

    #-------------------------------------------------------------------------------------------------
    def wnd_main_quit(self):
        # (GUI event callback) the user has requested to close the main window

        self.app_is_running = False

        # stop any samples loading or notes / MIDI file playback in progress
        self.midi_file_playback_in_progress = False
        self.keyboard_test_in_progress = False
        self.autoplayer_test_in_progress = False

        self.wav_player.audio_samples_load_abort()
        self.wav_player.midi_note_stop(-1)
        self.wav_player.wav_file_record_end()
        self.wav_player.samples_dic.clear()

        if self.midi_port is not None:
            self.midi_port.close()

        # save the data of the application
        self.app_data_save()

        # destroy the main window
        self.wnd_main.destroy()

    #------------------------------------------------------------------------
    def widgets_status_update(self):

        if not self.app_is_running:
            return

        audio_samples_load = self.audio_samples_load_in_progress
        audio_playback = self.midi_file_playback_in_progress and self.playback_choice.get() in (1, 2)
        prog_file_gen = self.midi_file_playback_in_progress and self.playback_choice.get() == 3
        keyboard_test = self.keyboard_test_in_progress
        autoplayer_test = self.autoplayer_test_in_progress
        no_activity = not(audio_samples_load or audio_playback or prog_file_gen or keyboard_test or autoplayer_test)

        self.midi_files_cmb['state'] = 'readonly' if no_activity else tk.DISABLED
        self.midi_file_sel_btn['state'] = tk.NORMAL if no_activity else tk.DISABLED

        self.carillon_def_files_cmb['state'] = 'readonly' if no_activity else tk.DISABLED
        self.carillon_def_file_sel_btn['state'] = tk.NORMAL if no_activity else tk.DISABLED

        self.samples_dir_cmb['state'] = 'readonly' if no_activity or audio_samples_load else tk.DISABLED
        self.samples_dir_sel_btn['state'] = tk.NORMAL if no_activity or audio_samples_load else tk.DISABLED

        self.playback_choice_keyboard_rad['state'] = tk.NORMAL if no_activity or audio_samples_load else tk.DISABLED
        self.playback_choice_autoplayer_rad['state'] = tk.NORMAL if no_activity or audio_samples_load else tk.DISABLED
        self.playback_choice_prog_gen_rad['state'] = tk.NORMAL if no_activity or audio_samples_load else tk.DISABLED

        self.midi_play_btn['text'] = "Interrompre" if audio_playback or prog_file_gen else "C'est parti !"
        self.midi_play_btn['state'] = tk.NORMAL if no_activity or audio_playback or prog_file_gen else tk.DISABLED

        self.test_keyboard_btn['text'] = "Interrompre" if keyboard_test else "Tester\nclavier"
        self.test_keyboard_btn['state'] = tk.NORMAL if no_activity or keyboard_test else tk.DISABLED

        self.test_autoplayer_btn['text'] = "Interrompre" if autoplayer_test else "Tester\njeu auto."
        self.test_autoplayer_btn['state'] = tk.NORMAL if (no_activity or autoplayer_test)  else tk.DISABLED

        self.record_wav_chkbtn['state'] = tk.NORMAL if not audio_samples_load else tk.DISABLED

        self.playback_position_label['state'] = tk.NORMAL if audio_playback or prog_file_gen or keyboard_test or autoplayer_test else tk.DISABLED
        self.playback_position_scale['state'] = tk.NORMAL if audio_playback or keyboard_test or autoplayer_test else tk.DISABLED
        self.play_pause_chkbtn['state'] = tk.NORMAL if audio_playback or keyboard_test or autoplayer_test else tk.DISABLED

        self.play_pause_status.set(0)

    #------------------------------------------------------------------------
    def cmb_on_click(self, event, widget):
        # (GUI event callback) a combobox widget has been clicked by the mouse button 1
        # check that all files/directories listed inside are still valid before to let the combobox be opened

        items_lst = list(widget['values'])  # make a copy of the items list
        for item_text in widget['values']:
            if (item_text != ''
                and ((widget == self.samples_dir_cmb and not os.path.isdir(item_text))
                     or (widget != self.samples_dir_cmb and not os.path.isfile(item_text)))):
                items_lst.remove(item_text)

        # update the items list of the combobox
        widget['values'] = items_lst

    #------------------------------------------------------------------------
    def cmb_on_selected(self, event, widget):
        # (GUI event callback) an item has been selected in a combobox widget
        # place the selected item at the top of the combobox items list

        item_text = widget.get()
        if item_text != '':
            # move the selected item at the beginning of the combobox list
            items_lst = list(widget['values'])  # make a copy of the items list
            items_lst.remove(item_text)
            items_lst.insert(0, item_text)

            # update the items list of the combobox
            widget['values'] = items_lst

        if widget == self.midi_files_cmb:
            self.midi_notes_to_play_lst.clear()   # to trigger a midi notes to play reload in background_thread_fct

        elif widget == self.carillon_def_files_cmb:
            self.manual_keys_dic.clear()   # to trigger a carillon definition file reload in background_thread_fct

        elif widget == self.samples_dir_cmb:
            if self.wav_player.samples_loading_in_progress:
                self.wav_player.audio_samples_load_abort()
                time.sleep(0.1)  # to let the time to the samples loading in progress, if any, to stop
            self.wav_player.samples_dic.clear()   # to trigger an audio samples reload in background_thread_fct

    #------------------------------------------------------------------------
    def btn_file_select(self, widget):
        # (GUI event callback) the user has clicked on the button'...' to select a file or a folder
        # if a file / folder has been selected, add it at the beginning of the combobox items list

        if widget == self.midi_files_cmb:
            new_item = filedialog.askopenfilename(title='Sélectionner un fichier MIDI', initialdir=os.path.dirname(widget.get()),
                                                   filetypes=[('Fichier MIDI', '*.mid')])
        elif widget == self.carillon_def_files_cmb:
            new_item = filedialog.askopenfilename(title='Sélectionner un fichier de définition de jeu automatique', initialdir=os.path.dirname(widget.get()),
                                                   filetypes=[('Fichier INI', '*.ini')])
        elif widget == self.samples_dir_cmb:
            new_item = filedialog.askdirectory(title='Sélectionner un répertoire contenant des échantillons sonores (fichiers .wav)',
                                                   initialdir=os.path.dirname(widget.get()))
        else:
            return

        if new_item != '':
            if widget == self.samples_dir_cmb:
                wav_files_nb = 0
                for file_dir_name in os.listdir(new_item):
                    if file_dir_name.endswith(".wav"):
                        wav_files_nb += 1
                        if wav_files_nb == 12:
                            # there are enough files in the folder
                            break
##                if wav_files_nb < 12:
                if wav_files_nb == 0:
                    tk.messagebox.showerror(APP_NAME, "Le dossier sélectionné ne contient aucun fichier avec l'extension .wav")
##                    elif wav_files_nb == 1:
##                        tk.messagebox.showerror(APP_NAME, "Le dossier sélectionné ne contient qu'un seul fichier avec l'extension .wav, il en faut un minimum de 12")
##                    else:
##                        tk.messagebox.showerror(APP_NAME, f"Le dossier sélectionné ne contient que {wav_files_nb} fichiers avec l'extension .wav, il en faut un minimum de 12")
                    return

            # put the selected file/folder name at the beginning of the combobox items list
            items_lst = list(widget['values'])  # make a copy of the items list
            if new_item in items_lst:
                items_lst.remove(new_item)
            items_lst.insert(0, new_item)

            # if the list has more than 20 items, delete the last one
            if len(items_lst) > 20:
                items_lst = items_lst[0:19] + ['']

            # update the items list of the combobox
            widget['values'] = items_lst
            widget.current(0)

            if widget == self.midi_files_cmb:
                self.midi_notes_to_play_lst.clear()   # to trigger a midi notes to play reload in background_thread_fct

            elif widget == self.carillon_def_files_cmb:
                self.manual_keys_dic.clear()          # to trigger a carillon definition file reload in background_thread_fct

            elif widget == self.samples_dir_cmb:
                if self.wav_player.samples_loading_in_progress:
                    self.wav_player.audio_samples_load_abort()
                    time.sleep(0.1)  # to let the time to the samples loading in progress, if any, to stop
                self.wav_player.samples_dic.clear()   # to trigger an audio samples reload in background_thread_fct

    #------------------------------------------------------------------------
    def btn_about_app(self):

        tk.messagebox.showinfo(APP_NAME, ABOUT_MSG)

    #-------------------------------------------------------------------------------------------------
    def app_data_load(self):
        # load the application data saved in the data saving file (if it is present)

        file_name = os.path.dirname(__file__) + os.path.sep + app_data_file_name

        midi_files_names_lst = []
        definition_files_names_lst = []
        directories_names_lst = []

        if os.path.isfile(file_name):
            with open(file_name, 'r', encoding='utf_8_sig') as file:
                for line in file:
                    line_fields = line.split('=')
                    if len(line_fields) == 2:
                        attr_name = line_fields[0].strip()
                        attr_value = line_fields[1].strip()

                        if (attr_name == midi_file_name_sel_key
                            and (attr_value == '' or (os.path.isfile(attr_value) and attr_value.endswith('.mid')))):
                            self.midi_files_cmb.set(attr_value)

                        elif (attr_name == midi_file_name_key
                              and (attr_value == '' or (os.path.isfile(attr_value) and attr_value.endswith('.mid')))):
                            midi_files_names_lst.append(attr_value)

                        elif (attr_name == definition_file_name_sel_key
                              and (attr_value == '' or (os.path.isfile(attr_value) and attr_value.endswith('.ini')))):
                            self.carillon_def_files_cmb.set(attr_value)

                        elif (attr_name == definition_file_name_key
                              and (attr_value == '' or (os.path.isfile(attr_value) and attr_value.endswith('.ini')))):
                            definition_files_names_lst.append(attr_value)

                        elif (attr_name == samples_dir_sel_key
                              and (attr_value == '' or (os.path.isdir(attr_value)))):
                            self.samples_dir_cmb.set(attr_value)

                        elif (attr_name == samples_dir_key
                              and (attr_value == '' or (os.path.isdir(attr_value)))):
                            directories_names_lst.append(attr_value)

        if '' not in midi_files_names_lst:
            midi_files_names_lst.append('')
        if '' not in definition_files_names_lst:
            definition_files_names_lst.append('')
        if '' not in directories_names_lst:
            directories_names_lst.append('')

        self.midi_files_cmb['values'] = midi_files_names_lst
        self.carillon_def_files_cmb['values'] = definition_files_names_lst
        self.samples_dir_cmb['values'] = directories_names_lst

    #-------------------------------------------------------------------------------------------------
    def app_data_save(self):
        # save the application data in the data saving file

        file_name = os.path.dirname(__file__) + os.path.sep + app_data_file_name

        with open(file_name, 'w', encoding='utf_8_sig') as file:

            file.write(f"{midi_file_name_sel_key}={self.midi_files_cmb.get()}\n")
            for file_name in self.midi_files_cmb['values']:
                file.write(f"{midi_file_name_key}={file_name}\n")

            file.write(f"{definition_file_name_sel_key}={self.carillon_def_files_cmb.get()}\n")
            for file_name in self.carillon_def_files_cmb['values']:
                file.write(f"{definition_file_name_key}={file_name}\n")

            file.write(f"{samples_dir_sel_key}={self.samples_dir_cmb.get()}\n")
            for dir_name in self.samples_dir_cmb['values']:
                file.write(f"{samples_dir_key}={dir_name}\n")

    #------------------------------------------------------------------------
    def carillon_def_file_load(self, file_name):
        # load the content of the given carillon definition file
        # return True or False whether the loading has been done with success or failure

        if not os.path.isfile(file_name):
            # the given file doesn't exist
            logs_display_fct(f'PROBLEME : le fichier "{file_name}" n\'existe pas')
            self.carillon_def_file_name = None
            return False

        logs_display_fct(f'\nLecture du fichier de définition de carillon "{file_name}"...\n')

        # data to recover from the given file
        self.carillon_def_file_name = file_name
        self.carillon_name = None
        self.manual_keys_dic.clear()
        self.pedal_keys_dic.clear()
        self.autoplayer_marks_nb = None
        self.autoplayer_rev_time = None
        self.autoplayer_levers_to_midi_dic.clear()

        keyboard_transpose_value = None
        manual_first_key_midi_note = None
        manual_last_key_midi_note = None
        manual_missing_keys_midi_note_lst = []
        manual_inactive_keys_midi_note_lst = []
        pedal_first_key_midi_note = None
        pedal_last_key_midi_note = None
        pedal_missing_keys_midi_note_lst = []
        pedal_inactive_keys_midi_note_lst = []

        with open(file_name, 'r') as file:
            for line in file:
                # remove the ending \n character if present at the end of the current line
                if line[-1:] == '\n':
                    line = line[:-1]
                # lines starting by ; or empty are ignored
                if not line.startswith(';') and len(line) > 0:
                    # recover from the line the attribute name and value around the = character
                    line_fields = line.split('=')
                    if len(line_fields) == 2:
                        attr_name = line_fields[0].strip()
                        attr_value = line_fields[1].strip()
                        attr_value_fields = attr_value.split()

                        if attr_name == carillon_name_key:
                            self.carillon_name = attr_value

                        elif attr_name == keyboard_transpose_key:
                            if attr_value.replace('+', '').isnumeric():
                                keyboard_transpose_value = int(attr_value)
                            else:
                                logs_display_fct(f'PROBLEME : la valeur donnée dans la ligne "{line}" doit être un nombre entier\n')

                        elif attr_name in (manual_first_key, manual_last_key, manual_missings_key, manual_inactives_key,
                                           pedal_first_key,  pedal_last_key,  pedal_missings_key,  pedal_inactives_key):
                            field_midi_notes = []
                            for field_value in attr_value_fields:
                                field_value = field_value.strip()
                                midi_note = note_to_midi_nb(field_value)
                                if midi_note is None:
                                    logs_display_fct(f'PROBLEME : la note "{field_value}" n\'est pas reconnue dans la ligne "{line}"\n')
                                else:
                                    field_midi_notes.append(midi_note)

                            if len(field_midi_notes) == 0:
                                field_midi_notes.append(None)

                            if attr_name == manual_first_key:
                                manual_first_key_midi_note = field_midi_notes[0]
                            elif attr_name == manual_last_key:
                                manual_last_key_midi_note = field_midi_notes[0]
                            elif attr_name == manual_missings_key:
                                manual_missing_keys_midi_note_lst = field_midi_notes
                            elif attr_name == manual_inactives_key:
                                manual_inactive_keys_midi_note_lst = field_midi_notes

                            elif attr_name == pedal_first_key:
                                pedal_first_key_midi_note = field_midi_notes[0]
                            elif attr_name == pedal_last_key:
                                pedal_last_key_midi_note = field_midi_notes[0]
                            elif attr_name == pedal_missings_key:
                                pedal_missing_keys_midi_note_lst = field_midi_notes
                            elif attr_name == pedal_inactives_key:
                                pedal_inactive_keys_midi_note_lst = field_midi_notes

                        elif attr_name == autoplayer_marks_nb_key:
                            if attr_value.isdigit():
                                self.autoplayer_marks_nb = int(attr_value)
                            else:
                                logs_display_fct(f'PROBLEME : la valeur donnée dans la ligne "{line}" doit être un nombre entier\n')

                        elif attr_name == autoplayer_rev_time_key:
                            if attr_value.isdigit():
                                self.autoplayer_rev_time = int(attr_value) / 1000   # value in ms converted to seconds
                            else:
                                logs_display_fct(f'PROBLEME : la valeur donnée dans la ligne "{line}" doit être un nombre entier\n')

                        elif attr_name == autoplayer_lever_key:
                            lever_nb = None
                            play_midi_note = None
                            if len(attr_value_fields) > 0:
                                # get the first field if defined (a lever number)
                                if attr_value_fields[0].isdigit():
                                    lever_nb = int(attr_value_fields[0])
                                else:
                                    logs_display_fct(f'PROBLEME : le numéro de levier donné dans la ligne "{line}" doit être un nombre entier\n')

                                if len(attr_value_fields) == 2:
                                    # get the second field if defined (a played MIDI note)
                                    play_midi_note = note_to_midi_nb(attr_value_fields[1])
                                    if play_midi_note is None:
                                        logs_display_fct(f'PROBLEME : la note "{attr_value_fields[1]}" n\'est pas reconnue dans la ligne "{line}"\n')

                            if lever_nb is not None:
                                self.autoplayer_levers_to_midi_dic[lever_nb] = play_midi_note
                    else:
                        logs_display_fct(f'PROBLEME : la ligne "{line}" n\'a pas de caractère =\n')

        if self.carillon_name is None:
            logs_display_fct('Pas de nom de carillon défini\n')
        else:
            logs_display_fct(f'{self.carillon_name}\n')

        if keyboard_transpose_value in (None, 0):
            if keyboard_transpose_value == 0:
                logs_display_fct('Clavier non transpositeur\n')
            keyboard_transpose_value = 0
            self.keyboard_trans_spn['foreground'] = 'black'
        else:
            if keyboard_transpose_value > 10:
                logs_display_fct(f'PROBLEME : Transposition de {keyboard_transpose_value} supérieure à +10.\n')
                keyboard_transpose_value = 10
            elif keyboard_transpose_value < -10:
                logs_display_fct(f'PROBLEME : Transposition de {keyboard_transpose_value} inférieure à -10.\n')
                keyboard_transpose_value = -10
            logs_display_fct(f'Clavier transpositeur de {keyboard_transpose_value:+g} demi-tons\n')
            self.keyboard_trans_spn['foreground'] = 'red'
        if keyboard_transpose_value > 0:
            self.keyboard_trans_value.set('+' + str(keyboard_transpose_value))
        else:
            self.keyboard_trans_value.set(keyboard_transpose_value)

        if manual_first_key_midi_note is None:
            logs_display_fct('Pas de première note définie pour le clavier, clavier ignoré\n')
        if manual_last_key_midi_note is None:
            logs_display_fct('Pas de dernière note définie pour le clavier, clavier ignoré\n')
        if manual_first_key_midi_note is not None and manual_last_key_midi_note is not None and manual_first_key_midi_note >= manual_last_key_midi_note:
            logs_display_fct('Première note supérieure ou égale à la dernière note, clavier ignoré\n')
            manual_first_key_midi_note = None

        if manual_first_key_midi_note is not None and manual_last_key_midi_note is not None:
            # build the keys list of the manual keyboard, removing missing keys and erasing inactive keys
            for key_midi_note in range(manual_first_key_midi_note, manual_last_key_midi_note + 1):
                self.manual_keys_dic[key_midi_note] = key_midi_note

            for key_midi_note in manual_missing_keys_midi_note_lst:
                if key_midi_note in self.manual_keys_dic.keys():
                    self.manual_keys_dic.pop(key_midi_note)

            for key_midi_note in manual_inactive_keys_midi_note_lst:
                if key_midi_note in self.manual_keys_dic.keys():
                    self.manual_keys_dic[key_midi_note] = None

            key_note_first = midi_nb_to_note(min(self.manual_keys_dic.keys()), 'fra')
            key_note_last  = midi_nb_to_note(max(self.manual_keys_dic.keys()), 'fra')
            logs_display_fct(f'{len(self.manual_keys_dic)} notes de clavier définies ({key_note_first} à {key_note_last}), dont {len(manual_inactive_keys_midi_note_lst)} inactive(s)\n')

            if pedal_first_key_midi_note is None:
                logs_display_fct('Pas de première note définie pour le pédalier, pédalier ignoré\n')
            if pedal_last_key_midi_note is None:
                logs_display_fct('Pas de dernière note définie pour le pédalier, pédalier ignoré\n')
            if pedal_first_key_midi_note is not None and pedal_last_key_midi_note is not None and pedal_first_key_midi_note >= pedal_last_key_midi_note:
                logs_display_fct('Première note supérieure ou égale à la dernière note, pédalier ignoré\n')
                pedal_first_key_midi_note = None

            if pedal_first_key_midi_note is not None and pedal_last_key_midi_note is not None:
                # build the keys list of the pedal keyboard, removing missing keys and erasing inactive keys
                for key_midi_note in range(pedal_first_key_midi_note, pedal_last_key_midi_note + 1):
                    self.pedal_keys_dic[key_midi_note] = key_midi_note

                for key_midi_note in pedal_missing_keys_midi_note_lst:
                    if key_midi_note in self.pedal_keys_dic.keys():
                        self.pedal_keys_dic.pop(key_midi_note)

                for key_midi_note in pedal_inactive_keys_midi_note_lst:
                    if key_midi_note in self.pedal_keys_dic.keys():
                        self.pedal_keys_dic[key_midi_note] = None

                key_note_first = midi_nb_to_note(min(self.pedal_keys_dic.keys()), 'fra')
                key_note_last  = midi_nb_to_note(max(self.pedal_keys_dic.keys()), 'fra')
                logs_display_fct(f'{len(self.pedal_keys_dic)} notes de pédalier définies ({key_note_first} à {key_note_last}), dont {len(pedal_inactive_keys_midi_note_lst)} inactive(s)\n')

        if len(self.autoplayer_levers_to_midi_dic) > 0:
            logs_display_fct('Jeu automatique :\n')
            logs_display_fct(f'   {len(self.autoplayer_levers_to_midi_dic)} leviers définis\n')

            if self.autoplayer_marks_nb is None:
                logs_display_fct(f'   PROBLEME : la valeur "{autoplayer_marks_nb_key}" n\'est pas définie, jeu automatique ignoré\n')
                self.autoplayer_levers_to_midi_dic.clear()
            else:
                logs_display_fct(f'   {self.autoplayer_marks_nb} repères de notation\n')

            if self.autoplayer_rev_time is None:
                logs_display_fct(f'   PROBLEME : la valeur "{autoplayer_rev_time_key}" n\'est pas définie, jeu automatique ignoré\n')
                self.autoplayer_levers_to_midi_dic.clear()
            else:
                logs_display_fct(f'   {self.autoplayer_rev_time} secondes de révolution des repères\n')
        else:
            logs_display_fct('Pas de jeu automatique défini\n')

        return True

    #-------------------------------------------------------------------------------------------------
    def autoplayer_display(self):
        # display the autoplayer in the canvas widget

        self.levers_canvas.delete('all')

        if len(self.autoplayer_levers_to_midi_dic) == 0:
            # hide the autoplayer frame if there are no levers to display
            self.autoplayer_frame.pack_forget()
            return

        # display the autoplayer frame
        self.autoplayer_frame.pack(after=self.choices_frame, side=tk.TOP, fill=tk.X)

        x = 10
        y_levers = 5
        y_numbers = 50

        self.canvas_levers_nb_to_id_dic = {}

        last_lever_nb = max(self.autoplayer_levers_to_midi_dic.keys())

        for lever_nb in range(1, last_lever_nb + 1):
            # display the lever number and the note controlled by the lever
            lever_tag = 'L' + str(lever_nb)
            midi_note = mydickey(self.autoplayer_levers_to_midi_dic, lever_nb)

            # define the color of the lever
            if midi_note is None:
                # the lever is not controlling a MIDI note
                status_tag = 'S0'
                note_color = color_key_inactive
                self.canvas_levers_nb_to_id_dic[lever_nb] = self.levers_canvas.create_text(x, y_levers, text='\nx\nx', fill=note_color, anchor=tk.N, tags=(lever_tag, status_tag))
            else:
                if (len(self.wav_player.samples_dic) == 0
                    or midi_note + int(self.autoplayer_trans_value.get()) not in self.wav_player.samples_dic.keys()):
                    # the lever is controlling a MIDI note which has no audio sample
                    status_tag = 'S1'
                    note_color = color_key_inactive
                else:
                    # the lever is controlling a MIDI note which has an audio sample
                    status_tag = 'S2'
                    note_color = color_key_active
                midi_tag = 'M' + str(midi_note)
                (note_name, sharp, octave) = midi_nb_to_note_split(midi_note)
                self.canvas_levers_nb_to_id_dic[lever_nb] = self.levers_canvas.create_text(x, y_levers, text=f'{sharp}\n{note_name}\n{str(octave)}', fill=note_color, anchor=tk.N, tags=(lever_tag, midi_tag, status_tag))

            if lever_nb % 5 == 0 or lever_nb == 1:
                # each 5 levers display the lever number and a vertical graduation
                self.levers_canvas.create_text(x, y_numbers + 15, text=str(lever_nb), fill='white')
                self.levers_canvas.create_line(x, y_numbers, x, y_numbers + 10, fill='white')

            x += 10

        # display an horizontal bar under the levers
        rect_id = self.levers_canvas.create_rectangle(0, y_numbers, x - 5, y_numbers + 25, fill='grey', width = 0)
        self.levers_canvas.tag_lower(rect_id)

    #-------------------------------------------------------------------------------------------------
    def autoplayer_levers_raise(self, levers_nb_to_raise_lst):
        # raise up the given levers of the autoplayer

        for lever_nb in levers_nb_to_raise_lst:
            lever_id = mydickey(self.canvas_levers_nb_to_id_dic, lever_nb)
            if lever_id is not None:
                lever_tags_list = self.levers_canvas.gettags(lever_id)
                if 'ON' not in lever_tags_list:
                    # the lever is not yet raised
                    for tag in lever_tags_list:
                        if tag in ('S0', 'S1'):
                            self.levers_canvas.itemconfigure(lever_id, fill=color_key_inactive_pressed)
                        elif tag  == 'S2':
                            self.levers_canvas.itemconfigure(lever_id, fill=color_key_active_pressed)

                            # play the note controlled by the lever
                            midi_note = mydickey(self.autoplayer_levers_to_midi_dic, lever_nb)
                            self.wav_player.midi_note_play(midi_note + self.autoplayer_trans_value.get())
                    # move the lever up
                    self.levers_canvas.move(lever_id, 0, -5)
                    self.levers_canvas.addtag_withtag('ON', lever_id)

        # prepare the call to drop the levers after 250 ms
        self.wnd_main.after(250, self.autoplayer_levers_drop, list(levers_nb_to_raise_lst))

    #-------------------------------------------------------------------------------------------------
    def autoplayer_levers_drop(self, levers_nb_to_drop_lst):
        # drop down the given levers of the autoplayer

        for lever_nb in levers_nb_to_drop_lst:
            lever_id = mydickey(self.canvas_levers_nb_to_id_dic, lever_nb)
            if lever_id is not None:
                lever_tags_list = self.levers_canvas.gettags(lever_id)
                if 'ON' in lever_tags_list:
                    # the lever is raised
                    for tag in lever_tags_list:
                        if tag in ('S0', 'S1'):
                            self.levers_canvas.itemconfigure(lever_id, fill=color_key_inactive)
                        elif tag  == 'S2':
                            self.levers_canvas.itemconfigure(lever_id, fill=color_key_active)
                    # move the lever down
                    self.levers_canvas.move(lever_id, 0, 5)
                    self.levers_canvas.dtag(lever_id, 'ON')

    #------------------------------------------------------------------------
    def autoplayer_lever_click_left(self, event):
        # (GUI callback) the user has left clicker on the autoplayer levers canvas

        if self.audio_samples_load_in_progress:
            return

        # recover the coordinates of the mouse in the coordinates of the canvas
        x_canvas_mouse = self.levers_canvas.canvasx(event.x)
        y_canvas_mouse = self.levers_canvas.canvasy(event.y)
        # recover the ID of the object under the mouse cursor
        object_id = self.levers_canvas.find_overlapping(x_canvas_mouse, y_canvas_mouse, x_canvas_mouse, y_canvas_mouse)

        # recover the lever nb and MIDI note of the clicked object if any
        for tag in self.levers_canvas.gettags(object_id):
            if tag[0] == 'L':
                lever_nb = int(tag[1:])
                # raise and play the note of the clicked object if any
                self.autoplayer_levers_raise((lever_nb,))
                break

    #-------------------------------------------------------------------------------------------------
    def autoplayer_trans_changed_evt(self):
        # (GUI callback) the user has changed the value of the spinbox widget to set the autoplayer transposition value

        if int(self.autoplayer_trans_value.get()) == 0:
            self.autoplayer_trans_spn['foreground'] = 'black'
        else:
            self.autoplayer_trans_spn['foreground'] = 'red'

        self.autoplayer_display()

    #------------------------------------------------------------------------
    def autoplayer_test_start_stop(self):
        # start/stop the autoplayer test

        if not self.autoplayer_test_in_progress:

            if len(self.autoplayer_levers_to_midi_dic) == 0:
                # no autoplayer levers have been defined
                tk.messagebox.showwarning(APP_NAME, "Veuillez sélectionner un fichier de définition de carillon contenant une définition de jeu automatique valide")
                return

            self.autoplayer_test_in_progress = True
            self.widgets_status_update()

            # the execution is continued in the function self.background_thread_fct which will call autoplayer_test

        else:
            self.autoplayer_test_in_progress = False
            self.widgets_status_update()
            self.logs_display( '\nTest interrompu\n')

    #------------------------------------------------------------------------
    def autoplayer_test(self):
        # test sequentially all the levers of the auto player

        levers_nb = len(self.autoplayer_levers_to_midi_dic)

        if levers_nb == 0:
            self.logs_display( '\nIl n\'y a pas de leviers de jeu automatique définis\n')

        self.playback_position_scale['from_'] = 1
        self.playback_position_scale['to'] = levers_nb
        self.playback_position_value.set(1)
        self.playback_position_changed = False

        lever_nb = 1
        while lever_nb <= levers_nb:

            if not self.playback_scale_moving:
                # update the playback position text and scale
                self.playback_position_value.set(lever_nb)
                self.playback_position_label['text'] = f'{lever_nb} / {levers_nb}'

            self.autoplayer_levers_raise((lever_nb,))

            time.sleep(0.3 / self.playback_speed_factor)

            while self.play_pause_status.get() == 1:
                time.sleep(0.1)

            if not self.autoplayer_test_in_progress:
                break

            if self.playback_position_changed:
                lever_nb = round(self.playback_position_value.get())
                self.playback_position_changed = False
            else:
                lever_nb += 1

    #-------------------------------------------------------------------------------------------------
    def keyboard_display(self):
        # display the keyboards (manual and pedal) in the canvas widget

        for keyboard_id in ('m', 'p'):
            # display the manual and pedal keyboards

            # get the data of the current keyboard to display
            if keyboard_id == 'm':
                widget = self.keyboard_canvas
                keys_dic = self.manual_keys_dic

                # dictionary storing the ID of each key item in the canvas from its MIDI note
                keys_id_dic = self.canvas_keys_id_dic = {}

                # define the positions and dimensions attributes of the keys
                x0 = x = 6
                y = 25
                note_width = 10
                notes_period = note_width * 2 + 4
                natural_notes_height = 40
                sharp_notes_height = int(natural_notes_height / 2)
                text_x_offset = 2
            else:
                widget = self.pedalboard_canvas
                keys_dic = self.pedal_keys_dic

                # dictionary storing the ID of each key item in the canvas from its MIDI note
                keys_id_dic = self.canvas_pedals_id_dic = {}

                # define the positions and dimensions attributes of the keys
                x0 = x = 60
                y = 25
                note_width = 15
                notes_period = note_width * 2 + 6
                natural_notes_height = 40
                sharp_notes_height = int(natural_notes_height / 2)
                text_x_offset = 5

            # delete all existing items in the canvas widget of the current keyboard
            widget.delete('all')

            if len(keys_dic) == 0:
                # none key to display for the current keyboard
                if keyboard_id == 'p':
                    # hide the pedal keyboard frame
                    self.pedal_frame.pack_forget()
                continue

            if keyboard_id == 'p':
                # display the pedal keyboard frame
                self.pedal_frame.pack(after=self.keyboard_frame, side=tk.TOP, fill=tk.X)

            # get the range of the MIDI notes of the keyboard or pedalboard
            key_midi_note_first = min(keys_dic.keys())
            key_midi_note_last  = max(keys_dic.keys())

            # display the keys of the current keyboard
            for midi_note in range(key_midi_note_first, key_midi_note_last + 1):
                midi_tag = 'M' + str(midi_note)
                (note_name, sharp, octave) = midi_nb_to_note_split(midi_note)

                if midi_note not in keys_dic.keys():
                    # there is no key in the keyboard for the MIDI note
                    status_tag = 'S0'
                    note_color = ''  # transparent key
                elif (keys_dic[midi_note] is None
                      or len(self.wav_player.samples_dic) == 0
                      or midi_note + int(self.keyboard_trans_value.get()) not in self.wav_player.samples_dic.keys()):
                    # the key is not controlling a MIDI note or there is no audio sample for this MIDI note
                    status_tag = 'S1'
                    note_color = color_key_inactive  # inactive key
                else:
                    # the key is controlling a MIDI note which has an audio sample
                    status_tag = 'S2'
                    note_color = color_key_active  # active key

                # display the current key
                if len(sharp) > 0:
                    # sharp key
                    if midi_note != key_midi_note_first:
                        x -= notes_period / 2
                    keys_id_dic[midi_note] = widget.create_rectangle(x, y, x + note_width, y + sharp_notes_height, width=0, fill=note_color, tags=(midi_tag, status_tag))
                    if midi_note == key_midi_note_last:
                        x += notes_period
                    else:
                        x += notes_period / 2
                else:
                    # natural key
                    keys_id_dic[midi_note] = widget.create_rectangle(x, y, x + note_width, y + natural_notes_height, width=0, fill=note_color, tags=(midi_tag, status_tag))
                    x += notes_period

            # display a horizontal rectangle on top of the keys
            widget.create_rectangle(x0 - 6, 0, x - notes_period/2, 25, fill='grey', width = 0)

            # display in the rectangle the octaves numbers at each C key or at the first key
            x = x0
            for midi_note in range(key_midi_note_first, key_midi_note_last + 1):
                # get the MIDI note name
                (note_name, sharp, octave) = midi_nb_to_note_split(midi_note)

                if (note_name == 'C' and len(sharp) == 0) or midi_note == key_midi_note_first:
                    widget.create_text(x + text_x_offset, y - 13, text=str(octave), anchor=tk.W, fill='white')

                if len(sharp) > 0:
                    # sharp key
                    if midi_note != key_midi_note_first:
                        x -= notes_period / 2
                    if midi_note == key_midi_note_last:
                        x += notes_period
                    else:
                        x += notes_period / 2
                else:
                    # natural key
                    x += notes_period

    #-------------------------------------------------------------------------------------------------
    def keyboard_keys_press(self, keys_midi_notes_to_press_lst, pressed_keyboard_id=None):
        # execute a press on the keys of the keyboard (manual and pedal) for the given MIDI notes and play their sound
        # the pedalboard is pressed only if pressed_keyboard_id = 'p'
        # the given MIDI notes list must be a list of tuples (midi_note, midi_velocity)

        for midi_note, midi_velocity in keys_midi_notes_to_press_lst:

            note_played = False

            key_id = mydickey(self.canvas_keys_id_dic, midi_note)
            if key_id is not None:
                # the MANUAL keyboard has a key for the current MIDI note
                key_tags_list = self.keyboard_canvas.gettags(key_id)
                if 'ON' not in key_tags_list:
                    # the key is not yet pressed
                    # set the pressed color
                    for tag in key_tags_list:
                        if tag in ('S0', 'S1'):
                            self.keyboard_canvas.itemconfig(key_id, fill=color_key_inactive_pressed)
                        elif tag  == 'S2':
                            self.keyboard_canvas.itemconfig(key_id, fill=color_key_active_pressed)

                            # play the note controlled by the key, if not already played by the other keyboard
                            self.wav_player.midi_note_play(midi_note + int(self.keyboard_trans_value.get()), midi_velocity)
                            note_played = True
                    # move the key up
                    self.keyboard_canvas.move(key_id, 0, -3)
                    self.keyboard_canvas.addtag_withtag('ON', key_id)

            key_id = mydickey(self.canvas_pedals_id_dic, midi_note)
            if key_id is not None and pressed_keyboard_id == 'p':
                # the PEDAL keyboard has a key for the current MIDI note, and it is pressed
                key_id = self.canvas_pedals_id_dic[midi_note]
                key_tags_list = self.pedalboard_canvas.gettags(key_id)
                if 'ON' not in key_tags_list:
                    # the key is not yet pressed
                    # set the pressed color
                    for tag in key_tags_list:
                        if tag in ('S0', 'S1'):
                            self.pedalboard_canvas.itemconfig(key_id, fill=color_key_inactive_pressed)
                        elif tag  == 'S2':
                            self.pedalboard_canvas.itemconfig(key_id, fill=color_key_active_pressed)

                            if not note_played:
                                # play the note controlled by the key, if not already played by the other keyboard
                                self.wav_player.midi_note_play(midi_note + int(self.keyboard_trans_value.get()), midi_velocity)
                    # move the key up
                    self.pedalboard_canvas.move(key_id, 0, -3)
                    self.pedalboard_canvas.addtag_withtag('ON', key_id)

        # the keys release will be done automatically 250ms later
        self.wnd_main.after(250, lambda: self.keyboard_keys_release(list(keys_midi_notes_to_press_lst)))

    #-------------------------------------------------------------------------------------------------
    def keyboard_keys_release(self, keys_midi_nb_to_release_lst):
        # execute a release on the keys of the keyboard (manual and pedal) for the given MIDI notes
        # the given list must be a list of tuples (midi_note, midi_velocity)

        for midi_note, midi_velocity in keys_midi_nb_to_release_lst:

            key_id = mydickey(self.canvas_keys_id_dic, midi_note)
            if key_id is not None:
                # the MANUAL keyboard has a key for the current MIDI note
                key_tags_list = self.keyboard_canvas.gettags(key_id)
                if 'ON' in key_tags_list:
                    # the key is pressed
                    # restore the unpressed color
                    for tag in key_tags_list:
                        if tag == 'S0':
                            self.keyboard_canvas.itemconfig(key_id, fill='')
                        elif tag == 'S1':
                            self.keyboard_canvas.itemconfig(key_id, fill=color_key_inactive)
                        elif tag == 'S2':
                            self.keyboard_canvas.itemconfig(key_id, fill=color_key_active)
                    # move the key down
                    self.keyboard_canvas.move(key_id, 0, 3)
                    self.keyboard_canvas.dtag(key_id, 'ON')

            key_id = mydickey(self.canvas_pedals_id_dic, midi_note)
            if key_id is not None:
                # the PEDAL keyboard has a key for the current MIDI note
                key_tags_list = self.pedalboard_canvas.gettags(key_id)
                if 'ON' in key_tags_list:
                    # the key is pressed
                    # restore the unpressed color
                    for tag in key_tags_list:
                        if tag == 'S0':
                            self.pedalboard_canvas.itemconfig(key_id, fill='')
                        elif tag == 'S1':
                            self.pedalboard_canvas.itemconfig(key_id, fill=color_key_inactive)
                        elif tag == 'S2':
                            self.pedalboard_canvas.itemconfig(key_id, fill=color_key_active)
                    # move the key down
                    self.pedalboard_canvas.move(key_id, 0, 3)
                    self.pedalboard_canvas.dtag(key_id, 'ON')

    #------------------------------------------------------------------------
    def keyboard_key_click_left_evt(self, event, widget):
        # (GUI callback) the user has clicked on a keyboard canvas with the left button of the mouse

        if self.audio_samples_load_in_progress:
            return

        if widget == self.keyboard_canvas:
            keyboard_id = 'm'
        else:
            keyboard_id = 'p'

        # recover the coordinates of the mouse in the coordinates of the canvas
        x_canvas_mouse = widget.canvasx(event.x)
        y_canvas_mouse = widget.canvasy(event.y)

        # recover the ID of the item under the mouse cursor
        item_id = widget.find_overlapping(x_canvas_mouse, y_canvas_mouse, x_canvas_mouse, y_canvas_mouse)

        # recover the MIDI note of the clicked key if any
        for tag in widget.gettags(item_id):
            if tag[0] == 'M':
                midi_note = int(tag[1:])
                # raise and play the MIDI note of the clicked key
                self.keyboard_keys_press(((midi_note, default_midi_velocity),), keyboard_id)
                break

    #-------------------------------------------------------------------------------------------------
    def keyboard_trans_changed_evt(self):
        # (GUI callback) the user has changed the value of the spinbox widget to set the keyboard transposition value

        if int(self.keyboard_trans_value.get()) == 0:
            self.keyboard_trans_spn['foreground'] = 'black'
        else:
            self.keyboard_trans_spn['foreground'] = 'red'

        self.keyboard_display()

    #------------------------------------------------------------------------
    def keyboard_test_start_stop(self):
        # start/stop the keyboard test

        if not self.keyboard_test_in_progress:

            self.keyboard_test_in_progress = True
            self.widgets_status_update()

            # the execution is continued in the function self.background_thread_fct which will call keyboard_test

        else:
            self.keyboard_test_in_progress = False
            self.widgets_status_update()
            self.logs_display( '\nTest interrompu\n')

    #------------------------------------------------------------------------
    def keyboard_test(self):
        # test sequentially all the keys of the keyboard, upwards then downwards

         # get the range of the MIDI notes of the keyboard + pedalboard if any
        key_midi_note_first = min(self.manual_keys_dic.keys())
        key_midi_note_last  = max(self.manual_keys_dic.keys())
        if len(self.pedal_keys_dic) > 0:
            key_midi_note_first = min(key_midi_note_first, min(self.pedal_keys_dic.keys()))
            key_midi_note_last  = max(key_midi_note_last, max(self.pedal_keys_dic.keys()))

        # set the list of MIDI notes to play to test the keyboard
        midi_notes_to_test_lst = list(range(key_midi_note_first, key_midi_note_last + 1)) + list(range(key_midi_note_last, key_midi_note_first - 1, -1))
        midi_notes_to_test_nb = len(midi_notes_to_test_lst)

        self.playback_position_scale['from_'] = 0
        self.playback_position_scale['to'] = midi_notes_to_test_nb - 1
        self.playback_position_value.set(0)
        self.playback_position_changed = False

        midi_note_idx = 0
        while midi_note_idx < midi_notes_to_test_nb:

            midi_note = midi_notes_to_test_lst[midi_note_idx]

            if not self.playback_scale_moving:
                # update the playback position text and scale
                self.playback_position_value.set(midi_note_idx)
                if midi_note_idx < len(midi_notes_to_test_lst) / 2:
                    self.playback_position_label['text'] = f'↑ {midi_note - key_midi_note_first + 1} / {key_midi_note_last - key_midi_note_first + 1}'
                else:
                    self.playback_position_label['text'] = f'↓ {midi_note - key_midi_note_first + 1} / {key_midi_note_last - key_midi_note_first + 1}'

            self.keyboard_keys_press(((midi_note, default_midi_velocity),))

            time.sleep(0.3 / self.playback_speed_factor)

            while self.play_pause_status.get() == 1:
                time.sleep(0.1)

            if not self.keyboard_test_in_progress:
                break

            if self.playback_position_changed:
                midi_note_idx = round(self.playback_position_value.get())
                self.playback_position_changed = False
            else:
                midi_note_idx += 1

    #------------------------------------------------------------------------
    def midi_file_playback_start_stop(self):
        # play/stop of the MIDI file playback

        if not self.midi_file_playback_in_progress:
            # there is no MIDI playback in progress

            if len(self.midi_notes_to_play_lst) == 0:
                tk.messagebox.showwarning(APP_NAME, "Veuillez sélectionner un fichier MIDI valide")
                return

            if self.playback_choice.get() in (2, 3) and len(self.autoplayer_levers_to_midi_dic) == 0:
                # no autoplayer levers have been defined
                # an autoplayer programmation file has to be generated
                tk.messagebox.showwarning(APP_NAME, "Veuillez sélectionner un fichier de définition de carillon contenant une définition de jeu automatique valide")
                return

            self.midi_file_playback_in_progress = True
            self.widgets_status_update()

            # the execution is continued in the function self.background_thread_fct

        else:
            self.midi_file_playback_in_progress = False
            self.widgets_status_update()

            if self.playback_choice.get() in (1, 2):  # play on the keyboard or the autoplayer
                self.logs_display( '\nJeu interrompu\n')
            else:
                self.logs_display( '\nGénération interrompue\n')

    #-------------------------------------------------------------------------------------------------
    def midi_file_playback(self):

        playback_steps_nb = len(self.midi_notes_to_play_lst)
        playback_duration = self.midi_notes_to_play_lst[-1]['time']
        playback_mode = self.playback_choice.get()

        if playback_steps_nb == 0:
            self.logs_display( '\nIl n\'y a pas de notes à jouer\n')

        self.playback_position_scale['from_'] = 0
        self.playback_position_scale['to'] = playback_steps_nb - 1
        self.playback_position_value.set(0)
        self.playback_position_changed = False

        next_notes_time_ns = time.monotonic_ns()  # absolute time in ns at which the next notes have to be played

        playback_step_nb = 0
        while playback_step_nb < playback_steps_nb:

            playback_dtime = self.midi_notes_to_play_lst[playback_step_nb]['dtime']  # delta time vs previous notes to play
            playback_time = self.midi_notes_to_play_lst[playback_step_nb]['time']    # absolute time

            # wait until it is time to play the next notes
            next_notes_time_ns += (playback_dtime / self.playback_speed_factor) * 1000000000
            waiting_time = (next_notes_time_ns - time.monotonic_ns()) / 1000000000
            if waiting_time > 0:
                time.sleep(waiting_time)

            if not self.midi_file_playback_in_progress or not self.app_is_running:
                # the playback has to be stopped
                break

            while self.play_pause_status.get() == 1:
                # the playback is in pause, wait until it is unpaused
                time.sleep(0.1)
                next_notes_time_ns = time.monotonic_ns()

            if not self.midi_file_playback_in_progress or not self.app_is_running:
                # the playback has to be stopped
                break

            if self.playback_position_changed:
                # the user has changed the position of the playback slider
                playback_step_nb = round(self.playback_position_value.get())
                playback_time = self.midi_notes_to_play_lst[playback_step_nb]['time']
                self.playback_position_changed = False

            if playback_mode == 1:
                # play with the keyboard
                midi_notes_lst = self.midi_notes_to_play_lst[playback_step_nb]['midi_lst']
                self.keyboard_keys_press(midi_notes_lst)
            elif playback_mode == 2:
                # play with the autoplayer
                self.autoplayer_levers_raise(self.levers_nb_to_play_lst[playback_step_nb])

            if not self.playback_scale_moving:
                # update the playback position text and scale
                self.playback_position_value.set(playback_step_nb)
                self.playback_position_label['text'] = f'{playback_time / self.playback_speed_factor:0.1f} / {playback_duration / self.playback_speed_factor:0.1f} sec.'
            playback_step_nb += 1

    #------------------------------------------------------------------------
    def midi_input_message(self, msg):
        # MIDO call back : a MIDI input message is arrived

        if (msg.type == 'note_on' and msg.velocity > 0):
            self.keyboard_keys_press(((msg.note, msg.velocity + 50),))

    #------------------------------------------------------------------------
    def playback_position_changing_evt(self, scale_value):
        # (GUI callback) the user is changing the position of the playback position scale

        self.playback_scale_moving = True  # it permits to block the slider update by the playback in progress

        if self.keyboard_test_in_progress or self.autoplayer_test_in_progress:
            self.playback_position_label['text'] = f'{round(float(scale_value))} / {self.playback_position_scale.cget("to")}'

        elif self.midi_file_playback_in_progress:
            playback_step_nb = round(float(scale_value))
            self.playback_position_label['text'] = f'{self.midi_notes_to_play_lst[playback_step_nb]["time"] / self.playback_speed_factor:0.1f} / {self.midi_notes_to_play_lst[-1]["time"] / self.playback_speed_factor:0.1f} sec.'

    #------------------------------------------------------------------------
    def playback_position_changed_evt(self, event):
        # (GUI callback) the user has completed to change the position of the playback position scale

        self.playback_scale_moving = False
        self.playback_position_changed = True

    #-------------------------------------------------------------------------------------------------
    def playback_speed_changing_evt(self, scale_value):
        # (GUI callback) the user is changing the position of the playback speed scale

        self.playback_speed_label['text'] = f'Vitesse {round(float(scale_value))}%'

    #-------------------------------------------------------------------------------------------------
    def playback_speed_changed_evt(self, event):
        # (GUI callback) the user has completed to change the position of the playback speed scale

        self.playback_speed_factor = self.playback_speed_scale.get() / 100

    #-------------------------------------------------------------------------------------------------
    def audio_volume_changing(self, scale_value):
        # (GUI callback) the user is changing the position of the audio volume scale

        self.audio_volume_label['text'] = f'Volume {round(float(scale_value))}%'
        self.wav_player.audio_volume_set(float(scale_value) / 100)

    #------------------------------------------------------------------------
    def audio_record_start_stop(self):

        if self.record_wav.get():
            if not os.path.isfile(self.midi_files_cmb.get()):
                tk.messagebox.showwarning(APP_NAME, "Veuillez sélectionner un fichier MIDI, le fichier d'enregistrement sera placé dans le même répertoire")
                self.record_wav.set(0)
                return

            self.recording_file_name = os.path.dirname(__file__) + os.path.sep + 'Midillon audio.wav'
            if self.wav_player.wav_file_record(self.recording_file_name):
                self.record_wav_chkbtn.configure(fg='red')
            else:
                self.record_wav.set(0)
        else:
            self.wav_player.wav_file_record_end()
            self.record_wav_chkbtn.configure(fg='black')
            os.startfile(self.recording_file_name)

    #------------------------------------------------------------------------
    def background_thread_fct(self):
        # function permitting to execute background tasks without blocking the GUI of the application

        while self.app_is_running:
            # the application is currently running

            if len(self.midi_notes_to_play_lst) == 0:
                # there is no MIDI notes to play from a selected MIDI file
                if self.midi_files_cmb.get() != '':
                    # a MIDI file is selected
                    self.midi_notes_to_play_lst = self.midi_file.get_notes_to_play(self.midi_files_cmb.get())
                    if len(self.midi_notes_to_play_lst) == 0:
                        # failure in the MIDI file reading, clear the file selection
                        self.midi_files_cmb.set('')
                    # define the autoplayer levers to play for the notes of the MIDI file and the selected autoplayer if any
                    self.levers_nb_to_play_lst = self.auto_player.get_levers_to_play(self.autoplayer_levers_to_midi_dic, self.midi_notes_to_play_lst)

            if len(self.manual_keys_dic) == 0:
                # there is no manual defined

                # clear pedalboard and autoplayer data if they are not empty
                self.pedal_keys_dic.clear()
                self.autoplayer_levers_to_midi_dic.clear()

                if self.carillon_def_files_cmb.get() != '':
                    # a carillon definition file is selected
                    if not self.carillon_def_file_load(self.carillon_def_files_cmb.get()):
                        # failure in the carillon definition file reading, clear the file selection
                        self.carillon_def_files_cmb.set('')

                    # define the autoplayer levers to play for the notes of the MIDI file and the selected autoplayer if any
                    self.levers_nb_to_play_lst = self.auto_player.get_levers_to_play(self.autoplayer_levers_to_midi_dic, self.midi_notes_to_play_lst)

                if len(self.manual_keys_dic) == 0:
                    # no keyboard has been built when loading the carillon definition file, so build a default manual keyboard
                    for key_midi_note in range(default_keyboard_first_key_midi_note, default_keyboard_last_key_midi_note + 1):
                        self.manual_keys_dic[key_midi_note] = key_midi_note
                    self.keyboard_trans_value.set(0)
                    self.keyboard_trans_spn['foreground'] = 'black'

                # display the keyboards and the autoplayer
                self.keyboard_display()
                self.autoplayer_display()

                self.logs_display('')  # to force the display of the last log line

            if len(self.wav_player.samples_dic) == 0:
                # audio samples have not been loaded
                if self.samples_dir_cmb.get() != '':
                    # a directory with samples inside is selected, load the audio samples defined inside it if any
                    self.audio_samples_load_in_progress = True
                    self.widgets_status_update()
                    if not self.wav_player.audio_samples_load(self.samples_dir_cmb.get()):
                        self.samples_dir_cmb.set('')
                    self.audio_samples_load_in_progress = False
                    self.widgets_status_update()

                if self.samples_dir_cmb.get() == '':
                    # no audio samples have been loaded, load generated samples
                    self.audio_samples_load_in_progress = True
                    self.widgets_status_update()
                    self.wav_player.audio_samples_gen(default_keyboard_first_key_midi_note, default_keyboard_last_key_midi_note)
                    self.audio_samples_load_in_progress = False
                    self.widgets_status_update()

                # display the keyboards and the autoplayer
                self.keyboard_display()
                self.autoplayer_display()

            # MIDI file playback
            if self.midi_file_playback_in_progress:

                if self.playback_choice.get() in (1, 2):
                    # play the MIDI file notes on the keyboard or the autoplayer
                    self.midi_file_playback()
                    if self.midi_file_playback_in_progress:
                        # the playback has not been interrupted
                        self.logs_display('\nJeu terminé\n')

                elif self.playback_choice.get() == 3:
                    # generate a programming file for the autoplayer

                    prog_file_name = self.midi_files_cmb.get()[:-4] + ' - programmation jeu automatique.txt'

                    self.auto_player.prog_file_generate(self.carillon_name, prog_file_name, self.midi_files_cmb.get(),
                                                        self.midi_notes_to_play_lst, self.levers_nb_to_play_lst,
                                                        self.autoplayer_marks_nb, self.autoplayer_rev_time, self.playback_speed_factor)

                    if self.midi_file_playback_in_progress:
                        # the generation has not been interrupted
                        self.logs_display('\nGénération terminée\n')
                        # open the generated file
                        os.startfile(prog_file_name)

                self.midi_file_playback_in_progress = False
                self.widgets_status_update()

            # keyboard test
            elif self.keyboard_test_in_progress:

                self.keyboard_test()

                if self.keyboard_test_in_progress:
                    # the test has not been interrupted
                    self.logs_display("\nTest terminé\n")
                self.keyboard_test_in_progress = False
                self.widgets_status_update()

            # autoplayer test
            elif self.autoplayer_test_in_progress:

                self.autoplayer_test()

                if self.autoplayer_test_in_progress:
                    # the test has not been interrupted
                    self.logs_display("\nTest terminé\n")
                self.autoplayer_test_in_progress = False
                self.widgets_status_update()

            # wait a little before to check if there are other tasks to execute
            time.sleep(0.1)

    #-------------------------------------------------------------------------------------------------
    def logs_display(self, log_text, overwrite_last_line=False):
        # add the given log text to the logs text box widget

        if not self.app_is_running:
            return

        self.logs_text.configure(state=tk.NORMAL)

        if overwrite_last_line:
            # delete the last line before to add the given text
            self.logs_text.delete("end-1c linestart", "end-1c lineend")

        # add the given text at the end of the text box
        self.logs_text.insert('end', log_text)

        # show the start of the last line of the text
        self.logs_text.see('end linestart')

        self.logs_text.configure(state=tk.DISABLED)

        # allow the refresh of the text box content
        self.wnd_main.update_idletasks()

    #-------------------------------------------------------------------------------------------------
    def logs_clear(self):
        # (GUI event callback) the user has pressed the button "Logs clear" to clear the logs text box content

        # clear the content of the logs text box
        self.logs_text.configure(state=tk.NORMAL)
        self.logs_text.delete(1.0, 'end')
        self.logs_text.configure(state=tk.DISABLED)


# notes names
NOTES_NAMES       = ['C', 'C#',  'D', 'D#',  'E', 'F', 'F#',  'G', 'G#',  'A', 'A#',  'B']
NOTES_NAMES_FR    = ['Do', 'Do#', 'Ré', 'Ré#', 'Mi', 'Fa', 'Fa#', 'Sol', 'Sol#', 'La', 'La#', 'Si']
NOTES_NAMES_FR_UP = ['DO', 'DO#', 'RE', 'RE#', 'MI', 'FA', 'FA#', 'SOL', 'SOL#', 'LA', 'LA#', 'SI']
#------------------------------------------------------------------------
def midi_nb_to_note(midi_nb, language='eng'):
    # return in a string the note name and octave (D#5 for example) corresponding to the given MIDI note number
    # the returned note name can be in French format (if language='fra', see NOTES_NAMES_FR), else it is in English format by default (see NOTES_NAMES)

    if midi_nb not in range(0, 128):
        return ''

    note_octave = int(midi_nb // 12) - 1   # -1 to have MIDI note number 69 = note A4 and not A5
    if language == 'fra':
        note_name = NOTES_NAMES_FR[midi_nb % 12]
    else:
        note_name = NOTES_NAMES[midi_nb % 12]

    return note_name + str(note_octave)

#------------------------------------------------------------------------
def midi_nb_to_note_split(midi_nb, language='eng'):
    # return in a string the note name and octave (D#5 for example) corresponding to the given MIDI note number
    # the returned note name can be in French format (if language='fra', see NOTES_NAMES_FR), else it is in English format by default (see NOTES_NAMES)

    if midi_nb not in range(0, 128):
        return ''

    note_octave = int(midi_nb // 12) - 1   # -1 to have MIDI note number 69 = note A4 and not A5
    if language == 'fra':
        note_name = NOTES_NAMES_FR[midi_nb % 12]
    else:
        note_name = NOTES_NAMES[midi_nb % 12]

    if '#' in note_name:
        sharp = '#'
        note_name = note_name.replace('#', '')
    else:
        sharp = ''

    return (note_name, sharp, note_octave)

#------------------------------------------------------------------------
def note_to_midi_nb(note_name):
    # return the MIDI note number corresponding to the note name found in the given string if any (for example A5, La5, G#6, Dsharp3, Sol#6, Bb3, Réb5)
    # return None if no note name has been found

    note_nam = note_name.upper().replace('É', 'E')

    rs = re.search(r"(A|B|C|D|E|F|G|DO|RE|MI|FA|SOL|LA|SI)(#|B|SHARP|)(\d)(#|B|SHARP|)", note_nam)

    if rs is None:
        # nothing found
        return None

    note_nam = rs.groups()[0]
    if note_nam == '':
        return None

    if note_nam in NOTES_NAMES:
        note_idx = NOTES_NAMES.index(note_nam)
    elif note_nam in NOTES_NAMES_FR_UP:
        note_idx = NOTES_NAMES_FR_UP.index(note_nam)
    else:
        return None

    note_alt = (rs.groups()[1] if rs.groups()[1] != '' else rs.groups()[3])
    if note_alt in ('#', 'SHARP'):
        note_idx += 1
        if note_idx == 12:
            note_idx = 0
    elif note_alt == 'B':
        note_idx -= 1
        if note_idx == -1:
            note_idx = 11

    note_oct = rs.groups()[2]
    if note_oct == '':
        return None

    midi_nb = note_idx + (12 * (int(note_oct) + 1))   # +1 to have note A4 = MIDI number 69 and not 57

    return midi_nb

#------------------------------------------------------------------------
def midi_nb_to_freq(midi_nb, a4_frequency=440.0):
    # return the frequency (float in Hz) corresponding to the given MIDI number
    # based on the given reference frequency of the A4 note (MIDI number 69), set at 440Hz by default if not provided
    return a4_frequency * math.pow(2, (midi_nb - 69) / 12)

#-------------------------------------------------------------------------------------------------
def mydickey(dic, key, default_val=None):
    # return the value corresponding to the given key in the given dic if it exists, else returns the provided default value or None if not defined

    try:
        return dic[key]
    except Exception:
        return default_val

#------------------------------------------------------------------------
def main():
    # main function of the application

    C_APP().wnd_main_build().mainloop()
    return

#------------------------------------------------------------------------
# first line of code executed at the launch of the script
# if we are in the main execution environment, call the main function of the application
if __name__ == '__main__':
    main()
