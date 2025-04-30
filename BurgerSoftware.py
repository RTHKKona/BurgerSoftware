#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# MT Framework ARC Tool (Python)
# Prerequisites: crcmod
# Install using: python -m pip install crcmod

import struct
import zlib
import io
import os
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from enum import Enum
from pathlib import Path
import inspect # Might be needed for future TypeReader/Writer
import time
import traceback # For logging detailed errors
from collections import defaultdict # For folder tree
import math # For hex editor rows

# --- Dependencies ---
try:
    import crcmod
    _crcmod_available = True
except ImportError:
    _crcmod_available = False
    print("*" * 60)
    print("Error: crcmod library not found.")
    print("CRC32 hash calculation for extensions will not work.")
    print("Please install it: python -m pip install crcmod")
    print("*" * 60)
    # Define dummy functions to prevent immediate crash if GUI is run
    def get_hash(input_string, encoding='utf-8'):
        print("CRCMOD not found, cannot calculate hash!")
        return 0
    # Optionally: sys.exit(1) if crcmod is absolutely essential to run

# --- Color Scheme ---
BG_COLOR = '#2b2b2b'
TEXT_COLOR = '#ffebcd'        # Blanched Almond - Main text
WIDGET_BG = '#3c3f41'        # Darker Gray - Treeview/Text/Hex background
INPUT_BG = '#45494a'         # Slightly lighter gray - Entry background
BUTTON_BG = '#4d4d4d'        # Medium Gray - Button Background
BUTTON_FG = TEXT_COLOR       # Text on buttons
BUTTON_ACTIVE_BG = '#636363' # Darker Gray - Button when pressed/active
BUTTON_BORDER = '#202020'    # Dark border for buttons
HEADER_BG = '#4d4d4d'        # Medium Gray - Treeview Header BG
HEADER_FG = TEXT_COLOR       # Text on headers
HIGHLIGHT_BG = '#556b7d'    # Steel Blue-ish Gray - Selection background
HIGHLIGHT_FG = '#ffffff'    # White - Selected text color
STATUS_BAR_BG = '#252526'   # Very Dark Gray - Status bar background
SASH_COLOR = '#45494a'      # Color for the paned window sash (Note: may not apply directly to tk.PanedWindow sash)
HEX_ADDR_FG = '#a9b7c6'     # Lighter gray for hex addresses
HEX_NULL_FG = '#606060'     # Darker gray for null bytes in hex view
ASCII_NONPRINT_FG = '#606060'# Darker gray for non-printable chars in ASCII view

# --- Constants and Enums ---
# ... (ByteOrder, BitOrder, MtArcPlatform - unchanged) ...
class ByteOrder(Enum): LittleEndian = 0; BigEndian = 1
class BitOrder(Enum): Default = 0; LeastSignificantBitFirst = 1; MostSignificantBitFirst = 2; LowestAddressFirst = 3; HighestAddressFirst = 4
class MtArcPlatform(Enum): LittleEndian = 0; Switch = 1; BigEndian = 2

FILENAME_ENCODING = 'shift_jis'

# --- CRC32 Calculation ---
# ... (CRC32 functions - unchanged) ...
_crc32_func = None
if _crcmod_available:
    try:
        _crc32_func = crcmod.mkCrcFun(0x104C11DB7, initCrc=0xFFFFFFFF, rev=True, xorOut=0x00000000)
        def calculate_mt_crc32_intermediate(data_bytes):
            if not _crc32_func: raise RuntimeError("crcmod func not initialized")
            return _crc32_func(data_bytes)
        def get_hash(input_string, encoding=FILENAME_ENCODING):
            if not _crc32_func: raise RuntimeError("crcmod func not initialized")
            try: input_bytes = input_string.encode(encoding, errors='replace'); crc_val = calculate_mt_crc32_intermediate(input_bytes); return (~crc_val) & 0xFFFFFFFF
            except Exception as e: print(f"Hash error for '{input_string}': {e}"); raise
    except Exception as e: print(f"CRCmod init error: {e}"); _crcmod_available = False
if not _crcmod_available:
    def get_hash(input_string, encoding='utf-8'): print("CRCMOD unavailable!"); return 0

# --- Extension Map ---
# ... (Extension map generation - unchanged) ...
print("Calculating extension map hashes...")
EXTENSION_MAP_HASH_TO_EXT = {}
EXTENSION_MAP_EXT_TO_HASH = {}
_EXTENSION_MAP_RAW = { # Keep concise for brevity
    "rTexture": ".tex", "rGUIMessage": ".gmd", "rModel": ".mod", "rMaterial": ".mrl", "rScheduler": ".sdl", "rMotionList": ".lmt", "rEffectAnim": ".ean",
    0x241F5DEB: ".tex", 0x242BB29A: ".gmd", 0x2749C8A8: ".mrl", 0x58A15856: ".mod", 0x73850D05: ".arc", # Add ALL others...
}
if _crcmod_available:
    for k, v in _EXTENSION_MAP_RAW.items():
        hash_val = 0
        if isinstance(k, str):
            try: hash_val = get_hash(k)
            except Exception: pass
        elif isinstance(k, int): hash_val = k
        if hash_val != 0: EXTENSION_MAP_HASH_TO_EXT[hash_val] = v;
        if v not in EXTENSION_MAP_EXT_TO_HASH: EXTENSION_MAP_EXT_TO_HASH[v] = hash_val
else: print("Skipping string-based extension map"); [ (EXTENSION_MAP_HASH_TO_EXT.update({k:v}), EXTENSION_MAP_EXT_TO_HASH.setdefault(v,k)) for k, v in _EXTENSION_MAP_RAW.items() if isinstance(k, int) ]
print(f"Gen {len(EXTENSION_MAP_HASH_TO_EXT)} hash->ext, {len(EXTENSION_MAP_EXT_TO_HASH)} ext->hash")
def determine_extension(h): return EXTENSION_MAP_HASH_TO_EXT.get(h, f".{h:08X}")
def determine_extension_hash(e):
    if not e.startswith('.'): e = '.' + e; h = EXTENSION_MAP_EXT_TO_HASH.get(e)
    if h is not None: return h
    if len(e) == 9:
        try: return int(e[1:], 16)
        except ValueError: pass
    if not _crcmod_available: raise ValueError(f"Ext '{e}' map failed (crcmod missing).")
    else: raise ValueError(f"Ext '{e}' cannot be mapped.")

# --- IO Classes ---
# ... (BinaryReaderXPy, BinaryWriterXPy - unchanged) ...
class BinaryReaderXPy:
    def __init__(self, stream, byte_order=ByteOrder.LittleEndian, encoding=FILENAME_ENCODING): self.base_stream = stream; self.byte_order = byte_order; self._encoding_default = encoding; self._fmt_prefix = '<' if byte_order == ByteOrder.LittleEndian else '>'
    def close(self):
        if self.base_stream and not self.base_stream.closed: self.base_stream.close()
        self.base_stream = None
    def seek(self, offset, whence=io.SEEK_SET):
        if not self.base_stream or self.base_stream.closed: raise ValueError("Stream is closed")
        return self.base_stream.seek(offset, whence)
    def tell(self):
        if not self.base_stream or self.base_stream.closed: raise ValueError("Stream is closed")
        return self.base_stream.tell()
    def read_bytes(self, count):
        if not self.base_stream or self.base_stream.closed: raise ValueError("Stream is closed")
        data = self.base_stream.read(count)
        if len(data) != count: raise EOFError(f"Could not read {count} bytes (got {len(data)}).")
        return data
    def read_byte(self): return self.read_bytes(1)[0]
    def read_sbyte(self): return struct.unpack(self._fmt_prefix + 'b', self.read_bytes(1))[0]
    def read_int16(self): return struct.unpack(self._fmt_prefix + 'h', self.read_bytes(2))[0]
    def read_uint16(self): return struct.unpack(self._fmt_prefix + 'H', self.read_bytes(2))[0]
    def read_int32(self): return struct.unpack(self._fmt_prefix + 'i', self.read_bytes(4))[0]
    def read_uint32(self): return struct.unpack(self._fmt_prefix + 'I', self.read_bytes(4))[0]
    def read_int64(self): return struct.unpack(self._fmt_prefix + 'q', self.read_bytes(8))[0]
    def read_uint64(self): return struct.unpack(self._fmt_prefix + 'Q', self.read_bytes(8))[0]
    def read_float(self): return struct.unpack(self._fmt_prefix + 'f', self.read_bytes(4))[0]
    def read_double(self): return struct.unpack(self._fmt_prefix + 'd', self.read_bytes(8))[0]
    def read_string(self, length=-1, encoding=None):
        enc = encoding if encoding is not None else self._encoding_default
        try:
            if length == -1: byte_list = [];
            else: raw_bytes = self.read_bytes(length); null_pos = raw_bytes.find(b'\0'); raw_bytes = raw_bytes[:null_pos] if null_pos != -1 else raw_bytes
            return raw_bytes.decode(enc, errors='replace')
        except Exception as e: print(f"[WARN] Decode failed {enc}: {raw_bytes!r}. {e}"); return raw_bytes.decode('ascii', errors='replace')
    def peek_bytes(self, count, offset=0):
         if not self.base_stream or self.base_stream.closed: raise ValueError("Stream is closed")
         current_pos = self.tell(); target_pos = current_pos + offset
         try: self.seek(target_pos); data = self.base_stream.read(count);
         finally: self.seek(current_pos)
         if len(data) != count: raise EOFError(f"Peek failed {count} bytes (got {len(data)}).")
         return data
    def peek_string(self, length=4, offset=0, encoding=None):
         try: raw_bytes = self.peek_bytes(length, offset); enc = encoding if encoding is not None else self._encoding_default; null_pos = raw_bytes.find(b'\0'); raw_bytes = raw_bytes[:null_pos] if null_pos != -1 else raw_bytes; return raw_bytes.decode(enc, errors='replace')
         except EOFError: return ""
         except Exception as e: print(f"[WARN] Peek decode failed {encoding or self._encoding_default}: {raw_bytes!r}. {e}"); return raw_bytes.decode('ascii', errors='replace')
    def reset_bit_buffer(self): pass
    def read_bits(self, count): raise NotImplementedError("Bit reading not implemented yet.")
    def read_bit(self): raise NotImplementedError("Bit reading not implemented yet.")

class BinaryWriterXPy:
    def __init__(self, stream, byte_order=ByteOrder.LittleEndian, encoding=FILENAME_ENCODING): self.base_stream = stream; self.byte_order = byte_order; self._encoding_default = encoding; self._fmt_prefix = '<' if byte_order == ByteOrder.LittleEndian else '>'
    def close(self):
        if self.base_stream and not self.base_stream.closed: self.base_stream.close()
        self.base_stream = None
    def seek(self, offset, whence=io.SEEK_SET):
        if not self.base_stream or self.base_stream.closed: raise ValueError("Stream is closed")
        return self.base_stream.seek(offset, whence)
    def tell(self):
        if not self.base_stream or self.base_stream.closed: raise ValueError("Stream is closed")
        return self.base_stream.tell()
    def write_bytes(self, data):
        if not self.base_stream or self.base_stream.closed: raise ValueError("Stream is closed")
        self.base_stream.write(data)
    def write_byte(self, value): self.write_bytes(struct.pack(self._fmt_prefix + 'B', value))
    def write_sbyte(self, value): self.write_bytes(struct.pack(self._fmt_prefix + 'b', value))
    def write_int16(self, value): self.write_bytes(struct.pack(self._fmt_prefix + 'h', value))
    def write_uint16(self, value): self.write_bytes(struct.pack(self._fmt_prefix + 'H', value))
    def write_int32(self, value): self.write_bytes(struct.pack(self._fmt_prefix + 'i', value))
    def write_uint32(self, value): self.write_bytes(struct.pack(self._fmt_prefix + 'I', value))
    def write_int64(self, value): self.write_bytes(struct.pack(self._fmt_prefix + 'q', value))
    def write_uint64(self, value): self.write_bytes(struct.pack(self._fmt_prefix + 'Q', value))
    def write_float(self, value): self.write_bytes(struct.pack(self._fmt_prefix + 'f', value))
    def write_double(self, value): self.write_bytes(struct.pack(self._fmt_prefix + 'd', value))
    def write_string(self, value, length=-1, encoding=None, pad_byte=b'\0'):
        enc = encoding if encoding is not None else self._encoding_default
        try: encoded_bytes = value.encode(enc, errors='replace')
        except Exception as e: print(f"[WARN] Encode failed {enc}: {e}"); encoded_bytes = value.encode('ascii', errors='replace')
        if length == -1: self.write_bytes(encoded_bytes + b'\0')
        else:
             if len(encoded_bytes) > length: truncated_bytes = encoded_bytes[:length]; print(f"[WARN] String '{value}' truncated to {length} bytes."); self.write_bytes(truncated_bytes)
             else: padded_bytes = encoded_bytes.ljust(length, pad_byte); self.write_bytes(padded_bytes)
    def write_padding(self, count, pad_byte=0x00):
        if count > 0: self.write_bytes(bytes([pad_byte] * count))
    def write_alignment(self, alignment=16, pad_byte=0x00):
        current_pos = self.tell(); remainder = current_pos % alignment
        if remainder > 0: bytes_to_write = alignment - remainder; self.write_padding(bytes_to_write, pad_byte)
    def flush(self): pass
    def write_bits(self, value, count): raise NotImplementedError("Bit writing not implemented yet.")
    def write_bit(self, value): raise NotImplementedError("Bit writing not implemented yet.")

# --- Data Structures ---
# ... (MtHeaderPy, IMtEntryPy, BaseMtEntryPy, MtEntryPy, MtEntryExtendedNamePy, MtEntrySwitchPy - unchanged) ...
class MtHeaderPy:
    STRUCT_FORMAT_LE = "<4shh"; STRUCT_FORMAT_BE = ">4shh"; SIZE = 8
    def __init__(self, magic=b'ARC\0', version=7, entry_count=0): self.magic = magic; self.version = version; self.entry_count = entry_count
    @classmethod
    def from_bytes(cls, data, platform):
        fmt = cls.STRUCT_FORMAT_BE if platform == MtArcPlatform.BigEndian else cls.STRUCT_FORMAT_LE
        try: magic_bytes, version, entry_count = struct.unpack(fmt, data)
        except struct.error as e: raise IOError(f"Failed unpack MtHeader: {e}")
        expected_magic = b'\0CRA' if platform == MtArcPlatform.BigEndian else b'ARC\0'
        if magic_bytes != expected_magic: print(f"[WARN] Header magic mismatch! Expected {expected_magic!r}, got {magic_bytes!r} for platform {platform}.")
        return cls(magic_bytes, version, entry_count)
    def to_bytes(self, platform):
        fmt = self.STRUCT_FORMAT_BE if platform == MtArcPlatform.BigEndian else self.STRUCT_FORMAT_LE
        magic_to_write = b'\0CRA' if platform == MtArcPlatform.BigEndian else b'ARC\0'
        try: entry_count_s16 = max(-32768, min(self.entry_count, 32767)); return struct.pack(fmt, magic_to_write, self.version, entry_count_s16)
        except struct.error as e: raise IOError(f"Failed pack MtHeader: {e}")
class IMtEntryPy:
    def get_full_name(self) -> str: raise NotImplementedError
    def set_full_name(self, full_path_str): raise NotImplementedError
    def get_decompressed_size(self, platform: MtArcPlatform) -> int: raise NotImplementedError
    def set_decompressed_size(self, size: int, platform: MtArcPlatform): raise NotImplementedError
    def to_bytes(self, platform: MtArcPlatform, encoding: str) -> bytes: raise NotImplementedError
class BaseMtEntryPy(IMtEntryPy):
    def __init__(self, file_name="", ext_hash=0, comp_size=0, decomp_size_raw=0, offset=0): self.file_name_str=file_name; self.extension_hash=ext_hash&0xFFFFFFFF; self.comp_size=comp_size; self._decomp_size_raw=decomp_size_raw; self.offset=offset; self.is_dirty=False; self.data_to_write=None
    def get_full_name(self):
        try: return self.file_name_str + determine_extension(self.extension_hash)
        except Exception as e: print(f"[ERROR] Failed get name for {self.extension_hash:#08X}: {e}"); return self.file_name_str + f".{self.extension_hash:08X}"
    def set_full_name(self, full_path_str):
        p=Path(full_path_str); ext=p.suffix
        try: self.extension_hash=determine_extension_hash(ext)&0xFFFFFFFF; self.file_name_str=str(p.with_suffix(''))
        except ValueError as e: print(f"[ERROR] set name '{full_path_str}': {e}.")
    def get_decompressed_size(self, platform):
        try: size_raw=int(self._decomp_size_raw);
        except (TypeError, ValueError): print(f"[WARN] Bad decomp value: {self._decomp_size_raw}"); return 0
        if platform == MtArcPlatform.LittleEndian: return size_raw & 0x00FFFFFF
        elif platform == MtArcPlatform.BigEndian: return (size_raw & 0xFFFFFFFF) >> 3
        else: return size_raw
    def set_decompressed_size(self, size, platform):
         try: current_flags_raw=self._decomp_size_raw; current_flags=int(current_flags_raw) if isinstance(current_flags_raw,int) else 0; target_size=max(0,int(size));
         except (TypeError, ValueError) as e: print(f"[WARN] Failed set decomp size ({size=},{self._decomp_size_raw=}): {e}"); self._decomp_size_raw=size; return
         if platform == MtArcPlatform.LittleEndian: self._decomp_size_raw=(current_flags&0xFF000000)|(target_size&0x00FFFFFF)
         elif platform == MtArcPlatform.BigEndian: self._decomp_size_raw=(current_flags&0x00000007)|((target_size<<3)&0xFFFFFFF8)
         else: self._decomp_size_raw=target_size
    def to_bytes(self, platform, encoding): raise NotImplementedError
    def _pack_int32(self, value): return max(-2147483648, min(int(value), 2147483647))
class MtEntryPy(BaseMtEntryPy):
    FILENAME_LEN=64; STRUCT_FORMAT_LE=f"< {FILENAME_LEN}s I i i i"; STRUCT_FORMAT_BE=f"> {FILENAME_LEN}s I i i i"; SIZE=80
    @classmethod
    def from_bytes(cls, data, platform, encoding=FILENAME_ENCODING):
        fmt=cls.STRUCT_FORMAT_BE if platform==MtArcPlatform.BigEndian else cls.STRUCT_FORMAT_LE;
        try: name_bytes, ext_hash, comp_size, decomp_size_raw, offset=struct.unpack(fmt,data)
        except struct.error as e: raise IOError(f"Unpack MtEntryPy failed: {e}")
        try: file_name=name_bytes.decode(encoding,errors='replace').partition('\0')[0]
        except Exception as e: print(f"[WARN] Decode filename failed: {e}"); file_name=name_bytes.partition(b'\0')[0].decode('ascii',errors='replace')
        return cls(file_name, ext_hash, comp_size, decomp_size_raw, offset)
    def to_bytes(self, platform, encoding=FILENAME_ENCODING):
        fmt=self.STRUCT_FORMAT_BE if platform==MtArcPlatform.BigEndian else self.STRUCT_FORMAT_LE;
        try: name_bytes=self.file_name_str.encode(encoding,errors='replace')
        except Exception as e: print(f"[WARN] Encode filename failed: {e}"); name_bytes=self.file_name_str.encode('ascii',errors='replace')
        padded_name=name_bytes.ljust(self.FILENAME_LEN,b'\0')[:self.FILENAME_LEN];
        try: return struct.pack(fmt,padded_name, self.extension_hash, self._pack_int32(self.comp_size), self._pack_int32(self._decomp_size_raw), self._pack_int32(self.offset))
        except Exception as e: raise IOError(f"Pack MtEntryPy failed for {self.get_full_name()}: {e}")
class MtEntryExtendedNamePy(MtEntryPy): FILENAME_LEN=128; STRUCT_FORMAT_LE=f"< {FILENAME_LEN}s I i i i"; STRUCT_FORMAT_BE=f"> {FILENAME_LEN}s I i i i"; SIZE=144
class MtEntrySwitchPy(BaseMtEntryPy):
    FILENAME_LEN=64; STRUCT_FORMAT_LE=f"< {FILENAME_LEN}s I i i i i"; SIZE=84
    def __init__(self, file_name="", ext_hash=0, comp_size=0, decomp_size_raw=0, offset=0, unk1=0): super().__init__(file_name, ext_hash, comp_size, decomp_size_raw, offset); self.unk1=unk1
    @classmethod
    def from_bytes(cls, data, platform, encoding=FILENAME_ENCODING):
        if platform!=MtArcPlatform.Switch: print("[WARN] Reading Switch entry on non-Switch.")
        fmt=cls.STRUCT_FORMAT_LE;
        try: name_bytes, ext_hash, comp_size, decomp_size_raw, unk1, offset=struct.unpack(fmt,data)
        except struct.error as e: raise IOError(f"Unpack MtEntrySwitchPy failed: {e}")
        try: file_name=name_bytes.decode(encoding,errors='replace').partition('\0')[0]
        except Exception as e: print(f"[WARN] Decode filename failed: {e}"); file_name=name_bytes.partition(b'\0')[0].decode('ascii',errors='replace')
        return cls(file_name, ext_hash, comp_size, decomp_size_raw, offset, unk1)
    def to_bytes(self, platform, encoding=FILENAME_ENCODING):
         fmt=self.STRUCT_FORMAT_LE;
         try: name_bytes=self.file_name_str.encode(encoding,errors='replace')
         except Exception as e: print(f"[WARN] Encode filename failed: {e}"); name_bytes=self.file_name_str.encode('ascii',errors='replace')
         padded_name=name_bytes.ljust(self.FILENAME_LEN,b'\0')[:self.FILENAME_LEN];
         try: return struct.pack(fmt,padded_name, self.extension_hash, self._pack_int32(self.comp_size), self._pack_int32(self._decomp_size_raw), self._pack_int32(self.unk1), self._pack_int32(self.offset))
         except Exception as e: raise IOError(f"Pack MtEntrySwitchPy failed for {self.get_full_name()}: {e}")

# --- Core ARC Logic ---
# ... (MtArc class - unchanged from previous version) ...
class MtArc:
    def __init__(self):
        self.header = MtHeaderPy(); self.entries: list[IMtEntryPy] = []; self.platform = MtArcPlatform.LittleEndian
        self.file_handle = None; self._is_extended_name = False; self._is_extended_header = False
        self.encoding = FILENAME_ENCODING; self.source_filepath = None; self._log_callback = print
    def set_logger(self, log_func): self._log_callback = log_func
    def log(self, message, level="INFO"):
        if self._log_callback: self._log_callback(f"[MtArc] {message}", level)
        else: print(f"[MtArc] {level}: {message}")
    def determine_platform(self, stream):
        initial_pos = stream.tell()
        try:
            header_bytes = stream.read(MtHeaderPy.SIZE)
            if len(header_bytes) < MtHeaderPy.SIZE: raise IOError("File too small for header.")
            try: magic_le, version_le, _ = struct.unpack(MtHeaderPy.STRUCT_FORMAT_LE, header_bytes)
            except struct.error: magic_le, version_le = None, None
            try: magic_be, _, _ = struct.unpack(MtHeaderPy.STRUCT_FORMAT_BE, header_bytes)
            except struct.error: magic_be = None
            if magic_le == b'ARC\0': return MtArcPlatform.Switch if version_le == 9 else MtArcPlatform.LittleEndian
            if magic_be == b'\0CRA': return MtArcPlatform.BigEndian
            raise ValueError("Unknown ARC format or invalid header.")
        finally: stream.seek(initial_pos)
    def _measure_type(self, cls):
        if hasattr(cls, 'SIZE'): return cls.SIZE
        raise NotImplementedError(f"Cannot measure size of type {cls.__name__}")
    def load(self, filepath):
        self.close(); self.source_filepath = Path(filepath); self.entries = []; self._is_extended_name = False; self._is_extended_header = False
        self.log(f"Loading ARC: {filepath}"); temp_reader = None
        try:
             f = open(filepath, 'rb'); self.file_handle = f; temp_reader = BinaryReaderXPy(self.file_handle)
             self.platform = self.determine_platform(self.file_handle)
             temp_reader.byte_order = ByteOrder.BigEndian if self.platform == MtArcPlatform.BigEndian else ByteOrder.LittleEndian
             self.log(f"Platform: {self.platform}, Byte Order: {temp_reader.byte_order}")
             self.header = MtHeaderPy.from_bytes(temp_reader.read_bytes(MtHeaderPy.SIZE), self.platform)
             self.log(f"Header: Ver={self.header.version:#0X}, Count={self.header.entry_count}")
             entry_offset = MtHeaderPy.SIZE; self._is_extended_header = (self.platform == MtArcPlatform.LittleEndian and self.header.version not in [7, 8])
             if self._is_extended_header: temp_reader.read_int32(); entry_offset += 4; self.log("Extended Header")
             EntryClass = MtEntryPy
             if self.platform == MtArcPlatform.Switch: EntryClass = MtEntrySwitchPy; self.log("Switch Entry")
             elif self.platform == MtArcPlatform.LittleEndian:
                 if self.header.entry_count > 0:
                     try:
                         first_entry_bytes = temp_reader.peek_bytes(MtEntryPy.SIZE, offset=0)
                         peek_entry = MtEntryPy.from_bytes(first_entry_bytes, self.platform, self.encoding)
                         peek_decomp_size = peek_entry.get_decompressed_size(self.platform)
                         if peek_entry.extension_hash == 0 or peek_decomp_size == 0 or peek_entry.offset == 0: self._is_extended_name = True; EntryClass = MtEntryExtendedNamePy; self.log("Extended Names")
                         else: self.log("Standard Names")
                     except Exception as e: self.log(f"Peek failed: {e}. Assuming standard.", "WARN")
             else: self.log("Standard Entry")
             entry_struct_size = self._measure_type(EntryClass)
             self.log(f"Reading {self.header.entry_count} entries (Size: {entry_struct_size})...")
             for i in range(self.header.entry_count):
                 try: entry = EntryClass.from_bytes(temp_reader.read_bytes(entry_struct_size), self.platform, self.encoding); self.entries.append(entry)
                 except EOFError: self.log(f"EOF reading entry {i+1}.", "WARN"); break
                 except Exception as e: self.log(f"Error reading entry {i+1}: {e}", "ERROR"); break
             self.log(f"Loaded {len(self.entries)} entries.")
             temp_reader.base_stream = None
        except FileNotFoundError: self.log(f"File not found: {filepath}", "ERROR"); self.close(); raise
        except Exception as e: self.log(f"Loading failed: {e}\n{traceback.format_exc()}", "ERROR"); self.close(); raise
        finally:
            if temp_reader and temp_reader.base_stream: temp_reader.close()
    def _determine_file_offset(self, entry_count, entry_size):
        entry_offset = MtHeaderPy.SIZE; header_size = entry_offset
        if self._is_extended_header: entry_offset += 4; header_size += 4
        entry_table_size = entry_size * entry_count; end_of_entries = header_size + entry_table_size
        v = self.header.version; order = 'big' if self.platform == MtArcPlatform.BigEndian else 'little'; alignment = 0
        if v in [0x4, 0x7, 0x8, 0x10] and order == 'little': alignment = 0x8000
        elif v == 0x9: alignment = 0x8000
        elif v == 0x11 and order == 'little': alignment = 0x100
        if alignment > 0: mask = ~(alignment - 1); return (end_of_entries + alignment - 1) & mask
        else: return end_of_entries
    def get_entry_data(self, entry: IMtEntryPy, compressed=False) -> bytes | None:
        if entry.data_to_write is not None:
            raw_data = entry.data_to_write
            if compressed:
                 if self.platform == MtArcPlatform.Switch and raw_data:
                      try: return zlib.compress(raw_data, level=9)
                      except Exception as e: self.log(f"Zlib comp failed for replaced {entry.get_full_name()}: {e}", "ERROR"); return raw_data
                 else: return raw_data
            else: return raw_data
        elif self.file_handle and not self.file_handle.closed and entry.offset >= 0 and entry.comp_size >= 0:
            try: self.file_handle.seek(entry.offset); comp_data = self.file_handle.read(entry.comp_size);
            except Exception as e: self.log(f"Read error for {entry.get_full_name()}: {e}", "ERROR"); return None
            if len(comp_data) != entry.comp_size: self.log(f"Read incomplete {entry.get_full_name()}.", "WARN"); return None
            decomp_size = entry.get_decompressed_size(self.platform); is_zlib_compressed = False
            if entry.comp_size == 0: is_zlib_compressed = False
            elif self.platform == MtArcPlatform.Switch: is_zlib_compressed = True
            elif entry.comp_size != decomp_size:
                 if entry.comp_size >= 2: cmf_flg = struct.unpack('>H', comp_data[:2])[0]; is_zlib_compressed = ((cmf_flg & 0x0F00) >> 8 == 0x08)
                 else: self.log(f"Size mismatch, data too small {entry.comp_size}: {entry.get_full_name()}", "WARN"); is_zlib_compressed = True
                 if is_zlib_compressed and not ((cmf_flg & 0x0F00) >> 8 == 0x08): self.log(f"Size mismatch but header {cmf_flg:#04X} not Zlib: {entry.get_full_name()}", "WARN"); is_zlib_compressed = False
            if is_zlib_compressed:
                if compressed: return comp_data
                try: raw_data = zlib.decompress(comp_data);
                except zlib.error as e: self.log(f"Zlib decompress failed {entry.get_full_name()}: {e}. Returning compressed.", "ERROR"); return comp_data
                if len(raw_data) != decomp_size: self.log(f"Decomp size mismatch {entry.get_full_name()}. Expected {decomp_size}, got {len(raw_data)}.", "WARN")
                return raw_data
            else: return comp_data
        else: self.log(f"No data source for {entry.get_full_name()}", "WARN"); return b''
    def save(self, filepath):
        if not self.entries and not (self.header and self.header.magic): raise ValueError("No data to save.")
        if self.file_handle and not self.file_handle.closed: self.log("Closing loaded file before saving.", "DEBUG"); self.close()
        filepath = Path(filepath); self.log(f"Saving: {filepath}")
        EntryClass = MtEntryPy;
        if self.platform == MtArcPlatform.Switch: EntryClass = MtEntrySwitchPy
        elif self._is_extended_name: EntryClass = MtEntryExtendedNamePy
        entry_size = self._measure_type(EntryClass); current_entry_count = len(self.entries)
        self.header.entry_count = current_entry_count; current_file_offset = self._determine_file_offset(current_entry_count, entry_size)
        self.log(f"Platform: {self.platform}, Ver: {self.header.version:#0X}, Count: {current_entry_count}, Entry: {EntryClass.__name__}, Data Offset: {current_file_offset:#0X}")
        temp_file_path = filepath.with_suffix(filepath.suffix + ".~tmp"); saved_entries_meta = []
        try:
            with open(temp_file_path, 'wb') as f:
                writer = BinaryWriterXPy(f, self.header.magic == b'\0CRA' and ByteOrder.BigEndian or ByteOrder.LittleEndian, self.encoding)
                entry_table_start = MtHeaderPy.SIZE + (4 if self._is_extended_header else 0); entry_table_size = entry_size * current_entry_count
                writer.write_padding(entry_table_start + entry_table_size); writer.write_alignment(current_file_offset)
                if writer.tell() != current_file_offset: self.log(f"Pos {writer.tell()} != offset {current_file_offset} after align! Seeking.", "WARN"); writer.seek(current_file_offset)
                self.log(f"Writing data at {writer.tell():#0X}"); total_data_written = 0
                for i, entry in enumerate(self.entries):
                    if not isinstance(entry, EntryClass): self.log(f"Entry {i} type mismatch. Skipping.", "ERROR"); continue
                    entry_start_offset = writer.tell(); raw_data = self.get_entry_data(entry, compressed=False)
                    if raw_data is None: self.log(f"Skipping save {entry.get_full_name()} (read error).", "ERROR"); entry.offset=-1; entry.comp_size=0; entry.set_decompressed_size(0, self.platform); saved_entries_meta.append(entry); continue
                    data_to_write = raw_data
                    try:
                         if self.platform == MtArcPlatform.Switch and raw_data: data_to_write = zlib.compress(raw_data, level=9)
                         elif not entry.is_dirty and entry.comp_size != entry.get_decompressed_size(self.platform) and raw_data: data_to_write = zlib.compress(raw_data, level=9)
                    except Exception as comp_err: self.log(f"Comp failed {entry.get_full_name()}: {comp_err}. Writing raw.", "WARN"); data_to_write = raw_data
                    writer.write_bytes(data_to_write); entry.offset = entry_start_offset; entry.comp_size = len(data_to_write)
                    entry.set_decompressed_size(len(raw_data), self.platform); entry.is_dirty = False; saved_entries_meta.append(entry); total_data_written += entry.comp_size
                    # writer.write_alignment(4) # Optional padding between files
                self.log(f"Data written: {total_data_written} bytes. Final Pos: {writer.tell():#X}")
                writer.seek(0); writer.write_bytes(self.header.to_bytes(self.platform))
                if self._is_extended_header: writer.write_int32(0)
                writer.seek(entry_table_start); self.log(f"Writing entry table at {entry_table_start:#X}")
                if len(saved_entries_meta) != current_entry_count: self.log(f"Meta count {len(saved_entries_meta)} != header count {current_entry_count}!", "FATAL")
                for entry_meta in saved_entries_meta:
                    try: writer.write_bytes(entry_meta.to_bytes(self.platform, self.encoding))
                    except Exception as entry_write_err: self.log(f"Error writing entry meta {entry_meta.get_full_name()}: {entry_write_err}", "FATAL"); raise
                if writer.tell() != entry_table_start + entry_table_size: self.log(f"Entry table pos mismatch {writer.tell():#X} vs {entry_table_start + entry_table_size:#X}", "WARN")
            os.replace(temp_file_path, filepath); self.log(f"Saved: {filepath}"); self.source_filepath = filepath
        except Exception as e:
            self.log(f"Save failed: {e}\n{traceback.format_exc()}", "ERROR")
            if temp_file_path.exists():
                try: os.remove(temp_file_path); self.log(f"Removed temp: {temp_file_path}")
                except OSError as remove_err: self.log(f"Error removing temp: {remove_err}", "ERROR")
            raise
    def extract_entry(self, entry: IMtEntryPy, output_dir: str):
        full_name=entry.get_full_name(); output_path=Path(output_dir)/Path(full_name)
        try: output_path.parent.mkdir(parents=True,exist_ok=True); data=self.get_entry_data(entry,compressed=False);
        except Exception as e: self.log(f"Extract prep error {full_name}: {e}", "ERROR"); return False
        if data is None: self.log(f"Skip extract {full_name} (read error).", "ERROR"); return False
        try:
            with open(output_path,'wb') as f: f.write(data); return True
        except Exception as e: self.log(f"Extract write error {full_name}: {e}", "ERROR"); return False
    def add_entry(self, file_path_to_add: str, path_in_archive: str) -> IMtEntryPy | None:
        p_add = Path(file_path_to_add);
        if not p_add.is_file(): self.log(f"File not found: {file_path_to_add}", "ERROR"); return None
        try:
            with open(p_add,'rb') as f: new_data=f.read()
        except Exception as e: self.log(f"Read error add file {file_path_to_add}: {e}", "ERROR"); return None
        EntryClass=MtEntryPy;
        if self.platform==MtArcPlatform.Switch: EntryClass=MtEntrySwitchPy
        elif self._is_extended_name: EntryClass=MtEntryExtendedNamePy
        entry=EntryClass();
        try: entry.set_full_name(path_in_archive)
        except ValueError as e: self.log(f"Set archive path failed '{path_in_archive}': {e}.", "ERROR"); return None
        entry.set_decompressed_size(len(new_data),self.platform); entry.comp_size=-1; entry.offset=-1; entry.data_to_write=new_data; entry.is_dirty=True; self.entries.append(entry);
        # Logged by caller self.log(f"Added entry: {path_in_archive}")
        return entry
    def replace_entry_data(self, entry_to_replace: IMtEntryPy, new_data: bytes):
        if entry_to_replace not in self.entries: self.log(f"Entry {entry_to_replace.get_full_name()} not found.", "ERROR"); return False
        try: entry_to_replace.set_decompressed_size(len(new_data), self.platform); entry_to_replace.data_to_write=new_data; entry_to_replace.is_dirty=True; return True
        except Exception as e: self.log(f"Staging replacement failed for {entry_to_replace.get_full_name()}: {e}", "ERROR"); return False
    def remove_entry(self, entry_to_remove: IMtEntryPy):
         if entry_to_remove in self.entries: self.entries.remove(entry_to_remove); return True
         else: self.log(f"Entry {entry_to_remove.get_full_name()} not found for removal.", "WARN"); return False
    def close(self):
        if self.file_handle:
            if not self.file_handle.closed: self.file_handle.close()
            self.file_handle = None

# --- Hex Editor View Class ---
class HexEditorView(ttk.Frame):
    BYTES_PER_ROW = 32
    BYTES_PER_GROUP = 4 # For column spacing

    def __init__(self, parent, app_instance, is_popup=False):
        super().__init__(parent, style="Dark.TFrame")
        self.app = app_instance
        self.is_popup = is_popup
        self.current_entry = None
        self._raw_data = bytearray() # Use bytearray for mutability
        self._edit_debounce = None
        self._syncing_scroll = False
        self._last_edit_source = None # 'hex' or 'ascii'

        self.grid_rowconfigure(1, weight=1)
        self.grid_columnconfigure(1, weight=1) # Hex view column
        self.grid_columnconfigure(2, weight=1) # ASCII view column

        # --- Toolbar (for popup) ---
        if self.is_popup:
            toolbar = ttk.Frame(self, style="Dark.TFrame")
            toolbar.grid(row=0, column=0, columnspan=4, sticky=tk.EW, pady=(0, 5))
            ttk.Button(toolbar, text="Apply Changes", command=self.apply_changes, style="Dark.TButton").pack(side=tk.LEFT, padx=5)
            # Add other buttons like find, goto etc. later

        # --- Address View ---
        addr_frame = ttk.Frame(self, style="Dark.TFrame")
        addr_frame.grid(row=1, column=0, sticky="ns")
        self.addr_text = tk.Text(addr_frame, width=11, height=20, wrap=tk.NONE, state=tk.DISABLED,
                                 font=("Consolas", 9) if os.name == 'nt' else ("Monospace", 10),
                                 bg=WIDGET_BG, fg=HEX_ADDR_FG, relief=tk.FLAT, bd=0, cursor="arrow")
        self.addr_text.pack(side=tk.LEFT, fill=tk.Y)

        # --- Hex View ---
        hex_frame = ttk.Frame(self, style="Dark.TFrame")
        hex_frame.grid(row=1, column=1, sticky="nsew")
        hex_frame.grid_rowconfigure(0, weight=1); hex_frame.grid_columnconfigure(0, weight=1)
        self.hex_text = tk.Text(hex_frame, width=self.BYTES_PER_ROW * 3 + (self.BYTES_PER_ROW // self.BYTES_PER_GROUP), height=20, wrap=tk.NONE,
                                font=("Consolas", 9) if os.name == 'nt' else ("Monospace", 10), undo=True, maxundo=50,
                                bg=WIDGET_BG, fg=TEXT_COLOR, relief=tk.FLAT, bd=0,
                                selectbackground=HIGHLIGHT_BG, selectforeground=HIGHLIGHT_FG, insertbackground=TEXT_COLOR)
        self.hex_v_scroll = ttk.Scrollbar(hex_frame, orient=tk.VERTICAL, command=self._scroll_views, style="Dark.Vertical.TScrollbar")
        self.hex_text['yscrollcommand'] = self._on_scroll # Custom handler
        self.hex_text.grid(row=0, column=0, sticky="nsew"); self.hex_v_scroll.grid(row=0, column=1, sticky="ns")

        # --- ASCII View ---
        ascii_frame = ttk.Frame(self, style="Dark.TFrame")
        ascii_frame.grid(row=1, column=2, sticky="nsew")
        ascii_frame.grid_rowconfigure(0, weight=1); ascii_frame.grid_columnconfigure(0, weight=1)
        self.ascii_text = tk.Text(ascii_frame, width=self.BYTES_PER_ROW + 2, height=20, wrap=tk.NONE, undo=True, maxundo=50,
                                  font=("Consolas", 9) if os.name == 'nt' else ("Monospace", 10),
                                  bg=WIDGET_BG, fg=TEXT_COLOR, relief=tk.FLAT, bd=0,
                                  selectbackground=HIGHLIGHT_BG, selectforeground=HIGHLIGHT_FG, insertbackground=TEXT_COLOR)
        # ASCII view uses the same scrollbar as Hex view
        self.ascii_text['yscrollcommand'] = self._on_scroll

        self.ascii_text.grid(row=0, column=0, sticky="nsew")

        # --- Tag Configurations ---
        self.hex_text.tag_configure("nullbyte", foreground=HEX_NULL_FG)
        self.ascii_text.tag_configure("nonprintable", foreground=ASCII_NONPRINT_FG)

        # --- Bindings ---
        self.hex_text.bind("<KeyRelease>", lambda e: self.schedule_update(e, 'hex'))
        self.ascii_text.bind("<KeyRelease>", lambda e: self.schedule_update(e, 'ascii'))
        self.hex_text.bind("<<Modified>>", lambda e: self.hex_text.edit_modified(False)) # Track changes
        self.ascii_text.bind("<<Modified>>", lambda e: self.ascii_text.edit_modified(False))

    def _on_scroll(self, *args):
        """Handle scroll events and sync views."""
        if not self._syncing_scroll:
            self._syncing_scroll = True
            self.hex_v_scroll.set(*args) # Update the scrollbar itself first
            # Get current scroll position from the widget that initiated
            if args[0] == 'scroll': # Dragging scrollbar
                 fraction = float(args[1])
            elif args[0] == 'moveto': # Clicking scrollbar arrows/trough
                 fraction = float(args[1])
            else: # Wheel scroll or other means (usually gives 2 args)
                 fraction = float(args[0])

            # Apply the same fraction to other text widgets
            self.addr_text.yview_moveto(fraction)
            self.hex_text.yview_moveto(fraction)
            self.ascii_text.yview_moveto(fraction)
            self._syncing_scroll = False

    def _scroll_views(self, *args):
         """Command for the scrollbar to move all text widgets."""
         if not self._syncing_scroll:
             self._syncing_scroll = True
             self.addr_text.yview(*args)
             self.hex_text.yview(*args)
             self.ascii_text.yview(*args)
             self._syncing_scroll = False

    def clear(self):
        """Clears the hex editor display."""
        self.current_entry = None
        self._raw_data = bytearray()
        for widget in [self.addr_text, self.hex_text, self.ascii_text]:
            widget.config(state=tk.NORMAL)
            widget.delete('1.0', tk.END)
            widget.config(state=tk.DISABLED)
        self.hex_text.edit_reset() # Clear undo stack
        self.ascii_text.edit_reset()

    def load_data(self, entry, data: bytes):
        """Loads and formats byte data into the hex editor."""
        self.clear()
        if not data:
            self.app.log_message(f"No data to display for {entry.get_full_name()}.", "WARN")
            return

        self.current_entry = entry
        self._raw_data = bytearray(data) # Make mutable copy
        self.app.log_message(f"Displaying {len(data):,} bytes for {entry.get_full_name()} in Hex Editor.")

        addr_lines = []
        hex_lines = []
        ascii_lines = []

        for i in range(0, len(data), self.BYTES_PER_ROW):
            chunk = data[i:min(i + self.BYTES_PER_ROW, len(data))]

            # Address
            addr_lines.append(f"{i:08X}: ")

            # Hex representation with spacing
            hex_row_parts = []
            tags_hex = [] # List of (tag, start_col, end_col) for this row
            col = 0
            for j in range(0, self.BYTES_PER_ROW):
                if j < len(chunk):
                    byte_val = chunk[j]
                    hex_byte = f"{byte_val:02X}"
                    hex_row_parts.append(hex_byte)
                    if byte_val == 0: # Tag null bytes
                         tags_hex.append(("nullbyte", col, col + 2))
                    col += 2
                else:
                    hex_row_parts.append("  ") # Padding for incomplete rows
                    col += 2
                if (j + 1) % self.BYTES_PER_GROUP == 0 and j < self.BYTES_PER_ROW - 1:
                     hex_row_parts.append(" ") # Group separator
                     col += 1
            hex_lines.append(("".join(hex_row_parts), tags_hex))

            # ASCII representation
            ascii_row = ""
            tags_ascii = [] # List of (tag, start_col, end_col) for this row
            for j, byte_val in enumerate(chunk):
                char = chr(byte_val) if 32 <= byte_val <= 126 else '.'
                ascii_row += char
                if char == '.':
                     tags_ascii.append(("nonprintable", j, j + 1))
            ascii_lines.append((ascii_row, tags_ascii))


        # --- Populate Widgets ---
        # Need to enable widgets, insert data with tags, then disable again
        for widget in [self.addr_text, self.hex_text, self.ascii_text]:
            widget.config(state=tk.NORMAL)
            widget.delete('1.0', tk.END) # Clear previous content

        # Insert Addresses
        self.addr_text.insert('1.0', "\n".join(addr_lines))

        # Insert Hex and Tags
        current_line = 1
        for hex_line, tags in hex_lines:
             start_index = f"{current_line}.0"
             self.hex_text.insert(start_index, hex_line + "\n")
             for tag, start_col, end_col in tags:
                  tag_start = f"{current_line}.{start_col}"
                  tag_end = f"{current_line}.{end_col}"
                  self.hex_text.tag_add(tag, tag_start, tag_end)
             current_line += 1

        # Insert ASCII and Tags
        current_line = 1
        for ascii_line, tags in ascii_lines:
             start_index = f"{current_line}.0"
             self.ascii_text.insert(start_index, ascii_line + "\n")
             for tag, start_col, end_col in tags:
                  tag_start = f"{current_line}.{start_col}"
                  tag_end = f"{current_line}.{end_col}"
                  self.ascii_text.tag_add(tag, tag_start, tag_end)
             current_line += 1

        # Reset scroll position
        self._scroll_views('moveto', '0.0')

        # Disable editing initially (or enable based on a setting)
        self.hex_text.config(state=tk.NORMAL) # Keep editable for now
        self.ascii_text.config(state=tk.NORMAL)
        self.addr_text.config(state=tk.DISABLED)

        # Reset undo stack after loading new data
        self.hex_text.edit_reset()
        self.ascii_text.edit_reset()
        self.hex_text.edit_modified(False)
        self.ascii_text.edit_modified(False)


    def schedule_update(self, event, source):
        """Debounces edits and schedules the update function."""
        # Cancel previous debounce timer if any
        if self._edit_debounce:
            self.after_cancel(self._edit_debounce)

        # Schedule new update after a short delay (e.g., 300ms)
        self._edit_debounce = self.after(300, lambda s=source: self.handle_edit(s))

    def handle_edit(self, source):
        """Processes edits made in Hex or ASCII view."""
        if not self.current_entry: return
        self._edit_debounce = None # Clear debounce timer ID
        self._last_edit_source = source

        if not (self.hex_text.edit_modified() or self.ascii_text.edit_modified()):
             # print("No modifications detected.")
             return # No changes detected

        self.app.log_message("Processing hex edit...", "DEBUG")

        # Get current cursor position in the source widget
        try:
             if source == 'hex':
                 cursor_index_str = self.hex_text.index(tk.INSERT)
             else: # ascii
                 cursor_index_str = self.ascii_text.index(tk.INSERT)
             line, col = map(int, cursor_index_str.split('.'))
        except Exception as e:
             self.app.log_message(f"Error getting cursor position: {e}", "WARN")
             return

        # --- Get All Text ---
        # Getting all text on every edit is inefficient for large files
        # A better approach tracks specific changes, but is much more complex.
        try:
            hex_content = self.hex_text.get('1.0', tk.END).strip()
            ascii_content = self.ascii_text.get('1.0', tk.END).strip()
        except Exception as e:
             self.app.log_message(f"Error getting text content: {e}", "ERROR")
             return

        # --- Reconstruct Bytes (Basic Overwrite Logic) ---
        new_data = bytearray()
        hex_lines = hex_content.split('\n')
        ascii_lines = ascii_content.split('\n')
        num_lines = len(hex_lines)
        bytes_processed = 0

        for i in range(num_lines):
             hex_line = hex_lines[i]
             # Remove spacing from hex line
             hex_bytes_str = "".join(hex_line.split())

             for j in range(0, len(hex_bytes_str), 2):
                 byte_hex = hex_bytes_str[j:j+2]
                 if len(byte_hex) == 2:
                     try:
                         byte_val = int(byte_hex, 16)
                         if bytes_processed < len(self._raw_data):
                              if self._raw_data[bytes_processed] != byte_val:
                                   # If edited in hex view, update raw data
                                   if source == 'hex':
                                        self._raw_data[bytes_processed] = byte_val
                                        self.app.mark_dirty(True) # Mark ARC as dirty
                                        self.app.set_status(f"Modified byte at offset {bytes_processed:#X}", 5000)
                                   # Add the potentially updated byte
                                   new_data.append(self._raw_data[bytes_processed])
                         else:
                              # Append new byte if user somehow added past the end (basic handling)
                              new_data.append(byte_val)
                              self.app.mark_dirty(True)
                         bytes_processed += 1
                     except ValueError:
                         # Invalid hex input, revert? Log error?
                         self.app.log_message(f"Invalid hex '{byte_hex}' at line {i+1}, col ~{j*1.5}", "WARN")
                         # Append original byte if possible
                         if bytes_processed < len(self._raw_data):
                              new_data.append(self._raw_data[bytes_processed])
                              bytes_processed += 1
                         # How to handle UI reversion cleanly is tricky
             # TODO: Add similar logic if source == 'ascii' to update self._raw_data

        # --- Update the *other* view based on changed raw data ---
        if source == 'hex':
             self.update_view_from_data('ascii')
        elif source == 'ascii':
             self.update_view_from_data('hex')

        # Store modified data back to the entry (important!)
        if self.current_entry:
             self.current_entry.data_to_write = bytes(self._raw_data) # Store bytes copy
             self.current_entry.is_dirty = True # Mark entry itself dirty

        # Reset modified flags after processing
        self.hex_text.edit_modified(False)
        self.ascii_text.edit_modified(False)
        # print("Edit handled.")

    def update_view_from_data(self, view_to_update):
        """Updates the hex or ascii view based on self._raw_data."""
        if not self.current_entry: return
        # This is inefficient - re-renders the whole view.
        # A better way updates only changed lines/bytes.
        self.app.log_message(f"Refreshing {view_to_update} view after edit.", "DEBUG")

        # Get current view position to restore later
        hex_scroll = self.hex_text.yview()
        ascii_scroll = self.ascii_text.yview()

        # Temporarily disable bindings during update to prevent recursion
        self.hex_text.unbind("<KeyRelease>")
        self.ascii_text.unbind("<KeyRelease>")

        # --- Regenerate Content for the target view ---
        if view_to_update == 'hex':
             target_widget = self.hex_text
             target_widget.config(state=tk.NORMAL)
             target_widget.delete('1.0', tk.END)
             current_line = 1
             for i in range(0, len(self._raw_data), self.BYTES_PER_ROW):
                 chunk = self._raw_data[i:min(i + self.BYTES_PER_ROW, len(self._raw_data))]
                 hex_row_parts = []; tags_hex = []; col = 0
                 for j in range(0, self.BYTES_PER_ROW):
                     if j < len(chunk):
                         byte_val = chunk[j]; hex_byte = f"{byte_val:02X}"; hex_row_parts.append(hex_byte)
                         if byte_val == 0: tags_hex.append(("nullbyte", col, col + 2))
                         col += 2
                     else: hex_row_parts.append("  "); col += 2
                     if (j + 1) % self.BYTES_PER_GROUP == 0 and j < self.BYTES_PER_ROW - 1: hex_row_parts.append(" "); col += 1
                 hex_line = "".join(hex_row_parts)
                 start_index = f"{current_line}.0"; target_widget.insert(start_index, hex_line + "\n")
                 for tag, start_col, end_col in tags_hex: target_widget.tag_add(tag, f"{current_line}.{start_col}", f"{current_line}.{end_col}")
                 current_line += 1
        elif view_to_update == 'ascii':
             target_widget = self.ascii_text
             target_widget.config(state=tk.NORMAL)
             target_widget.delete('1.0', tk.END)
             current_line = 1
             for i in range(0, len(self._raw_data), self.BYTES_PER_ROW):
                 chunk = self._raw_data[i:min(i + self.BYTES_PER_ROW, len(self._raw_data))]
                 ascii_row = ""; tags_ascii = []
                 for j, byte_val in enumerate(chunk):
                     try: # Use cp1252 for 'Windows ANSI' like view
                          char = chunk[j:j+1].decode('cp1252')
                          if not char.isprintable() or ord(char) < 32: char = '.'
                     except UnicodeDecodeError: char = '.'
                     ascii_row += char
                     if char == '.': tags_ascii.append(("nonprintable", j, j + 1))
                 start_index = f"{current_line}.0"; target_widget.insert(start_index, ascii_row + "\n")
                 for tag, start_col, end_col in tags_ascii: target_widget.tag_add(tag, f"{current_line}.{start_col}", f"{current_line}.{end_col}")
                 current_line += 1

        target_widget.config(state=tk.NORMAL) # Keep editable? Or disable after refresh?

        # Restore scroll positions
        self.hex_text.yview_moveto(hex_scroll[0])
        self.ascii_text.yview_moveto(ascii_scroll[0])
        self.addr_text.yview_moveto(hex_scroll[0]) # Keep address synced

        # Re-enable bindings
        self.hex_text.bind("<KeyRelease>", lambda e: self.schedule_update(e, 'hex'))
        self.ascii_text.bind("<KeyRelease>", lambda e: self.schedule_update(e, 'ascii'))


    def apply_changes(self):
        """Explicitly called to save changes from editor back to entry (for popup)."""
        if self.current_entry and self.current_entry.is_dirty:
             # The handle_edit method already updates self._raw_data and current_entry.data_to_write
             self.app.log_message(f"Applied hex editor changes to entry: {self.current_entry.get_full_name()}")
             self.app.mark_dirty(True) # Ensure main app knows about changes
             # Maybe close the popup window here?
             # self.master.destroy() # If self.master is the Toplevel window
        else:
             self.app.log_message("No changes in hex editor to apply.", "INFO")


# --- Main GUI Application ---
class MtArcToolApp:
    def __init__(self, root):
        self.root = root
        self.root.title("MT ARC Tool")
        self.root.geometry("950x800") # Wider for hex editor
        self.root.configure(bg=BG_COLOR)

        self.arc = MtArc()
        self.is_dirty = False
        self.tree_item_map = {}
        self.tree_sort_column = "#0" # Default sort column ID (Tree name column)
        self.tree_sort_reverse = False
        self.hex_editor_popup = None # To hold reference to popup window

        self.setup_styles()

        # --- Menu ---
        # ... (Menu setup - unchanged) ...
        self.menu_bar = tk.Menu(root, bg=BG_COLOR, fg=TEXT_COLOR, activebackground=HIGHLIGHT_BG, activeforeground=HIGHLIGHT_FG, relief=tk.FLAT, bd=0)
        self.file_menu = tk.Menu(self.menu_bar, tearoff=0, bg=BUTTON_BG, fg=TEXT_COLOR, activebackground=HIGHLIGHT_BG, activeforeground=HIGHLIGHT_FG)
        self.file_menu.add_command(label="Open ARC", command=self.open_arc, background=BUTTON_BG, foreground=TEXT_COLOR)
        self.file_menu.add_command(label="Save ARC As...", command=self.save_arc_as, state=tk.DISABLED, background=BUTTON_BG, foreground=TEXT_COLOR)
        self.file_menu.add_command(label="Batch Inject...", command=self.open_batch_inject_dialog, background=BUTTON_BG, foreground=TEXT_COLOR)
        self.file_menu.add_separator(background=BG_COLOR)
        self.file_menu.add_command(label="Exit", command=self.on_exit, background=BUTTON_BG, foreground=TEXT_COLOR)
        self.menu_bar.add_cascade(label="File", menu=self.file_menu)
        root.config(menu=self.menu_bar)
        root.protocol("WM_DELETE_WINDOW", self.on_exit)

        # --- Main Frame (PanedWindow for Tree/Hex/Log) ---
        self.main_paned_window = tk.PanedWindow(root, orient=tk.VERTICAL, sashrelief=tk.RAISED, sashwidth=5, bg=BG_COLOR)
        self.main_paned_window.pack(expand=True, fill=tk.BOTH, padx=5, pady=5)

        # --- Top Pane (Tree View) ---
        self.tree_frame = ttk.Frame(self.main_paned_window, style="Dark.TFrame", padding="5")
        self.main_paned_window.add(self.tree_frame, stretch="always", minsize=200)
        self.tree_frame.grid_rowconfigure(0, weight=1); self.tree_frame.grid_columnconfigure(0, weight=1)
        self.tree_scroll_y = ttk.Scrollbar(self.tree_frame, orient=tk.VERTICAL, style="Dark.Vertical.TScrollbar")
        self.tree_scroll_x = ttk.Scrollbar(self.tree_frame, orient=tk.HORIZONTAL, style="Dark.Horizontal.TScrollbar")
        self.tree = ttk.Treeview(
            self.tree_frame, columns=("Size", "CompSize", "Offset"), show="tree headings",
            yscrollcommand=self.tree_scroll_y.set, xscrollcommand=self.tree_scroll_x.set, selectmode="browse", style="Dark.Treeview" # browse select mode
        )
        # ... (Tree headings/columns setup - unchanged) ...
        self.tree.heading("#0", text="File Path", anchor=tk.W, command=lambda: self.sort_tree_column("#0", False))
        self.tree.heading("Size", text="Size", anchor=tk.E, command=lambda: self.sort_tree_column("Size", False))
        self.tree.heading("CompSize", text="Comp Size", anchor=tk.E, command=lambda: self.sort_tree_column("CompSize", False))
        self.tree.heading("Offset", text="Offset", anchor=tk.E, command=lambda: self.sort_tree_column("Offset", False))
        self.tree.column("#0", width=450, stretch=tk.YES, anchor=tk.W); self.tree.column("Size", width=100, stretch=tk.NO, anchor=tk.E)
        self.tree.column("CompSize", width=100, stretch=tk.NO, anchor=tk.E); self.tree.column("Offset", width=100, stretch=tk.NO, anchor=tk.E)
        self.tree_scroll_y.config(command=self.tree.yview); self.tree_scroll_x.config(command=self.tree.xview)
        self.tree.grid(row=0, column=0, sticky="nsew"); self.tree_scroll_y.grid(row=0, column=1, sticky="ns"); self.tree_scroll_x.grid(row=1, column=0, sticky="ew")
        self.tree.bind('<<TreeviewSelect>>', self.on_tree_select) # Bind selection change

        # --- Middle Pane (Embedded Hex Editor) ---
        self.hex_editor_frame_outer = ttk.LabelFrame(self.main_paned_window, text="Hex Editor", style="Dark.TLabelframe", padding=5)
        self.main_paned_window.add(self.hex_editor_frame_outer, stretch="always", minsize=200)
        self.hex_editor_frame_outer.grid_rowconfigure(1, weight=1) # Allow HexEditorView to expand
        self.hex_editor_frame_outer.grid_columnconfigure(0, weight=1)
        # Toolbar for embedded view (Popout button)
        hex_toolbar = ttk.Frame(self.hex_editor_frame_outer, style="Dark.TFrame")
        hex_toolbar.grid(row=0, column=0, sticky=tk.EW)
        self.popout_btn = ttk.Button(hex_toolbar, text="Pop Out Hex Editor", command=self.popout_hex_editor, style="Dark.TButton", state=tk.DISABLED)
        self.popout_btn.pack(side=tk.RIGHT, padx=2, pady=2)
        # Hex Editor View instance (embedded initially)
        self.hex_editor_view = HexEditorView(self.hex_editor_frame_outer, self, is_popup=False)
        self.hex_editor_view.grid(row=1, column=0, sticky="nsew")


        # --- Bottom Pane (Log Console) ---
        self.log_frame = ttk.LabelFrame(self.main_paned_window, text="Console Log", style="Dark.TLabelframe", padding="5")
        self.main_paned_window.add(self.log_frame, stretch="never", minsize=150)
        # ... (Log setup - unchanged) ...
        self.log_frame.grid_rowconfigure(0, weight=1); self.log_frame.grid_columnconfigure(0, weight=1)
        self.log_text = tk.Text(self.log_frame, height=10, width=80, wrap=tk.WORD, state=tk.DISABLED, font=("Consolas", 9) if os.name == 'nt' else ("Monospace", 10), bg=WIDGET_BG, fg=TEXT_COLOR, relief=tk.FLAT, bd=0, selectbackground=HIGHLIGHT_BG, selectforeground=HIGHLIGHT_FG, insertbackground=TEXT_COLOR)
        log_scroll = ttk.Scrollbar(self.log_frame, orient=tk.VERTICAL, command=self.log_text.yview, style="Dark.Vertical.TScrollbar")
        self.log_text['yscrollcommand'] = log_scroll.set; self.log_text.grid(row=0, column=0, sticky="nsew"); log_scroll.grid(row=0, column=1, sticky="ns")
        self.log_text.tag_configure("timestamp", foreground="gray"); self.log_text.tag_configure("info", foreground=TEXT_COLOR)
        self.log_text.tag_configure("debug", foreground="cyan"); self.log_text.tag_configure("print", foreground="lightblue")
        self.log_text.tag_configure("warn", foreground="yellow"); self.log_text.tag_configure("error", foreground="orange")
        self.log_text.tag_configure("fatal", foreground="red", font=(("Consolas", 9, "bold") if os.name == 'nt' else ("Monospace", 10, "bold")))


        # --- Buttons (Below PanedWindow) ---
        self.button_frame = ttk.Frame(root, style="Dark.TFrame", padding=(5, 0, 5, 5))
        self.button_frame.pack(fill=tk.X, side=tk.BOTTOM)
        # ... (Button definitions and packing - unchanged) ...
        self.extract_selected_btn = ttk.Button(self.button_frame, text="Extract Selected", command=self.extract_selected, state=tk.DISABLED, style="Dark.TButton")
        self.extract_all_btn = ttk.Button(self.button_frame, text="Extract All", command=self.extract_all, state=tk.DISABLED, style="Dark.TButton")
        self.add_files_btn = ttk.Button(self.button_frame, text="Add Files...", command=self.add_files, state=tk.DISABLED, style="Dark.TButton")
        self.remove_selected_btn = ttk.Button(self.button_frame, text="Remove Selected", command=self.remove_selected, state=tk.DISABLED, style="Dark.TButton")
        self.replace_selected_btn = ttk.Button(self.button_frame, text="Replace Selected...", command=self.replace_selected, state=tk.DISABLED, style="Dark.TButton")
        self.extract_selected_btn.pack(side=tk.LEFT, padx=5, pady=5); self.extract_all_btn.pack(side=tk.LEFT, padx=5, pady=5)
        self.add_files_btn.pack(side=tk.LEFT, padx=5, pady=5); self.remove_selected_btn.pack(side=tk.LEFT, padx=5, pady=5)
        self.replace_selected_btn.pack(side=tk.LEFT, padx=5, pady=5)

        # --- Status Bar ---
        self.status_var = tk.StringVar()
        self.status_bar = ttk.Label(root, textvariable=self.status_var, relief=tk.FLAT, anchor=tk.W, padding=(5, 3), style="StatusBar.TLabel", background=STATUS_BAR_BG, foreground=TEXT_COLOR)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

        self.redirect_print(); self.arc.set_logger(self.log_message)
        self.set_status("Ready. Open an ARC file."); self.log_message("MT ARC Tool started.", level="INFO"); self.update_button_states()

    def setup_styles(self):
        # ... (Style setup - unchanged) ...
        style = ttk.Style(self.root); style.theme_use('clam')
        style.configure('.', background=BG_COLOR, foreground=TEXT_COLOR, fieldbackground=INPUT_BG, bordercolor=BUTTON_BORDER, lightcolor=WIDGET_BG, darkcolor=BG_COLOR)
        style.map('.', background=[('active', HIGHLIGHT_BG), ('disabled', '#555555')], foreground=[('active', HIGHLIGHT_FG), ('disabled', '#999999')])
        style.configure("Dark.TFrame", background=BG_COLOR)
        style.configure("Dark.TLabelframe", background=BG_COLOR, bordercolor=TEXT_COLOR, relief=tk.GROOVE)
        style.configure("Dark.TLabelframe.Label", background=BG_COLOR, foreground=TEXT_COLOR)
        style.configure("Dark.TButton", background=BUTTON_BG, foreground=BUTTON_FG, relief=tk.RAISED, borderwidth=1, bordercolor=BUTTON_BORDER, padding=5, focuscolor=HIGHLIGHT_FG)
        style.map("Dark.TButton", background=[('pressed', BUTTON_ACTIVE_BG), ('active', HIGHLIGHT_BG)], foreground=[('pressed', HIGHLIGHT_FG), ('active', HIGHLIGHT_FG)], relief=[('pressed', tk.SUNKEN)])
        style.configure("Dark.Treeview", background=WIDGET_BG, foreground=TEXT_COLOR, fieldbackground=WIDGET_BG, rowheight=22)
        style.map("Dark.Treeview", background=[('selected', HIGHLIGHT_BG)], foreground=[('selected', HIGHLIGHT_FG)])
        style.configure("Dark.Treeview.Heading", background=HEADER_BG, foreground=HEADER_FG, relief=tk.RAISED, padding=(5,3))
        style.map("Dark.Treeview.Heading", background=[('active', HIGHLIGHT_BG)])
        style.configure("Dark.Vertical.TScrollbar", background=BUTTON_BG, troughcolor=WIDGET_BG, bordercolor=BUTTON_BORDER, arrowcolor=TEXT_COLOR)
        style.map("Dark.Vertical.TScrollbar", background=[('active', HIGHLIGHT_BG)])
        style.configure("Dark.Horizontal.TScrollbar", background=BUTTON_BG, troughcolor=WIDGET_BG, bordercolor=BUTTON_BORDER, arrowcolor=TEXT_COLOR)
        style.map("Dark.Horizontal.TScrollbar", background=[('active', HIGHLIGHT_BG)])
        style.configure("TEntry", fieldbackground=INPUT_BG, foreground=TEXT_COLOR, insertcolor=TEXT_COLOR, bordercolor=BUTTON_BORDER, borderwidth=1, relief=tk.FLAT)
        style.configure("StatusBar.TLabel", background=STATUS_BAR_BG, foreground=TEXT_COLOR, padding=(5, 3), relief=tk.FLAT)
        style.configure("Dialog.TFrame", background=BG_COLOR)
        style.configure("Dialog.TLabel", background=BG_COLOR, foreground=TEXT_COLOR)
        style.configure("Dialog.TLabelframe", background=BG_COLOR, bordercolor=TEXT_COLOR)
        style.configure("Dialog.TLabelframe.Label", background=BG_COLOR, foreground=TEXT_COLOR)
        style.configure("Dialog.TButton", background=BUTTON_BG, foreground=BUTTON_FG, bordercolor=BUTTON_BORDER)
        style.map("Dialog.TButton", background=[('pressed', BUTTON_ACTIVE_BG), ('active', HIGHLIGHT_BG)])
        style.configure("Dialog.TEntry", fieldbackground=INPUT_BG, foreground=TEXT_COLOR, insertcolor=TEXT_COLOR)
        style.configure("Dialog.Vertical.TScrollbar", background=BUTTON_BG, troughcolor=WIDGET_BG)
        style.map("Dialog.Vertical.TScrollbar", background=[('active', HIGHLIGHT_BG)])

    def log_message(self, message, level="INFO"):
        # ... (log_message - unchanged) ...
        try:
            timestamp = time.strftime("%H:%M:%S"); tag = level.lower()
            self.log_text.config(state=tk.NORMAL)
            self.log_text.insert(tk.END, f"[{timestamp} {level}] ", ("timestamp", tag))
            self.log_text.insert(tk.END, f"{message}\n", (tag,))
            self.log_text.see(tk.END); self.log_text.config(state=tk.DISABLED); self.root.update_idletasks()
        except Exception as e: print(f"LOGGING ERROR: {e}"); print(f"Original Message ({level}): {message}")

    class PrintRedirector:
        # ... (PrintRedirector - unchanged) ...
        def __init__(self, log_method): self.log_method = log_method; self.buffer = ""
        def write(self, message):
            self.buffer += message
            if '\n' in self.buffer: lines = self.buffer.split('\n'); [self.log_method(line.strip(), "PRINT") for line in lines[:-1] if line.strip()]; self.buffer = lines[-1]
        def flush(self):
            if self.buffer.strip(): self.log_method(self.buffer.strip(), "PRINT"); self.buffer = ""

    def redirect_print(self):
        # ... (redirect_print - unchanged) ...
        import sys; sys.stdout = self.PrintRedirector(self.log_message); sys.stderr = self.PrintRedirector(self.log_message)

    def set_status(self, text, duration_ms=0):
        # ... (set_status - unchanged) ...
        self.status_var.set(text); self.root.update_idletasks()
        if duration_ms > 0: self.root.after(duration_ms, lambda: self.status_var.set("Ready.") if self.status_var.get() == text else None)

    def mark_dirty(self, dirty=True):
        # ... (mark_dirty - unchanged) ...
        if dirty == self.is_dirty: return
        self.is_dirty = dirty; title = "MT ARC Tool"
        if self.arc.source_filepath: title += f" - {self.arc.source_filepath.name}"
        elif self.arc.entries: title += " - [New ARC]"
        if self.is_dirty: title += "*"; self.root.title(title); self.update_button_states()

    def update_button_states(self):
        # ... (update_button_states - updated for hex editor) ...
        has_entries = bool(self.arc.entries); has_selection = bool(self.tree.selection())
        single_file_selected = False
        can_popout = False
        if has_selection:
             iid = self.tree.selection()[0]
             tags = self.tree.item(iid, "tags")
             if 'file' in tags:
                 single_file_selected = (len(self.tree.selection()) == 1)
                 can_popout = True # Enable popout if a file is selected

        can_save = has_entries or self.is_dirty
        self.file_menu.entryconfig("Save ARC As...", state=tk.NORMAL if can_save else tk.DISABLED)
        self.extract_selected_btn.config(state=tk.NORMAL if single_file_selected else tk.DISABLED) # Only allow extracting single file for now
        self.extract_all_btn.config(state=tk.NORMAL if has_entries else tk.DISABLED)
        self.add_files_btn.config(state=tk.NORMAL if (self.arc.source_filepath or has_entries) else tk.DISABLED)
        self.remove_selected_btn.config(state=tk.NORMAL if single_file_selected else tk.DISABLED) # Only remove single file for now
        self.replace_selected_btn.config(state=tk.NORMAL if single_file_selected else tk.DISABLED)
        self.popout_btn.config(state=tk.NORMAL if can_popout and not self.hex_editor_popup else tk.DISABLED) # Enable if file selected and not already popped out

    def populate_tree(self):
        # ... (populate_tree - unchanged) ...
        for item in self.tree.get_children(): self.tree.delete(item)
        self.tree_item_map = {}
        if not self.arc.entries: self.update_button_states(); return
        sorted_entries = sorted(self.arc.entries, key=lambda e: e.get_full_name())
        for entry in sorted_entries:
            full_path = entry.get_full_name().replace('\\', '/'); path_parts = full_path.split('/'); filename = path_parts[-1]; parent_iid = ""
            current_path = ""
            for i, part in enumerate(path_parts[:-1]):
                current_path = f"{current_path}/{part}" if current_path else part
                if current_path not in self.tree_item_map: folder_iid = self.tree.insert(parent_iid, tk.END, text=part, open=False, tags=('folder',)); self.tree_item_map[current_path] = folder_iid; parent_iid = folder_iid
                else: parent_iid = self.tree_item_map[current_path]
            size = entry.get_decompressed_size(self.arc.platform); comp_size_val = entry.comp_size if entry.comp_size != -1 else -1
            offset_val = entry.offset if entry.offset != -1 else -1
            comp_size_disp = f"{comp_size_val:,}" if comp_size_val != -1 else "N/A"; offset_disp = f"{offset_val:#0X}" if offset_val != -1 else "N/A"
            file_iid = id(entry)
            self.tree.insert(parent_iid, tk.END, iid=file_iid, text=filename, values=(f"{size:,}", comp_size_disp, offset_disp), tags=('file', entry))
        self.update_button_states()


    def get_selected_entries(self) -> list[IMtEntryPy]:
        # ... (get_selected_entries - unchanged) ...
        selected_iids = self.tree.selection(); entries = []
        for iid in selected_iids:
            try:
                tags = self.tree.item(iid, "tags")
                if tags and 'file' in tags and len(tags) > 1 and isinstance(tags[1], IMtEntryPy): entries.append(tags[1])
            except Exception as e: self.log_message(f"Error retrieving entry for selected item {iid}: {e}", level="ERROR")
        return entries

    def sort_tree_column(self, col, reverse):
        # ... (sort_tree_column - unchanged) ...
        selected_items = self.tree.selection(); parents_to_sort = set()
        if selected_items:
             for iid in selected_items: parents_to_sort.add(self.tree.parent(iid))
        else: parents_to_sort.add("")
        col_map = {"#0": "name", "Size": "size", "CompSize": "compsize", "Offset": "offset"}; sort_key = col_map.get(col)
        if not sort_key: return
        for parent_iid in parents_to_sort:
            children = list(self.tree.get_children(parent_iid));
            if not children: continue
            items_data = []
            for child_iid in children:
                tags = self.tree.item(child_iid, "tags"); is_folder = 'folder' in tags
                entry_obj = tags[1] if len(tags) > 1 and isinstance(tags[1], IMtEntryPy) else None
                item_text = self.tree.item(child_iid, "text"); name_val = item_text; size_val = -1; compsize_val = -1; offset_val = -1
                if entry_obj:
                    try: size_val_str = self.tree.set(child_iid, "Size").replace(',',''); size_val = int(size_val_str) if size_val_str.isdigit() else -1
                    except: pass
                    try: compsize_str = self.tree.set(child_iid, "CompSize").replace(',',''); compsize_val = int(compsize_str) if compsize_str.isdigit() else -1
                    except: pass
                    try: offset_str = self.tree.set(child_iid, "Offset"); offset_val = int(offset_str, 16) if offset_str.startswith('0x') else -1
                    except: pass
                sort_val = name_val
                if sort_key == "size": sort_val = size_val
                elif sort_key == "compsize": sort_val = compsize_val
                elif sort_key == "offset": sort_val = offset_val
                items_data.append({'iid': child_iid, 'sort_key': sort_val, 'is_folder': is_folder})
            try: items_data.sort(key=lambda x: (not x['is_folder'], x['sort_key']), reverse=reverse)
            except TypeError: self.log_message(f"Cannot sort col '{col}' mixed types under '{parent_iid or 'root'}'. Sort by name.", "WARN"); items_data.sort(key=lambda x: (not x['is_folder'], self.tree.item(x['iid'], "text")), reverse=reverse)
            for i, item_info in enumerate(items_data): self.tree.move(item_info['iid'], parent_iid, i)
        self.tree.heading(col, command=lambda: self.sort_tree_column(col, not reverse))


    def on_tree_select(self, event=None):
        """Loads selected file data into the hex editor."""
        selected_iids = self.tree.selection()
        if not selected_iids:
            self.hex_editor_view.clear()
            self.update_button_states()
            return

        iid = selected_iids[0] # Handle only the first selection for hex view
        tags = self.tree.item(iid, "tags")

        if tags and 'file' in tags and len(tags) > 1 and isinstance(tags[1], IMtEntryPy):
            entry = tags[1]
            self.log_message(f"Loading '{entry.get_full_name()}' into Hex Editor...")
            self.set_status(f"Loading {entry.get_full_name()}...")
            try:
                # Use get_entry_data which handles stored data_to_write first
                data = self.arc.get_entry_data(entry, compressed=False)
                if data is None:
                     messagebox.showerror("Load Error", f"Failed to get data for {entry.get_full_name()}. See log.")
                     self.hex_editor_view.clear()
                else:
                    self.hex_editor_view.load_data(entry, data)
                self.set_status(f"Viewing {entry.get_full_name()}")
            except Exception as e:
                 self.log_message(f"Error loading data for hex view: {e}", "ERROR")
                 messagebox.showerror("Load Error", f"Failed to load data for {entry.get_full_name()}:\n{e}")
                 self.hex_editor_view.clear()
                 self.set_status("Error loading data.")
        else:
            # It's a folder or invalid item
            self.hex_editor_view.clear()
            self.set_status("Select a file to view hex.")

        self.update_button_states()

    def popout_hex_editor(self):
        """Moves the hex editor view to a separate Toplevel window."""
        if self.hex_editor_popup or not self.hex_editor_view.current_entry:
            self.log_message("Hex editor already popped out or no file loaded.", "WARN")
            return

        # Create the popup window
        self.hex_editor_popup = tk.Toplevel(self.root)
        self.hex_editor_popup.title(f"Hex Editor - {self.hex_editor_view.current_entry.get_full_name()}")
        self.hex_editor_popup.geometry("800x600")
        self.hex_editor_popup.configure(bg=BG_COLOR)
        # Apply styles to the popup if necessary (styles are usually global)

        # Make the popup transient to the main window
        self.hex_editor_popup.transient(self.root)
        self.hex_editor_popup.protocol("WM_DELETE_WINDOW", self.popin_hex_editor) # Handle closing popup

        # Move the HexEditorView instance to the popup
        self.hex_editor_view.grid_forget() # Remove from embedded frame
        self.hex_editor_view.master = self.hex_editor_popup # Change parent
        self.hex_editor_view.is_popup = True # Update state
        # Re-grid within the popup (might need an outer frame in popup)
        popup_frame = ttk.Frame(self.hex_editor_popup, style="Dark.TFrame", padding=5)
        popup_frame.pack(expand=True, fill=tk.BOTH)
        popup_frame.grid_rowconfigure(1, weight=1) # Allow HexEditorView to expand
        popup_frame.grid_columnconfigure(0, weight=1)
        # Add popup toolbar
        toolbar = ttk.Frame(popup_frame, style="Dark.TFrame")
        toolbar.grid(row=0, column=0, sticky=tk.EW, pady=(0, 5))
        ttk.Button(toolbar, text="Apply Changes", command=self.apply_hex_changes, style="Dark.TButton").pack(side=tk.LEFT, padx=5)
        ttk.Button(toolbar, text="Pop In", command=self.popin_hex_editor, style="Dark.TButton").pack(side=tk.RIGHT, padx=2, pady=2)
        # Place the hex editor view itself
        self.hex_editor_view.grid(row=1, column=0, sticky="nsew")

        self.log_message("Hex editor popped out.")
        self.popout_btn.config(state=tk.DISABLED) # Disable button in main window

    def popin_hex_editor(self):
        """Moves the hex editor back to the embedded frame."""
        if not self.hex_editor_popup:
            return

        # Ask to apply changes first?
        if self.hex_editor_view.current_entry and self.hex_editor_view.current_entry.is_dirty:
             if messagebox.askyesno("Apply Changes?", "Apply changes made in the hex editor before popping in?"):
                  self.apply_hex_changes()
             else:
                  self.log_message("Discarding hex editor changes.", "WARN")
                  # Reload original data?
                  self.on_tree_select() # Re-select to reload

        # Move the view back
        self.hex_editor_view.grid_forget() # Remove from popup frame
        self.hex_editor_view.master = self.hex_editor_frame_outer # Reset parent
        self.hex_editor_view.is_popup = False # Update state
        self.hex_editor_view.grid(row=1, column=0, sticky="nsew") # Re-grid in embedded frame

        # Destroy the popup window
        self.hex_editor_popup.destroy()
        self.hex_editor_popup = None

        self.log_message("Hex editor popped in.")
        self.update_button_states() # Re-enable popout button if file selected

    def apply_hex_changes(self):
        """Applies changes from the hex editor (called from popup)."""
        if self.hex_editor_popup and self.hex_editor_view:
            self.hex_editor_view.apply_changes()
        else:
             self.log_message("Cannot apply hex changes: editor not popped out or invalid.", "WARN")


    # --- Action Methods ---
    # (open_arc, save_arc_as, extract_selected, extract_all, add_files, remove_selected, replace_selected - methods exist, logic correct)
    def open_arc(self):
        if self.is_dirty:
             if not messagebox.askyesno("Unsaved Changes", "Discard unsaved changes and open a new file?"): return
        filepath = filedialog.askopenfilename(title="Open MT ARC File", filetypes=(("ARC files", "*.arc"), ("All files", "*.*")))
        if not filepath: return
        try:
            self.set_status(f"Loading {os.path.basename(filepath)}...")
            if self.arc: self.arc.close(); self.hex_editor_view.clear() # Clear hex view on close
            self.arc = MtArc(); self.arc.set_logger(self.log_message)
            self.arc.load(filepath)
            self.populate_tree(); self.set_status(f"Loaded {len(self.arc.entries)} files from {os.path.basename(filepath)}")
            self.mark_dirty(False)
        except Exception as e: self.log_message(f"Failed load {filepath}: {e}", "ERROR"); messagebox.showerror("Error Loading", f"Failed:\n{e}\n\nSee log."); self.arc = MtArc(); self.arc.set_logger(self.log_message); self.populate_tree(); self.mark_dirty(False)
        finally: self.update_button_states()

    def save_arc_as(self):
        if not self.arc.entries and not self.is_dirty: messagebox.showwarning("Save Error", "No changes or entries to save."); return
        # Apply any pending hex edits before saving
        if self.hex_editor_view and self.hex_editor_view.current_entry and self.hex_editor_view.current_entry.is_dirty:
            self.log_message("Applying pending hex editor changes before saving...", "INFO")
            self.hex_editor_view.apply_changes() # Ensure data is saved back to entry

        initial_name = self.arc.source_filepath.name if self.arc.source_filepath else "Untitled.arc"
        filepath = filedialog.asksaveasfilename(title="Save ARC As", initialfile=initial_name, defaultextension=".arc", filetypes=(("ARC files", "*.arc"), ("All files", "*.*")))
        if not filepath: return
        try:
            self.set_status(f"Saving to {os.path.basename(filepath)}..."); start_time = time.time()
            self.arc.save(filepath); end_time = time.time()
            self.set_status(f"Saved {len(self.arc.entries)} files to {os.path.basename(filepath)} in {end_time - start_time:.2f}s")
            self.mark_dirty(False); self.populate_tree() # Repopulate with potentially updated offsets/sizes
        except Exception as e: messagebox.showerror("Error Saving", f"Failed:\n{e}\n\nSee log."); self.set_status("Saving failed")
        finally: self.update_button_states()

    def extract_selected(self):
        selected_entries = self.get_selected_entries()
        if not selected_entries: messagebox.showwarning("Extraction", "No files selected."); return
        output_dir = filedialog.askdirectory(title="Select Extraction Directory")
        if not output_dir: return
        self.set_status(f"Extracting {len(selected_entries)} file(s)..."); self.log_message(f"Extracting {len(selected_entries)} selected files to: {output_dir}")
        extracted_count, failed_count = 0, 0; start_time = time.time()
        try:
            for entry in selected_entries:
                if self.arc.extract_entry(entry, output_dir): extracted_count += 1
                else: failed_count += 1
            end_time = time.time(); msg = f"Extracted {extracted_count} file(s)"
            if failed_count > 0: msg += f", {failed_count} failed"
            msg += f" in {end_time - start_time:.2f}s."; self.log_message(msg); self.set_status(msg, duration_ms=5000)
        except Exception as e: self.log_message(f"Extraction failed: {e}", "ERROR"); messagebox.showerror("Extraction Error", f"Error:\n{e}"); self.set_status("Extraction failed")

    def extract_all(self):
        if not self.arc.entries: messagebox.showwarning("Extraction", "ARC empty."); return
        output_dir = filedialog.askdirectory(title="Select Extraction Directory for All Files")
        if not output_dir: return
        total_files = len(self.arc.entries); self.set_status(f"Extracting all {total_files} files...")
        self.log_message(f"Extracting {total_files} files to: {output_dir}")
        extracted_count, failed_count = 0, 0; start_time = time.time()
        try:
            for i, entry in enumerate(self.arc.entries):
                if i % 100 == 0: self.set_status(f"Extracting {i+1}/{total_files}...")
                if self.arc.extract_entry(entry, output_dir): extracted_count += 1
                else: failed_count += 1
            end_time = time.time(); msg = f"Extracted {extracted_count} file(s)"
            if failed_count > 0: msg += f", {failed_count} failed"
            msg += f" in {end_time - start_time:.2f}s."; self.log_message(msg); self.set_status(msg, duration_ms=5000)
        except Exception as e: self.log_message(f"Extraction failed: {e}", "ERROR"); messagebox.showerror("Extraction Error", f"Error:\n{e}"); self.set_status("Extraction failed")

    def add_files(self):
        if not self.arc.source_filepath and not self.arc.entries: messagebox.showwarning("Add Error", "Open or create an ARC first."); return
        files_to_add = filedialog.askopenfilenames(title="Select Files to Add")
        if not files_to_add: return
        # TODO: Ask for destination folder in ARC? For now, add to root.
        dest_folder = "" # tk.simpledialog.askstring("Destination Path", "Enter destination path within ARC (e.g., folder/subfolder), leave empty for root:", parent=self.root)
        # if dest_folder is None: return # User cancelled

        self.set_status("Adding files..."); self.log_message(f"Adding {len(files_to_add)} file(s)...")
        added_count = 0; start_time = time.time()
        for f_path in files_to_add:
            archive_path = os.path.join(dest_folder, os.path.basename(f_path)).replace('\\', '/') # Combine path
            self.log_message(f"Adding '{f_path}' as '{archive_path}'")
            if self.arc.add_entry(f_path, archive_path): added_count += 1
        end_time = time.time()
        if added_count > 0: self.populate_tree(); self.mark_dirty(True); msg = f"Added {added_count} file(s) in {end_time - start_time:.2f}s. Save required."; self.log_message(msg); self.set_status(msg, duration_ms=5000)
        else: self.set_status("No files added.", duration_ms=3000)

    def remove_selected(self):
        selected_entries = self.get_selected_entries()
        if not selected_entries: messagebox.showwarning("Remove", "No files selected."); return
        confirm = messagebox.askyesno("Confirm Removal", f"Remove {len(selected_entries)} selected file(s)? Save required.")
        if not confirm: return
        self.log_message(f"Removing {len(selected_entries)} selected file(s)...")
        removed_count = 0; start_time = time.time()
        for entry in selected_entries:
             if self.arc.remove_entry(entry): self.log_message(f"Removed '{entry.get_full_name()}'"); removed_count += 1
        end_time = time.time()
        if removed_count > 0: self.populate_tree(); self.mark_dirty(True); msg = f"Removed {removed_count} file(s) in {end_time - start_time:.2f}s. Save required."; self.log_message(msg); self.set_status(msg, duration_ms=5000)
        # Clear hex editor if the removed file was displayed
        if self.hex_editor_view.current_entry in selected_entries: self.hex_editor_view.clear()


    def replace_selected(self):
        selected_items = self.tree.selection()
        if not selected_items: messagebox.showwarning("Replace", "No file selected."); return
        if len(selected_items) > 1: messagebox.showwarning("Replace", "Select only one file."); return
        iid = selected_items[0]; tags = self.tree.item(iid, "tags")
        if not tags or 'file' not in tags or len(tags) < 2 or not isinstance(tags[1], IMtEntryPy): messagebox.showwarning("Replace", "Selection is not a valid file entry."); return
        entry_to_replace = tags[1]
        file_to_import = filedialog.askopenfilename(title=f"Select File to Replace '{entry_to_replace.get_full_name()}'")
        if not file_to_import: return
        self.log_message(f"Replacing '{entry_to_replace.get_full_name()}' with '{file_to_import}'...")
        try:
            start_time = time.time()
            with open(file_to_import, 'rb') as f_rep: new_data = f_rep.read()
            if self.arc.replace_entry_data(entry_to_replace, new_data):
                end_time = time.time()
                # Reload data in hex editor if this entry is currently viewed
                if self.hex_editor_view.current_entry == entry_to_replace:
                     self.hex_editor_view.load_data(entry_to_replace, new_data)
                self.populate_tree() # Update tree view (size might change)
                self.mark_dirty(True); msg = f"Staged replacement for '{entry_to_replace.get_full_name()}' in {end_time - start_time:.2f}s. Save required."; self.log_message(msg); self.set_status(msg, duration_ms=5000)
            else: self.set_status(f"Replacement failed.", duration_ms=3000)
        except Exception as e: self.log_message(f"Replace failed: {e}", "ERROR"); messagebox.showerror("Replace Error", f"Failed:\n{e}"); self.set_status("Replacement error.")

    def open_batch_inject_dialog(self):
        # ... (open_batch_inject_dialog - unchanged) ...
        if self.is_dirty: messagebox.showwarning("Unsaved Changes", "Save or discard changes before batch op."); return
        if self.arc and self.arc.source_filepath: self.log_message("Closing current ARC before batch op."); self.arc.close(); self.arc = MtArc(); self.arc.set_logger(self.log_message); self.populate_tree(); self.mark_dirty(False); self.hex_editor_view.clear()
        dialog = BatchInjectDialog(self); dialog.wait_window()

    def run_batch_injection(self, original_dir, modified_base_dir, output_dir, log_callback):
        # ... (run_batch_injection - unchanged from previous optimization) ...
        arc_files_processed = 0; arc_files_skipped = 0; total_files_replaced = 0; total_files_failed = 0; start_batch_time = time.time()
        original_path = Path(original_dir); modified_base_path = Path(modified_base_dir); output_path = Path(output_dir)
        try: arc_filepaths = list(original_path.glob('*.arc'))
        except Exception as e: log_callback(f"[FATAL] Error scanning ARCs in {original_path}: {e}"); return
        log_callback(f"Found {len(arc_filepaths)} .arc file(s) in {original_path}")
        if not arc_filepaths: log_callback("No .arc files found."); return
        for i, arc_filepath in enumerate(arc_filepaths):
            arc_filename = arc_filepath.name; modified_arc_folder = modified_base_path / arc_filename # Use full filename for folder
            log_callback(f"\n--- Processing ARC {i+1}/{len(arc_filepaths)}: {arc_filename} ---")
            if not modified_arc_folder.is_dir(): log_callback(f"  [SKIP] Mod folder not found: {modified_arc_folder}"); arc_files_skipped += 1; continue
            batch_arc = MtArc(); batch_arc.set_logger(lambda msg, level="INFO": log_callback(f"    {msg}", level))
            try: batch_arc.load(arc_filepath); log_callback(f"  Loaded original ARC ({len(batch_arc.entries)} entries).")
            except Exception as e: log_callback(f"  [FAIL] Error loading {arc_filename}: {e}. Skipping."); arc_files_skipped += 1; continue
            files_replaced_in_arc = 0; files_failed_in_arc = 0; files_skipped_in_arc = 0; arc_modified = False
            for entry in batch_arc.entries: # Iterate original entries
                entry_archive_path_str = entry.get_full_name().replace('\\', '/'); expected_mod_filepath = modified_arc_folder / entry_archive_path_str
                if expected_mod_filepath.is_file(): # Check if modified file exists
                    try:
                        with open(expected_mod_filepath, 'rb') as mod_f: new_data_bytes = mod_f.read()
                        # log_callback(f"    Replacing: {entry_archive_path_str} ({len(new_data_bytes):,} bytes)") # Optional Verbose
                        if batch_arc.replace_entry_data(entry, new_data_bytes): files_replaced_in_arc += 1; arc_modified = True
                        else: files_failed_in_arc += 1 # Logged internally
                    except Exception as read_err: log_callback(f"    [FAIL] Read error for {expected_mod_filepath}: {read_err}"); files_failed_in_arc += 1
                else: files_skipped_in_arc += 1 # No modified file, skip
            log_callback(f"  Scan done: {files_replaced_in_arc} replaced, {files_failed_in_arc} failed, {files_skipped_in_arc} skipped.")
            if arc_modified:
                output_arc_path = output_path / arc_filename; log_callback(f"  Saving modified ARC: {output_arc_path}")
                try: batch_arc.save(output_arc_path); log_callback(f"  Saved {arc_filename}."); arc_files_processed += 1; total_files_replaced += files_replaced_in_arc; total_files_failed += files_failed_in_arc
                except Exception as e: log_callback(f"  [FAIL] Save error {output_arc_path}: {e}"); arc_files_skipped += 1; total_files_failed += files_replaced_in_arc
            else: log_callback(f"  No mods needed for {arc_filename}. Skipping save."); arc_files_skipped += 1
            batch_arc.close()
        end_batch_time = time.time(); log_callback("\n--- Batch Summary ---"); log_callback(f"Time: {end_batch_time - start_batch_time:.2f}s")
        log_callback(f"ARCs Saved: {arc_files_processed}"); log_callback(f"ARCs Skipped: {arc_files_skipped}")
        log_callback(f"Files Replaced: {total_files_replaced}"); log_callback(f"File Fails: {total_files_failed}")


    def on_exit(self):
        # ... (on_exit - unchanged) ...
         if self.is_dirty:
              if not messagebox.askyesno("Exit", "Unsaved changes exist. Exit anyway?"): return
         if self.arc: self.arc.close()
         # Clean up hex editor popup if it exists
         if self.hex_editor_popup:
              try: self.hex_editor_popup.destroy()
              except: pass
         self.log_message("Exiting MT ARC Tool.")
         self.root.destroy()

# --- Batch Injection Dialog Class ---
# ... (BatchInjectDialog - unchanged from previous version) ...
class BatchInjectDialog(tk.Toplevel):
    def __init__(self, app_instance): # Takes app instance
        super().__init__(app_instance.root) # Parent is app's root
        self.app_instance = app_instance # Store app instance
        self.title("Batch Inject Files"); self.geometry("650x450"); self.resizable(True, True)
        self.grab_set(); self.transient(app_instance.root)
        self.main_frame = ttk.Frame(self, padding="10", style="Dialog.TFrame"); self.main_frame.pack(expand=True, fill=tk.BOTH)
        self.main_frame.grid_rowconfigure(3, weight=1); self.main_frame.grid_columnconfigure(1, weight=1)
        self.paths = {"original": tk.StringVar(), "modified": tk.StringVar(), "output": tk.StringVar()}
        labels = {"original": "Original ARC Directory:", "modified": "Modified Files Root Dir:", "output": "Output ARC Directory:"}
        row_num = 0
        for key, label_text in labels.items():
            ttk.Label(self.main_frame, text=label_text, style="Dialog.TLabel").grid(row=row_num, column=0, sticky=tk.W, pady=3, padx=2)
            entry = ttk.Entry(self.main_frame, textvariable=self.paths[key], width=60, style="Dialog.TEntry")
            entry.grid(row=row_num, column=1, sticky=(tk.W, tk.E), padx=5, pady=3)
            button = ttk.Button(self.main_frame, text="Browse...", style="Dialog.TButton", command=lambda k=key: self.browse_dir(k))
            button.grid(row=row_num, column=2, padx=2, pady=3); row_num += 1
        log_frame = ttk.LabelFrame(self.main_frame, text="Batch Log", padding="5", style="Dialog.TLabelframe")
        log_frame.grid(row=3, column=0, columnspan=3, sticky="nsew", pady=(10, 5)); log_frame.grid_rowconfigure(0, weight=1); log_frame.grid_columnconfigure(0, weight=1)
        self.log_text = tk.Text(log_frame, height=15, width=70, wrap=tk.WORD, state=tk.DISABLED, font=("Consolas", 9) if os.name == 'nt' else ("Monospace", 10), bg=WIDGET_BG, fg=TEXT_COLOR, relief=tk.FLAT, bd=0)
        log_scroll = ttk.Scrollbar(log_frame, orient=tk.VERTICAL, command=self.log_text.yview, style="Dialog.Vertical.TScrollbar")
        self.log_text['yscrollcommand'] = log_scroll.set; self.log_text.grid(row=0, column=0, sticky="nsew"); log_scroll.grid(row=0, column=1, sticky="ns")
        button_frame = ttk.Frame(self.main_frame, style="Dialog.TFrame"); button_frame.grid(row=4, column=0, columnspan=3, pady=(5, 0), sticky=tk.E)
        self.start_button = ttk.Button(button_frame, text="Start Batch Inject", command=self.start_injection, style="Dialog.TButton"); self.start_button.pack(side=tk.RIGHT, padx=5)
        self.close_button = ttk.Button(button_frame, text="Close", command=self.close_dialog, style="Dialog.TButton"); self.close_button.pack(side=tk.RIGHT, padx=5)
        self.is_running = False; self.protocol("WM_DELETE_WINDOW", self.close_dialog); self.setup_dialog_styles()
    def setup_dialog_styles(self): style = ttk.Style(self); pass # Use main styles
    def browse_dir(self, path_key):
        directory = filedialog.askdirectory(title=f"Select {path_key.replace('_',' ').capitalize()} Directory")
        if directory: self.paths[path_key].set(directory)
    def log_message(self, message, level="INFO"):
        timestamp = time.strftime("%H:%M:%S"); log_entry = f"[{timestamp}] {message}\n"
        self.log_text.config(state=tk.NORMAL); self.log_text.insert(tk.END, log_entry); self.log_text.see(tk.END); self.log_text.config(state=tk.DISABLED); self.update_idletasks()
    def set_ui_state(self, enabled):
        state = tk.NORMAL if enabled else tk.DISABLED; self.is_running = not enabled
        widgets_to_toggle = [self.start_button];
        for key in self.paths:
            for child in self.main_frame.winfo_children():
                if isinstance(child, ttk.Entry) and child.cget('textvariable') == str(self.paths[key]): widgets_to_toggle.append(child)
                elif isinstance(child, ttk.Button) and "Browse" in child.cget('text'): widgets_to_toggle.append(child)
        for widget in widgets_to_toggle:
             try: widget.config(state=state)
             except tk.TclError: pass
        self.close_button.config(state=tk.NORMAL)
    def start_injection(self):
        orig_dir=self.paths["original"].get(); mod_dir=self.paths["modified"].get(); out_dir=self.paths["output"].get()
        if not all([orig_dir,mod_dir,out_dir]): messagebox.showerror("Input Error","Select all three dirs."); return
        if not Path(orig_dir).is_dir(): messagebox.showerror("Input Error",f"Original dir not found:\n{orig_dir}"); return
        if not Path(mod_dir).is_dir(): messagebox.showerror("Input Error",f"Modified dir not found:\n{mod_dir}"); return
        out_path=Path(out_dir)
        if not out_path.is_dir():
             if messagebox.askyesno("Create Dir?",f"Output dir not exist:\n{out_dir}\nCreate?"):
                  try: out_path.mkdir(parents=True,exist_ok=True)
                  except Exception as e: messagebox.showerror("Error",f"Failed create output:\n{e}"); return
             else: return
        if Path(orig_dir).resolve()==out_path.resolve(): messagebox.showerror("Input Error","Output cannot be same as Original."); return
        if Path(mod_dir).resolve()==out_path.resolve(): messagebox.showerror("Input Error","Output cannot be same as Modified."); return
        self.log_text.config(state=tk.NORMAL); self.log_text.delete('1.0',tk.END); self.log_text.config(state=tk.DISABLED); self.log_message("Starting Batch Injection...")
        self.log_message(f"  Original: {orig_dir}"); self.log_message(f"  Modified: {mod_dir}"); self.log_message(f"  Output: {out_dir}"); self.log_message("-"*20); self.set_ui_state(False)
        try: self.app_instance.run_batch_injection(orig_dir, mod_dir, out_dir, self.log_message); self.log_message("-"*20); self.log_message("Batch Finished."); messagebox.showinfo("Finished","Batch injection complete.")
        except Exception as e: self.log_message(f"\n--- BATCH FAILED ---"); self.log_message(f"Error: {e}"); self.log_message(traceback.format_exc()); messagebox.showerror("Batch Failed",f"Error:\n{e}\n\nCheck log.")
        finally: self.set_ui_state(True)
    def close_dialog(self):
         if self.is_running: messagebox.showwarning("Process Running","Wait for batch process."); return
         self.destroy()


# --- Main Execution ---
if __name__ == "__main__":
    if not _crcmod_available:
         if not messagebox.askyesno("Missing Dependency", "CRCmod library missing/failed.\nExtension hash lookups will not work.\nContinue anyway?"): import sys; sys.exit(1)
    root = tk.Tk()
    app = MtArcToolApp(root)
    root.mainloop()