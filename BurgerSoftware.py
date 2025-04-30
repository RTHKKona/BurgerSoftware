#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# BurgerSoftware (Kuriimu2 Python Fork) - MT Framework ARC Tool
# Prerequisites: crcmod
# Install using: python -m pip install crcmod

import struct
import zlib
import io
import os
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import tkinter.font # Added import
from enum import Enum
from pathlib import Path
import inspect # Might be needed for future TypeReader/Writer
import time
import traceback # For logging detailed errors
from collections import defaultdict # For folder tree
import math # For hex editor rows
import threading # For potentially non-blocking batch operations

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
# HEX_NULL_FG = '#606060'     # REMOVED - Null bytes will use default TEXT_COLOR
ASCII_NONPRINT_FG = '#606060'# Darker gray for non-printable chars in ASCII view
EDITED_FG = '#ff6060'         # Reddish color for edited bytes

# --- Constants and Enums ---
class ByteOrder(Enum):
    LittleEndian = 0
    BigEndian = 1

class BitOrder(Enum): # Keep for future compatibility
    Default = 0
    LeastSignificantBitFirst = 1
    MostSignificantBitFirst = 2
    LowestAddressFirst = 3
    HighestAddressFirst = 4

class MtArcPlatform(Enum):
    LittleEndian = 0
    Switch = 1
    BigEndian = 2

FILENAME_ENCODING = 'shift_jis' # Defaulting based on analysis

# --- CRC32 Calculation (Using crcmod) ---
_crc32_func = None
if _crcmod_available:
    try:
        # Parameters derived from C# Kryptography.Hash.Crc.Crc32 used by MtArcSupport
        _crc32_func = crcmod.mkCrcFun(0x104C11DB7, initCrc=0xFFFFFFFF, rev=True, xorOut=0x00000000)

        def calculate_mt_crc32_intermediate(data_bytes):
            """Calculates the raw CRC value before the final ~ operation."""
            if not _crc32_func: raise RuntimeError("crcmod function not initialized")
            return _crc32_func(data_bytes)

        def get_hash(input_string, encoding=FILENAME_ENCODING):
            """Calculates the specific hash used for MT Framework extensions."""
            if not _crc32_func: raise RuntimeError("crcmod function not initialized")
            try:
                input_bytes = input_string.encode(encoding, errors='replace')
                crc_val = calculate_mt_crc32_intermediate(input_bytes)
                return (~crc_val) & 0xFFFFFFFF
            except Exception as e:
                print(f"Error calculating hash for '{input_string}' with encoding '{encoding}': {e}")
                raise
    except Exception as e:
         print(f"Error initializing crcmod function: {e}")
         _crcmod_available = False
         def get_hash(input_string, encoding='utf-8'):
            print("CRCMOD init failed, cannot calculate hash!")
            return 0
elif not _crcmod_available: # If import failed earlier
    def get_hash(input_string, encoding='utf-8'):
            print("CRCMOD unavailable, cannot calculate hash!")
            return 0

# --- Precompute Extension Map ---
print("Calculating extension map hashes...")
EXTENSION_MAP_HASH_TO_EXT = {}
EXTENSION_MAP_EXT_TO_HASH = {}
_EXTENSION_MAP_RAW = {
    "rAIFSM": ".xfsa", "rCameraList": ".lcm", "rCharacter": ".xfsc", "rCollision": ".sbc", "rEffectAnim": ".ean",
    "rEffectList": ".efl", "rGUI": ".gui", "rGUIFont": ".gfd", "rGUIIconInfo": ".gii", "rGUIMessage": ".gmd",
    "rHit2D": ".xfsh", "rLayoutParameter": ".xfsl", "rMaterial": ".mrl", "rModel": ".mod", "rMotionList": ".lmt",
    "rPropParam": ".prp", "rScheduler": ".sdl", "rSoundBank": ".sbkr", "rSoundRequest": ".srqr",
    "rSoundSourceADPCM": ".mca", "rTexture": ".tex", "rBodyEdit": ".bed", "rEditConvert": ".edc",
    "rEffect2D": ".e2d", "rFaceEdit": ".fed", "rFacialAnimation": ".fca",
    0x22FA09: ".hpe", 0x26E7FF: ".ccl", 0x86B80F: ".plexp", 0xFDA99B: ".ntr", 0x2358E1A: ".spkg",
    0x2373BA7: ".spn", 0x2833703: ".efs", 0x315E81F: ".sds", 0x437BCF2: ".grw", 0x4B4BE62: ".tmd",
    0x525AEE2: ".wfp", 0x5A36D08: ".qif", 0x69A1911: ".olp", 0x737E28B: ".rst", 0x7437CCE: ".base",
    0x79B5F3E: ".pci", 0x7F768AF: ".gii", 0x89BEF2C: ".sap", 0xA74682F: ".rnp", 0xC4FCAE4: ".PlDefendParam",
    0xD06BE6B: ".tmn", 0xECD7DF4: ".scs", 0x11C35522: ".gr2", 0x12191BA1: ".epv", 0x12688D38: ".pjp",
    0x12C3BFA7: ".cpl", 0x133917BA: ".mss", 0x14428EAE: ".gce", 0x15302EF4: ".lot", 0x157388D3: ".itl",
    0x15773620: ".nmr", 0x167DBBFF: ".stq", 0x1823137D: ".mlm", 0x19054795: ".nnl", 0x199C56C0: ".ocl",
    0x1B520B68: ".zon", 0x1BCC4966: ".srq", 0x1C2B501F: ".atr", 0x1EB3767C: ".spr", 0x2052D67E: ".sn2",
    0x215896C2: ".statusparam", 0x2282360D: ".jex", 0x22948394: ".gui", 0x22B2A2A2: ".PlNeckPos",
    0x232E228C: ".rev", 0x241F5DEB: ".tex", 0x242BB29A: ".gmd", 0x257D2F7C: ".swm", 0x2749C8A8: ".mrl",
    0x271D08FE: ".ssq", 0x272B80EA: ".prp", 0x2A37242D: ".gpl", 0x2A4F96A8: ".rbd", 0x2B0670A5: ".map",
    0x2B303957: ".gop", 0x2B40AE8F: ".equ", 0x2CE309AB: ".joblvl", 0x2D12E086: ".srd", 0x2D462600: ".gfd",
    0x30FC745F: ".smx", 0x312607A4: ".bll", 0x31B81AA5: ".qr", 0x325AACA5: ".shl", 0x32E2B13B: ".edp",
    0x33B21191: ".esp", 0x354284E7: ".lvl", 0x358012E8: ".vib", 0x39A0D1D6: ".sms", 0x39C52040: ".lcm",
    0x3A947AC1: ".cql", 0x3B350990: ".qsp", 0x3BBA4E33: ".qct", 0x3D97AD80: ".amr", 0x3E356F93: ".stc",
    0x3E363245: ".chn", 0x3FB52996: ".imx", 0x4046F1E1: ".ajp", 0x437662FC: ".oml", 0x4509FA80: ".itemlv",
    0x456B6180: ".cnsshake", 0x472022DF: ".AIPlActParam", 0x48538FFD: ".ist", 0x48C0AF2D: ".msl",
    0x49B5A885: ".ssc", 0x4B704CC0: ".mia", 0x4C0DB839: ".sdl", 0x4CA26828: ".bmse", 0x4E397417: ".ean",
    0x4E44FB6D: ".fpe", 0x4EF19843: ".nav", 0x4FB35A95: ".aor", 0x50F3D713: ".skl", 0x5175C242: ".geo2",
    0x51FC779F: ".sbc", 0x522F7A3D: ".fcp", 0x52DBDCD6: ".rdd", 0x535D969F: ".ctc", 0x5802B3FF: ".ahc",
    0x58A15856: ".mod", 0x59D80140: ".ablparam", 0x5A7FEA62: ".ik", 0x5B334013: ".bap", 0x5EA7A3E9: ".sky",
    0x5F36B659: ".way", 0x5F88B715: ".epd", 0x60BB6A09: ".hed", 0x6186627D: ".wep", 0x619D23DF: ".shp",
    0x628DFB41: ".gr2s", 0x63747AA7: ".rpi", 0x63B524A7: ".ltg", 0x64387FF1: ".qlv", 0x65B275E5: ".sce",
    0x66B45610: ".fsm", 0x671F21DA: ".stp", 0x69A5C538: ".dwm", 0x6D0115ED: ".prt", 0x6D5AE854: ".efl",
    0x6DB9FA5F: ".cmc", 0x6EE70EFF: ".pcf", 0x6F302481: ".plw", 0x6FE1EA15: ".spl", 0x72821C38: ".stm",
    0x73850D05: ".arc", 0x754B82B4: ".ahs", 0x76820D81: ".lmt", 0x76DE35F6: ".rpn", 0x7808EA10: ".rtex",
    0x7817FFA5: ".fbik_human", 0x7AA81CAB: ".eap", 0x7BEC319A: ".sps", 0x7DA64808: ".qmk", 0x7E1C8D43: ".pcs",
    0x7E33A16C: ".spc", 0x7E4152FF: ".stg", 0x17A550D: ".lom", 0x253F147: ".hit", 0x39D71F2: ".rvt",
    0xDADAB62: ".oba", 0x10C460E6: ".msg", 0x176C3F95: ".los", 0x19A59A91: ".lnk", 0x1BA81D3C: ".nck",
    0x1ED12F1B: ".glp", 0x1EFB1B67: ".adh", 0x2447D742: ".idm", 0x266E8A91: ".lku", 0x2C4666D1: ".smh",
    0x2DC54131: ".cdf", 0x30ED4060: ".pth", 0x36E29465: ".hkx", 0x38F66FC3: ".seg", 0x430B4FF4: ".ptl",
    0x46810940: ".egv", 0x4D894D5D: ".cmi", 0x4E2FEF36: ".mtg", 0x4F16B7AB: ".hri", 0x50F9DB3E: ".bfx",
    0x5204D557: ".shp", 0x538120DE: ".eng", 0x557ECC08: ".aef", 0x585831AA: ".pos", 0x5898749C: ".bgm",
    0x60524FBB: ".shw", 0x60DD1B16: ".lsp", 0x758B2EB7: ".cef", 0x7D1530C2: ".sngw", 0x46FB08BA: ".bmt",
    0x285A13D9: ".vzo", 0x4323D83A: ".stex", 0x6A5CDD23: ".occ", 0x62440501: ".lmd", 0x62A68441: ".thk",
    0x4D3C70A1: ".bth", 0x244CC507: ".itr", 0x6A9197ED: ".sss", 0x3B764DD4: ".sstr", 0x3516C3D2: ".lfd",
    0x0CF7FB37: ".msf", 0x3D2E1661: ".ein", 0x3B5A0DA5: ".idx", 0x354E1E08: ".ard", 0x5B9071CF: ".col",
    0x342366F0: ".atk", 0x76042FD2: ".eco", 0x052CCE4E: ".mef", 0x55E21D03: ".emp", 0x51BE0EC: ".rut",
    0x70078B5: ".rmt", 0x949A1DA: ".adl", 0x9C48A11: ".unk", 0xA736313: ".mdl", 0x108F442E: ".mdl",
    0x130124FA: ".rmh", 0x18FF29AB: ".cut", 0x1BE1DBEB: ".dom", 0x24339E8C: ".evl", 0x28D65BFA: ".pos",
    0x2ADFA358: ".pvl", 0x348C831D: ".evc", 0x375F06DA: ".evt", 0x40171000: ".dat", 0x42940D09: ".fmt",
    0x4356673E: ".man", 0x46C78353: ".mes", 0x5DF3D947: ".mry", 0x5FF4BE71: ".ene", 0x6505B384: ".ddsp",
    0x681835FC: ".itm", 0x6A76E771: ".mes", 0x6B0369B1: ".atr", 0x6B571E45: ".lgt", 0x6E69693A: ".obj",
    0x7050198A: ".pmb", 0x74AFE18C: ".mdl", 0x7618CC9A: ".mtn", 0x7D9D148B: ".eft", 0x7DB518E8: ".mdl",
    0x7F68C6AF: ".mpac",
}

if _crcmod_available:
    for k, v in _EXTENSION_MAP_RAW.items():
        hash_val = 0
        if isinstance(k, str):
            try: hash_val = get_hash(k)
            except Exception: pass
        elif isinstance(k, int): hash_val = k
        if hash_val != 0:
            EXTENSION_MAP_HASH_TO_EXT[hash_val] = v
            if v not in EXTENSION_MAP_EXT_TO_HASH: EXTENSION_MAP_EXT_TO_HASH[v] = hash_val
else:
    print("Skipping string-based extension map generation as crcmod is unavailable.")
    for k, v in _EXTENSION_MAP_RAW.items():
         if isinstance(k, int):
              EXTENSION_MAP_HASH_TO_EXT[k] = v
              if v not in EXTENSION_MAP_EXT_TO_HASH: EXTENSION_MAP_EXT_TO_HASH[v] = k
print(f"Generated {len(EXTENSION_MAP_HASH_TO_EXT)} hash->ext entries.")
print(f"Generated {len(EXTENSION_MAP_EXT_TO_HASH)} ext->hash entries.")

def determine_extension(extension_hash):
    return EXTENSION_MAP_HASH_TO_EXT.get(extension_hash, f".{extension_hash:08X}")

def determine_extension_hash(extension):
    if not extension.startswith('.'): extension = '.' + extension
    hash_val = EXTENSION_MAP_EXT_TO_HASH.get(extension)
    if hash_val is not None: return hash_val
    if len(extension) == 9: # Try parsing like ".AABBCCDD"
        try: return int(extension[1:], 16)
        except ValueError: pass
    if not _crcmod_available: raise ValueError(f"Extension '{extension}' cannot be mapped (crcmod missing/failed).")
    else: raise ValueError(f"Extension '{extension}' cannot be mapped to a known hash.")

# --- IO Classes ---
class BinaryReaderXPy:
    """Reads standard data types, handles byte order."""
    def __init__(self, stream, byte_order=ByteOrder.LittleEndian, encoding=FILENAME_ENCODING):
        self.base_stream = stream
        self.byte_order = byte_order
        self._encoding_default = encoding
        self._fmt_prefix = '<' if byte_order == ByteOrder.LittleEndian else '>'
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
            if length == -1:
                 byte_list = []
                 while True:
                      b = self.read_bytes(1)
                      if not b or b == b'\0': break
                      byte_list.append(b)
                 raw_bytes = b''.join(byte_list)
            else:
                 raw_bytes = self.read_bytes(length)
                 null_pos = raw_bytes.find(b'\0')
                 if null_pos != -1: raw_bytes = raw_bytes[:null_pos]
            return raw_bytes.decode(enc, errors='replace')
        except Exception as e:
             print(f"[WARN] Failed to decode string bytes with {enc}: {raw_bytes!r}. Error: {e}")
             return raw_bytes.decode('ascii', errors='replace')
    def peek_bytes(self, count, offset=0):
         if not self.base_stream or self.base_stream.closed: raise ValueError("Stream is closed")
         current_pos = self.tell(); target_pos = current_pos + offset
         try:
              self.seek(target_pos)
              data = self.base_stream.read(count)
              if len(data) != count: raise EOFError(f"Could not peek {count} bytes (got {len(data)}).")
              return data
         finally: self.seek(current_pos)
    def peek_string(self, length=4, offset=0, encoding=None):
         try:
             raw_bytes = self.peek_bytes(length, offset)
             enc = encoding if encoding is not None else self._encoding_default
             null_pos = raw_bytes.find(b'\0')
             if null_pos != -1: raw_bytes = raw_bytes[:null_pos]
             return raw_bytes.decode(enc, errors='replace')
         except EOFError: return ""
         except Exception as e:
             print(f"[WARN] Failed to decode peeked string bytes with {encoding or self._encoding_default}: {raw_bytes!r}. Error: {e}")
             return raw_bytes.decode('ascii', errors='replace')
    def reset_bit_buffer(self): pass
    def read_bits(self, count): raise NotImplementedError("Bit reading not implemented yet.")
    def read_bit(self): raise NotImplementedError("Bit reading not implemented yet.")

class BinaryWriterXPy:
    """Writes standard data types, handles byte order."""
    def __init__(self, stream, byte_order=ByteOrder.LittleEndian, encoding=FILENAME_ENCODING):
        self.base_stream = stream
        self.byte_order = byte_order
        self._encoding_default = encoding
        self._fmt_prefix = '<' if byte_order == ByteOrder.LittleEndian else '>'
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
        except Exception as e: print(f"[WARN] Encoding string '{value}' failed with {enc}: {e}. Using ASCII."); encoded_bytes = value.encode('ascii', errors='replace')
        if length == -1: self.write_bytes(encoded_bytes + b'\0')
        else:
             if len(encoded_bytes) > length: truncated_bytes = encoded_bytes[:length]; print(f"[WARN] String '{value}' truncated from {len(encoded_bytes)} to {length} bytes."); self.write_bytes(truncated_bytes)
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
    def __init__(self, file_name="", ext_hash=0, comp_size=0, decomp_size_raw=0, offset=0):
        self.file_name_str = file_name; self.extension_hash = ext_hash & 0xFFFFFFFF; self.comp_size = comp_size
        self._decomp_size_raw = decomp_size_raw; self.offset = offset; self.is_dirty = False; self.data_to_write = None
    def get_full_name(self):
        try: return self.file_name_str + determine_extension(self.extension_hash)
        except Exception as e: print(f"[ERROR] Failed getting full name for hash {self.extension_hash:#08X}: {e}"); return self.file_name_str + f".{self.extension_hash:08X}"
    def set_full_name(self, full_path_str):
        p = Path(full_path_str); ext = p.suffix
        try: self.extension_hash = determine_extension_hash(ext) & 0xFFFFFFFF; self.file_name_str = str(p.with_suffix(''))
        except ValueError as e: print(f"[ERROR] setting name '{full_path_str}': {e}. Keeping old name '{self.get_full_name()}'.")
    def get_decompressed_size(self, platform):
        try: size_raw = int(self._decomp_size_raw)
        except (TypeError, ValueError): print(f"[WARN] Bad decomp value: {self._decomp_size_raw}"); return 0
        if platform == MtArcPlatform.LittleEndian: return size_raw & 0x00FFFFFF
        elif platform == MtArcPlatform.BigEndian: return (size_raw & 0xFFFFFFFF) >> 3
        else: return size_raw
    def set_decompressed_size(self, size, platform):
         try:
             current_flags_raw = self._decomp_size_raw; current_flags = int(current_flags_raw) if isinstance(current_flags_raw, int) else 0
             target_size = max(0, int(size))
             if platform == MtArcPlatform.LittleEndian: self._decomp_size_raw = (current_flags & 0xFF000000) | (target_size & 0x00FFFFFF)
             elif platform == MtArcPlatform.BigEndian: self._decomp_size_raw = (current_flags & 0x00000007) | ((target_size << 3) & 0xFFFFFFF8)
             else: self._decomp_size_raw = target_size
         except (TypeError, ValueError) as e: print(f"[WARN] Failed setting decomp size ({size=}, {self._decomp_size_raw=}): {e}"); self._decomp_size_raw = size
    def to_bytes(self, platform, encoding): raise NotImplementedError
    def _pack_int32(self, value): return max(-2147483648, min(int(value), 2147483647))

class MtEntryPy(BaseMtEntryPy):
    FILENAME_LEN = 64; STRUCT_FORMAT_LE = f"< {FILENAME_LEN}s I i i i"; STRUCT_FORMAT_BE = f"> {FILENAME_LEN}s I i i i"; SIZE = 80
    @classmethod
    def from_bytes(cls, data, platform, encoding=FILENAME_ENCODING):
        fmt=cls.STRUCT_FORMAT_BE if platform==MtArcPlatform.BigEndian else cls.STRUCT_FORMAT_LE;
        try: name_bytes, ext_hash, comp_size, decomp_size_raw, offset=struct.unpack(fmt,data)
        except struct.error as e: raise IOError(f"Unpack MtEntryPy failed: {e}")
        try: file_name=name_bytes.decode(encoding,errors='replace').partition('\0')[0]
        except Exception as e: print(f"[WARN] Failed decoding filename: {e}"); file_name=name_bytes.partition(b'\0')[0].decode('ascii',errors='replace')
        return cls(file_name, ext_hash, comp_size, decomp_size_raw, offset)
    def to_bytes(self, platform, encoding=FILENAME_ENCODING):
        fmt=self.STRUCT_FORMAT_BE if platform==MtArcPlatform.BigEndian else self.STRUCT_FORMAT_LE;
        try: name_bytes=self.file_name_str.encode(encoding,errors='replace')
        except Exception as e: print(f"[WARN] Failed encoding filename: {e}"); name_bytes=self.file_name_str.encode('ascii',errors='replace')
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
        except Exception as e: print(f"[WARN] Failed decoding filename: {e}"); file_name=name_bytes.partition(b'\0')[0].decode('ascii',errors='replace')
        return cls(file_name, ext_hash, comp_size, decomp_size_raw, offset, unk1)
    def to_bytes(self, platform, encoding=FILENAME_ENCODING):
         fmt=self.STRUCT_FORMAT_LE;
         try: name_bytes=self.file_name_str.encode(encoding,errors='replace')
         except Exception as e: print(f"[WARN] Failed encoding filename: {e}"); name_bytes=self.file_name_str.encode('ascii',errors='replace')
         padded_name=name_bytes.ljust(self.FILENAME_LEN,b'\0')[:self.FILENAME_LEN];
         try: return struct.pack(fmt,padded_name, self.extension_hash, self._pack_int32(self.comp_size), self._pack_int32(self._decomp_size_raw), self._pack_int32(self.unk1), self._pack_int32(self.offset))
         except Exception as e: raise IOError(f"Pack MtEntrySwitchPy failed for {self.get_full_name()}: {e}")


# --- Core ARC Logic ---
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
        initial_pos = stream.tell();
        try:
            header_bytes = stream.read(MtHeaderPy.SIZE);
            if len(header_bytes) < MtHeaderPy.SIZE: raise IOError("File too small");
            try: magic_le, version_le, _ = struct.unpack(MtHeaderPy.STRUCT_FORMAT_LE, header_bytes)
            except struct.error: magic_le, version_le = None, None
            try: magic_be, _, _ = struct.unpack(MtHeaderPy.STRUCT_FORMAT_BE, header_bytes)
            except struct.error: magic_be = None
            if magic_le == b'ARC\0': return MtArcPlatform.Switch if version_le == 9 else MtArcPlatform.LittleEndian
            if magic_be == b'\0CRA': return MtArcPlatform.BigEndian
            raise ValueError("Unknown ARC format")
        finally: stream.seek(initial_pos)
    def _measure_type(self, cls):
        if hasattr(cls, 'SIZE'): return cls.SIZE; raise NotImplementedError(f"No size for {cls.__name__}")
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
                         # Peek requires care with reader position; use offset from start for safety
                         peek_offset = temp_reader.tell()
                         first_entry_bytes = temp_reader.peek_bytes(MtEntryPy.SIZE, offset=0) # Peek from current pos
                         peek_entry = MtEntryPy.from_bytes(first_entry_bytes, self.platform, self.encoding)
                         peek_decomp_size = peek_entry.get_decompressed_size(self.platform)
                         if peek_entry.extension_hash == 0 or peek_decomp_size == 0 or peek_entry.offset == 0:
                              self._is_extended_name = True; EntryClass = MtEntryExtendedNamePy; self.log("Extended Names")
                         else: self.log("Standard Names")
                     except EOFError: self.log("EOF during peek for extended name check.", "WARN")
                     except Exception as e: self.log(f"Peek failed: {e}. Assuming standard.", "WARN")
                     # temp_reader.seek(peek_offset) # Ensure position is correct after peek
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
        v=self.header.version; order='big' if self.platform==MtArcPlatform.BigEndian else 'little'; alignment=0
        if v in [4,7,8,16] and order=='little': alignment=0x8000
        elif v==9: alignment=0x8000
        elif v==17 and order=='little': alignment=0x100 # 0x11 = 17 decimal
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
            decomp_size=entry.get_decompressed_size(self.platform); is_zlib_compressed=False
            if entry.comp_size==0: is_zlib_compressed=False
            elif self.platform==MtArcPlatform.Switch: is_zlib_compressed=True
            elif entry.comp_size!=decomp_size:
                 if entry.comp_size>=2: cmf_flg=struct.unpack('>H',comp_data[:2])[0]; is_zlib_compressed=((cmf_flg&0x0F00)>>8 == 8)
                 else: self.log(f"Size mismatch, data too small {entry.comp_size}: {entry.get_full_name()}", "WARN"); is_zlib_compressed=True
                 if is_zlib_compressed and entry.comp_size >= 2 and not ((cmf_flg&0x0F00)>>8 == 8): self.log(f"Size mismatch header {cmf_flg:#04X} not Zlib: {entry.get_full_name()}", "WARN"); is_zlib_compressed=False
            if is_zlib_compressed:
                if compressed: return comp_data
                try: raw_data=zlib.decompress(comp_data);
                except zlib.error as e: self.log(f"Zlib decompress failed {entry.get_full_name()}: {e}. Returning compressed.", "ERROR"); return comp_data
                if len(raw_data)!=decomp_size: self.log(f"Decomp size mismatch {entry.get_full_name()}. Expected {decomp_size}, got {len(raw_data)}.", "WARN")
                return raw_data
            else: return comp_data
        else: self.log(f"No data source for {entry.get_full_name()}", "WARN"); return b''
    def save(self, filepath):
        if not self.entries and not (self.header and self.header.magic): raise ValueError("No data to save.")
        if self.file_handle and not self.file_handle.closed: self.log("Closing loaded file before saving.", "DEBUG"); self.close()
        filepath = Path(filepath); self.log(f"Saving: {filepath}")
        EntryClass=MtEntryPy;
        if self.platform==MtArcPlatform.Switch: EntryClass=MtEntrySwitchPy
        elif self._is_extended_name: EntryClass=MtEntryExtendedNamePy
        entry_size=self._measure_type(EntryClass); current_entry_count=len(self.entries)
        self.header.entry_count=current_entry_count; current_file_offset=self._determine_file_offset(current_entry_count, entry_size)
        self.log(f"Platform: {self.platform}, Ver: {self.header.version:#0X}, Count: {current_entry_count}, Entry: {EntryClass.__name__}, Data Offset: {current_file_offset:#0X}")
        temp_file_path=filepath.with_suffix(filepath.suffix + ".~tmp"); saved_entries_meta=[]
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
                    # writer.write_alignment(4) # Optional padding
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
    BYTES_PER_GROUP = 4

    def __init__(self, parent, app_instance, is_popup=False):
        super().__init__(parent, style="Dark.TFrame")
        self.app = app_instance; self.is_popup = is_popup; self.current_entry = None
        self._raw_data = bytearray(); self._edit_debounce = None; self._syncing_scroll = False
        self._last_edit_source = None

        self.font_size = 10 if os.name == 'nt' else 11 # Increased font size
        self.hex_font = ("Consolas", self.font_size) if os.name == 'nt' else ("Monospace", self.font_size)

        self.grid_rowconfigure(1, weight=1); self.grid_columnconfigure(1, weight=1); self.grid_columnconfigure(2, weight=1)

        self.hex_toolbar = ttk.Frame(self, style="Dark.TFrame")
        self.hex_toolbar.grid(row=0, column=0, columnspan=3, sticky=tk.EW, pady=(0, 5))
        self.apply_btn = ttk.Button(self.hex_toolbar, text="Apply Changes", command=self.apply_changes, style="Dark.TButton", state=tk.DISABLED)
        self.popout_btn = ttk.Button(self.hex_toolbar, text="Pop Out", command=self.app.popout_hex_editor, style="Dark.TButton", state=tk.DISABLED)
        self.popin_btn = ttk.Button(self.hex_toolbar, text="Pop In", command=self.app.popin_hex_editor, style="Dark.TButton")
        self.show_toolbar()

        addr_frame = ttk.Frame(self, style="Dark.TFrame"); addr_frame.grid(row=1, column=0, sticky="ns")
        self.addr_text = tk.Text(addr_frame, width=11, height=20, wrap=tk.NONE, state=tk.DISABLED, font=self.hex_font, bg=WIDGET_BG, fg=HEX_ADDR_FG, relief=tk.FLAT, bd=0, cursor="arrow")
        self.addr_text.pack(side=tk.LEFT, fill=tk.Y)

        hex_frame = ttk.Frame(self, style="Dark.TFrame"); hex_frame.grid(row=1, column=1, sticky="nsew")
        hex_frame.grid_rowconfigure(0, weight=1); hex_frame.grid_columnconfigure(0, weight=1)
        self.hex_text = tk.Text(hex_frame, width=self.BYTES_PER_ROW * 3 + (self.BYTES_PER_ROW // self.BYTES_PER_GROUP), height=20, wrap=tk.NONE, font=self.hex_font, undo=True, maxundo=50, bg=WIDGET_BG, fg=TEXT_COLOR, relief=tk.FLAT, bd=0, selectbackground=HIGHLIGHT_BG, selectforeground=HIGHLIGHT_FG, insertbackground=TEXT_COLOR)
        self.hex_v_scroll = ttk.Scrollbar(hex_frame, orient=tk.VERTICAL, command=self._scroll_views, style="Dark.Vertical.TScrollbar")
        self.hex_text['yscrollcommand'] = self._on_scroll; self.hex_text.grid(row=0, column=0, sticky="nsew"); self.hex_v_scroll.grid(row=0, column=1, sticky="ns")

        ascii_frame = ttk.Frame(self, style="Dark.TFrame"); ascii_frame.grid(row=1, column=2, sticky="nsew")
        ascii_frame.grid_rowconfigure(0, weight=1); ascii_frame.grid_columnconfigure(0, weight=1)
        self.ascii_text = tk.Text(ascii_frame, width=self.BYTES_PER_ROW + 2, height=20, wrap=tk.NONE, undo=True, maxundo=50, font=self.hex_font, bg=WIDGET_BG, fg=TEXT_COLOR, relief=tk.FLAT, bd=0, selectbackground=HIGHLIGHT_BG, selectforeground=HIGHLIGHT_FG, insertbackground=TEXT_COLOR)
        self.ascii_text['yscrollcommand'] = self._on_scroll; self.ascii_text.grid(row=0, column=0, sticky="nsew")

        # self.hex_text.tag_configure("nullbyte", foreground=HEX_NULL_FG) # Removed null byte graying
        self.ascii_text.tag_configure("nonprintable", foreground=ASCII_NONPRINT_FG)
        self.hex_text.tag_configure("edited", foreground=EDITED_FG); self.ascii_text.tag_configure("edited", foreground=EDITED_FG)

        self.hex_text.bind("<KeyRelease>", lambda e: self.schedule_update(e, 'hex')); self.ascii_text.bind("<KeyRelease>", lambda e: self.schedule_update(e, 'ascii'))
        self.hex_text.bind("<<Modified>>", lambda e: self.on_modified(self.hex_text)); self.ascii_text.bind("<<Modified>>", lambda e: self.on_modified(self.ascii_text))

    def show_toolbar(self):
        self.apply_btn.pack_forget(); self.popout_btn.pack_forget(); self.popin_btn.pack_forget()
        if self.is_popup: self.apply_btn.pack(side=tk.LEFT, padx=5, pady=2); self.popin_btn.pack(side=tk.RIGHT, padx=5, pady=2)
        else: self.popout_btn.pack(side=tk.RIGHT, padx=5, pady=2)
    def on_modified(self, widget):
        if widget.edit_modified(): self.apply_btn.config(state=tk.NORMAL if self.is_popup else tk.DISABLED); widget.edit_modified(False)
    def _on_scroll(self, *args):
        if self._syncing_scroll: return
        self._syncing_scroll = True
        # Determine the fraction from the arguments provided by Tkinter
        fraction = 0.0
        if args[0] == 'moveto': fraction = float(args[1])
        elif args[0] == 'scroll': fraction = self.hex_text.yview()[0] # Get current top fraction if scrolled by units/pages
        else: # Should be the fraction from yscrollcommand
             try: fraction = float(args[0])
             except (ValueError, IndexError): pass # Ignore if invalid args

        # Apply scroll to all linked widgets
        self.addr_text.yview_moveto(fraction); self.hex_text.yview_moveto(fraction); self.ascii_text.yview_moveto(fraction)
        # Update the scrollbar itself to reflect the final position
        self.hex_v_scroll.set(fraction, self.hex_text.yview()[1]) # Use fraction and bottom edge
        self._syncing_scroll = False

    def _scroll_views(self, *args):
         if self._syncing_scroll: return
         self._syncing_scroll = True; self.addr_text.yview(*args); self.hex_text.yview(*args); self.ascii_text.yview(*args)
         self._syncing_scroll = False
    def clear(self):
        self.current_entry = None; self._raw_data = bytearray()
        for widget in [self.addr_text, self.hex_text, self.ascii_text]: widget.config(state=tk.NORMAL); widget.delete('1.0', tk.END); widget.config(state=tk.DISABLED)
        self.hex_text.edit_reset(); self.ascii_text.edit_reset(); self.apply_btn.config(state=tk.DISABLED)
        if not self.is_popup: self.app.update_button_states()
    def load_data(self, entry, data: bytes):
        self.clear();
        if data is None: data = b''
        self.current_entry = entry; self._raw_data = bytearray(data)
        self.app.log_message(f"HexEditor: Displaying {len(data):,} bytes for {entry.get_full_name()}", "DEBUG")
        addr_lines, hex_lines_data, ascii_lines_data = [], [], []
        for i in range(0, len(data) if data else 0, self.BYTES_PER_ROW):
            chunk = data[i:min(i + self.BYTES_PER_ROW, len(data))]; addr_lines.append(f"{i:08X}: ")
            hex_row_parts, tags_hex, col = [], [], 0
            for j in range(self.BYTES_PER_ROW):
                if j < len(chunk): byte_val = chunk[j]; hex_byte = f"{byte_val:02X}"; hex_row_parts.append(hex_byte);
                else: hex_row_parts.append("  ");
                # REMOVED: if j < len(chunk) and byte_val == 0: tags_hex.append(("nullbyte", col, col + 2))
                col += 2
                if (j + 1) % self.BYTES_PER_GROUP == 0 and j < self.BYTES_PER_ROW - 1: hex_row_parts.append(" "); col += 1
            hex_lines_data.append(("".join(hex_row_parts), tags_hex))
            ascii_row, tags_ascii = "", []
            for j, byte_val in enumerate(chunk):
                try: char = chunk[j:j+1].decode('cp1252'); char = char if char.isprintable() and ord(char)>=32 else '.'
                except: char = '.'
                ascii_row += char;
                if char == '.': tags_ascii.append(("nonprintable", j, j + 1))
            ascii_lines_data.append((ascii_row, tags_ascii))
        for widget in [self.addr_text, self.hex_text, self.ascii_text]: widget.config(state=tk.NORMAL); widget.delete('1.0', tk.END)
        self.addr_text.insert('1.0', "\n".join(addr_lines))
        for idx, (line, tags) in enumerate(hex_lines_data): self.hex_text.insert(f"{idx+1}.0", line+"\n"); [self.hex_text.tag_add(tag, f"{idx+1}.{sc}", f"{idx+1}.{ec}") for tag,sc,ec in tags]
        for idx, (line, tags) in enumerate(ascii_lines_data): self.ascii_text.insert(f"{idx+1}.0", line+"\n"); [self.ascii_text.tag_add(tag, f"{idx+1}.{sc}", f"{idx+1}.{ec}") for tag,sc,ec in tags]
        self._scroll_views('moveto', '0.0'); self.hex_text.config(state=tk.NORMAL); self.ascii_text.config(state=tk.NORMAL); self.addr_text.config(state=tk.DISABLED)
        self.hex_text.edit_reset(); self.ascii_text.edit_reset(); self.hex_text.edit_modified(False); self.ascii_text.edit_modified(False)
        self.apply_btn.config(state=tk.DISABLED)
        if not self.is_popup: self.app.update_button_states()

    def schedule_update(self, event, source):
        if self._edit_debounce: self.after_cancel(self._edit_debounce)
        if event.keysym in ('Shift_L', 'Shift_R', 'Control_L', 'Control_R', 'Alt_L', 'Alt_R'): return
        self._edit_debounce = self.after(300, lambda s=source: self.handle_edit(s))

    def handle_edit(self, source):
        if not self.current_entry: return; self._edit_debounce = None
        widget = self.hex_text if source == 'hex' else self.ascii_text
        try:
            content = widget.get('1.0', tk.END + "-1c")
            lines = content.split('\n')
        except Exception as e: self.app.log_message(f"Hex Editor: Error getting text: {e}", "ERROR"); return

        new_byte_list = bytearray()
        original_data_len = len(self._raw_data)
        edited_offsets = set() # Track offsets that were changed in this pass

        if source == 'hex':
            line_offset = 0
            for line_idx, line in enumerate(lines):
                hex_bytes_str = "".join(c for c in line if c in '0123456789abcdefABCDEF')
                byte_index_in_line = 0
                for j in range(0, len(hex_bytes_str), 2):
                    byte_hex = hex_bytes_str[j:j+2]; current_offset = line_offset + byte_index_in_line
                    if len(byte_hex) == 2:
                        try: new_byte_val = int(byte_hex, 16)
                        except ValueError: self.app.log_message(f"Invalid hex '{byte_hex}' line {line_idx+1}", "WARN"); new_byte_val = self._raw_data[current_offset] if current_offset < original_data_len else 0;
                    else: new_byte_val = self._raw_data[current_offset] if current_offset < original_data_len else 0 # Incomplete pair
                    if current_offset < original_data_len and self._raw_data[current_offset] != new_byte_val: edited_offsets.add(current_offset)
                    new_byte_list.append(new_byte_val); byte_index_in_line += 1
                    if len(new_byte_list) >= original_data_len: break # No insert
                line_offset += self.BYTES_PER_ROW
                if len(new_byte_list) >= original_data_len: break
            # Pad if needed (user deleted chars)
            if len(new_byte_list) < original_data_len:
                new_byte_list.extend(self._raw_data[len(new_byte_list):])

        elif source == 'ascii':
            line_offset = 0
            for line_idx, line in enumerate(lines):
                for j in range(self.BYTES_PER_ROW):
                    current_offset = line_offset + j
                    if current_offset >= original_data_len: break
                    if j < len(line): char = line[j];
                    else: new_byte_list.append(self._raw_data[current_offset]); continue # Line shorter
                    try: new_byte_val = char.encode('cp1252')[0]
                    except: new_byte_val = ord('.')
                    if self._raw_data[current_offset] != new_byte_val: edited_offsets.add(current_offset)
                    new_byte_list.append(new_byte_val)
                line_offset += self.BYTES_PER_ROW
                if current_offset >= original_data_len -1: break
            # Pad if needed
            if len(new_byte_list) < original_data_len:
                new_byte_list.extend(self._raw_data[len(new_byte_list):])

        if bytes(new_byte_list) != self._raw_data:
             self.app.log_message(f"Hex data modified ({len(new_byte_list)} bytes). Staging.", "DEBUG")
             self._raw_data = new_byte_list
             self.app.mark_dirty(True); self.current_entry.data_to_write = bytes(self._raw_data); self.current_entry.is_dirty = True
             self.update_view_from_data('ascii' if source == 'hex' else 'hex', edited_offsets)
             self.apply_btn.config(state=tk.NORMAL if self.is_popup else tk.DISABLED)
        else: self.app.log_message("Hex content unchanged after parsing.", "DEBUG")
        widget.edit_modified(False) # Reset modified flag after processing

    def update_view_from_data(self, view_to_update, edited_offsets=None):
        if edited_offsets is None: edited_offsets = set()
        if not self.current_entry: return
        self.app.log_message(f"Refreshing {view_to_update} view...", "DEBUG")
        hex_scroll = self.hex_text.yview(); ascii_scroll = self.ascii_text.yview()
        self.hex_text.unbind("<KeyRelease>"); self.ascii_text.unbind("<KeyRelease>")
        self.hex_text.unbind("<<Modified>>"); self.ascii_text.unbind("<<Modified>>")

        widget = self.hex_text if view_to_update == 'hex' else self.ascii_text
        widget.config(state=tk.NORMAL); widget.delete('1.0', tk.END)
        widget.tag_remove("edited", "1.0", tk.END) # Clear old edited tags

        current_line = 1
        for i in range(0, len(self._raw_data), self.BYTES_PER_ROW):
            chunk = self._raw_data[i:min(i + self.BYTES_PER_ROW, len(self._raw_data))]
            line_content, tags = "", []
            if view_to_update == 'hex':
                hex_row_parts, col = [], 0
                for j in range(self.BYTES_PER_ROW):
                    current_offset = i + j
                    if j < len(chunk): byte_val = chunk[j]; hex_byte = f"{byte_val:02X}"; hex_row_parts.append(hex_byte);
                    else: hex_row_parts.append("  ");
                    # if j < len(chunk) and byte_val == 0: tags.append(("nullbyte", col, col + 2)) # Removed nullbyte tag
                    if current_offset in edited_offsets: tags.append(("edited", col, col + 2))
                    col += 2
                    if (j + 1) % self.BYTES_PER_GROUP == 0 and j < self.BYTES_PER_ROW - 1: hex_row_parts.append(" "); col += 1
                line_content = "".join(hex_row_parts)
            else: # ascii
                ascii_row = ""
                for j, byte_val in enumerate(chunk):
                    current_offset = i + j
                    try: char = chunk[j:j+1].decode('cp1252'); char = char if char.isprintable() and ord(char)>=32 else '.'
                    except: char = '.'
                    ascii_row += char;
                    if char == '.': tags.append(("nonprintable", j, j + 1))
                    if current_offset in edited_offsets: tags.append(("edited", j, j + 1))
                line_content = ascii_row
            start_index = f"{current_line}.0"; widget.insert(start_index, line_content + "\n")
            for tag, sc, ec in tags: widget.tag_add(tag, f"{current_line}.{sc}", f"{current_line}.{ec}")
            current_line += 1

        widget.config(state=tk.NORMAL)
        self.hex_text.yview_moveto(hex_scroll[0]); self.ascii_text.yview_moveto(ascii_scroll[0]); self.addr_text.yview_moveto(hex_scroll[0])
        self.hex_text.bind("<KeyRelease>", lambda e: self.schedule_update(e, 'hex')); self.ascii_text.bind("<KeyRelease>", lambda e: self.schedule_update(e, 'ascii'))
        self.hex_text.bind("<<Modified>>", lambda e: self.on_modified(self.hex_text)); self.ascii_text.bind("<<Modified>>", lambda e: self.on_modified(self.ascii_text))
        widget.edit_modified(False)

    def apply_changes(self):
        if self.hex_text.edit_modified(): self.handle_edit('hex')
        if self.ascii_text.edit_modified(): self.handle_edit('ascii')
        if self.current_entry and self.current_entry.is_dirty:
             self.app.log_message(f"Applied hex changes: {self.current_entry.get_full_name()}")
             self.app.mark_dirty(True); self.apply_btn.config(state=tk.DISABLED)
        else: self.app.log_message("No hex changes to apply.", "INFO")


# --- Main GUI Application ---
class MtArcToolApp:
    def __init__(self, root):
        self.root = root; self.root.title("BurgerSoftware (Kuriimu2 Python Fork) - MT ARC Tool"); self.root.geometry("1100x750"); self.root.configure(bg=BG_COLOR) # Updated title
        self.arc = MtArc(); self.is_dirty = False; self.tree_item_map = {}; self.tree_sort_column = "#0"; self.tree_sort_reverse = False; self.hex_editor_popup = None; self.tree_iid_to_entry = {}
        self.setup_styles()
        # Setup Menu
        self.menu_bar=tk.Menu(root,bg=BG_COLOR,fg=TEXT_COLOR,activebackground=HIGHLIGHT_BG,activeforeground=HIGHLIGHT_FG,relief=tk.FLAT,bd=0); self.file_menu=tk.Menu(self.menu_bar,tearoff=0,bg=BUTTON_BG,fg=TEXT_COLOR,activebackground=HIGHLIGHT_BG,activeforeground=HIGHLIGHT_FG); self.file_menu.add_command(label="Open ARC",command=self.open_arc,background=BUTTON_BG,foreground=TEXT_COLOR); self.file_menu.add_command(label="Save ARC As...",command=self.save_arc_as,state=tk.DISABLED,background=BUTTON_BG,foreground=TEXT_COLOR); self.file_menu.add_command(label="Batch Inject...",command=self.open_batch_inject_dialog,background=BUTTON_BG,foreground=TEXT_COLOR); self.file_menu.add_command(label="Batch Extract...", command=self.open_batch_extract_dialog, background=BUTTON_BG, foreground=TEXT_COLOR); self.file_menu.add_separator(background=BG_COLOR); self.file_menu.add_command(label="Exit",command=self.on_exit,background=BUTTON_BG,foreground=TEXT_COLOR); self.menu_bar.add_cascade(label="File",menu=self.file_menu); root.config(menu=self.menu_bar); root.protocol("WM_DELETE_WINDOW",self.on_exit)
        # Setup Main Layout (Horizontal Paned)
        self.main_h_pane=tk.PanedWindow(root,orient=tk.HORIZONTAL,sashrelief=tk.RAISED,sashwidth=5,bg=BG_COLOR); self.main_h_pane.pack(expand=True,fill=tk.BOTH,padx=5,pady=5)
        # Setup Tree Pane (Left)
        self.tree_frame=ttk.Frame(self.main_h_pane,style="Dark.TFrame",padding="5"); self.main_h_pane.add(self.tree_frame,stretch="never",minsize=350); self.tree_frame.grid_rowconfigure(0,weight=1); self.tree_frame.grid_columnconfigure(0,weight=1); self.tree_scroll_y=ttk.Scrollbar(self.tree_frame,orient=tk.VERTICAL,style="Dark.Vertical.TScrollbar"); self.tree_scroll_x=ttk.Scrollbar(self.tree_frame,orient=tk.HORIZONTAL,style="Dark.Horizontal.TScrollbar"); self.tree=ttk.Treeview(self.tree_frame,columns=("Size","CompSize","Offset"),show="tree headings",yscrollcommand=self.tree_scroll_y.set,xscrollcommand=self.tree_scroll_x.set,selectmode="browse",style="Dark.Treeview"); self.tree.heading("#0",text="File Path",anchor=tk.W,command=lambda:self.sort_tree_column("#0",False)); self.tree.heading("Size",text="Size",anchor=tk.E,command=lambda:self.sort_tree_column("Size",False)); self.tree.heading("CompSize",text="Comp Size",anchor=tk.E,command=lambda:self.sort_tree_column("CompSize",False)); self.tree.heading("Offset",text="Offset",anchor=tk.E,command=lambda:self.sort_tree_column("Offset",False)); self.tree.column("#0",width=300,stretch=tk.YES,anchor=tk.W); self.tree.column("Size",width=80,stretch=tk.NO,anchor=tk.E); self.tree.column("CompSize",width=80,stretch=tk.NO,anchor=tk.E); self.tree.column("Offset",width=80,stretch=tk.NO,anchor=tk.E); self.tree_scroll_y.config(command=self.tree.yview); self.tree_scroll_x.config(command=self.tree.xview); self.tree.grid(row=0,column=0,sticky="nsew"); self.tree_scroll_y.grid(row=0,column=1,sticky="ns"); self.tree_scroll_x.grid(row=1,column=0,sticky="ew"); self.tree.bind('<<TreeviewSelect>>',self.on_tree_select); self.tree.bind('<Double-1>',self.on_tree_select)
        # Setup Right Pane (Vertical Paned)
        self.right_v_pane=tk.PanedWindow(self.main_h_pane,orient=tk.VERTICAL,sashrelief=tk.RAISED,sashwidth=5,bg=BG_COLOR); self.main_h_pane.add(self.right_v_pane,stretch="always",minsize=550)
        # Setup Hex Editor Pane (Right-Top)
        self.hex_editor_frame_outer=ttk.LabelFrame(self.right_v_pane,text="Hex Editor",style="Dark.TLabelframe",padding=5); self.right_v_pane.add(self.hex_editor_frame_outer,stretch="always",minsize=300); self.hex_editor_frame_outer.grid_rowconfigure(1,weight=1); self.hex_editor_frame_outer.grid_columnconfigure(0,weight=1); self.hex_editor_view=HexEditorView(self.hex_editor_frame_outer,self,is_popup=False); self.hex_editor_view.grid(row=1,column=0,sticky="nsew")
        # Setup Log Pane (Right-Bottom)
        self.log_frame=ttk.LabelFrame(self.right_v_pane,text="Console Log",style="Dark.TLabelframe",padding="5"); self.right_v_pane.add(self.log_frame,stretch="never",minsize=150); self.log_frame.grid_rowconfigure(0,weight=1); self.log_frame.grid_columnconfigure(0,weight=1); self.log_text=tk.Text(self.log_frame,height=10,width=80,wrap=tk.WORD,state=tk.DISABLED,font=("Consolas",9) if os.name=='nt' else ("Monospace",11),bg=WIDGET_BG,fg=TEXT_COLOR,relief=tk.FLAT,bd=0,selectbackground=HIGHLIGHT_BG,selectforeground=HIGHLIGHT_FG,insertbackground=TEXT_COLOR); log_scroll=ttk.Scrollbar(self.log_frame,orient=tk.VERTICAL,command=self.log_text.yview,style="Dark.Vertical.TScrollbar"); self.log_text['yscrollcommand']=log_scroll.set; self.log_text.grid(row=0,column=0,sticky="nsew"); log_scroll.grid(row=0,column=1,sticky="ns"); self.log_text.tag_configure("timestamp",foreground="gray"); self.log_text.tag_configure("info",foreground=TEXT_COLOR); self.log_text.tag_configure("debug",foreground="cyan"); self.log_text.tag_configure("print",foreground="lightblue"); self.log_text.tag_configure("warn",foreground="yellow"); self.log_text.tag_configure("error",foreground="orange"); self.log_text.tag_configure("fatal",foreground="red",font=(("Consolas",10,"bold") if os.name=='nt' else ("Monospace",12,"bold")))
        # Setup Button Bar
        self.button_frame=ttk.Frame(root,style="Dark.TFrame",padding=(5,0,5,5)); self.button_frame.pack(fill=tk.X,side=tk.BOTTOM); self.extract_selected_btn=ttk.Button(self.button_frame,text="Extract Selected",command=self.extract_selected,state=tk.DISABLED,style="Dark.TButton"); self.extract_all_btn=ttk.Button(self.button_frame,text="Extract All",command=self.extract_all,state=tk.DISABLED,style="Dark.TButton"); self.add_files_btn=ttk.Button(self.button_frame,text="Add Files...",command=self.add_files,state=tk.DISABLED,style="Dark.TButton"); self.remove_selected_btn=ttk.Button(self.button_frame,text="Remove Selected",command=self.remove_selected,state=tk.DISABLED,style="Dark.TButton"); self.replace_selected_btn=ttk.Button(self.button_frame,text="Replace Selected...",command=self.replace_selected,state=tk.DISABLED,style="Dark.TButton"); self.extract_selected_btn.pack(side=tk.LEFT,padx=5,pady=5); self.extract_all_btn.pack(side=tk.LEFT,padx=5,pady=5); self.add_files_btn.pack(side=tk.LEFT,padx=5,pady=5); self.remove_selected_btn.pack(side=tk.LEFT,padx=5,pady=5); self.replace_selected_btn.pack(side=tk.LEFT,padx=5,pady=5)
        # Setup Status Bar
        self.status_var=tk.StringVar(); self.status_bar=ttk.Label(root,textvariable=self.status_var,relief=tk.FLAT,anchor=tk.W,padding=(5,3),style="StatusBar.TLabel",background=STATUS_BAR_BG,foreground=TEXT_COLOR); self.status_bar.pack(side=tk.BOTTOM,fill=tk.X)
        self.redirect_print(); self.arc.set_logger(self.log_message); self.set_status("Ready. Open an ARC file."); self.log_message("BurgerSoftware (Kuriimu2 Python Fork) - MT ARC Tool started.",level="INFO"); self.update_button_states()

    def setup_styles(self):
        # ... (Style setup - Unchanged, uses larger font) ...
        style = ttk.Style(self.root); style.theme_use('clam')
        try:
            default_font = tkinter.font.nametofont("TkDefaultFont"); default_font.configure(size=default_font['size'] + 1)
            text_font = tkinter.font.nametofont("TkTextFont"); text_font.configure(size=text_font['size'] + 1)
            fixed_font = tkinter.font.nametofont("TkFixedFont"); fixed_font.configure(size=fixed_font['size'] + 1)
        except tk.TclError as font_error: self.log_message(f"Could not configure fonts: {font_error}", "WARN"); default_font = tkinter.font.Font(family="Segoe UI", size=10)
        style.configure('.', background=BG_COLOR, foreground=TEXT_COLOR, fieldbackground=INPUT_BG, bordercolor=BUTTON_BORDER, lightcolor=WIDGET_BG, darkcolor=BG_COLOR, font=default_font)
        style.map('.', background=[('active',HIGHLIGHT_BG), ('disabled','#555555')], foreground=[('active',HIGHLIGHT_FG), ('disabled','#999999')])
        style.configure("Dark.TFrame", background=BG_COLOR); style.configure("Dark.TLabelframe", background=BG_COLOR, bordercolor=TEXT_COLOR, relief=tk.GROOVE); style.configure("Dark.TLabelframe.Label", background=BG_COLOR, foreground=TEXT_COLOR)
        style.configure("Dark.TButton", background=BUTTON_BG, foreground=BUTTON_FG, relief=tk.RAISED, borderwidth=1, bordercolor=BUTTON_BORDER, padding=6, focuscolor=HIGHLIGHT_FG, font=default_font); style.map("Dark.TButton", background=[('pressed',BUTTON_ACTIVE_BG), ('active',HIGHLIGHT_BG)], foreground=[('pressed',HIGHLIGHT_FG), ('active',HIGHLIGHT_FG)], relief=[('pressed',tk.SUNKEN)])
        style.configure("Dark.Treeview", background=WIDGET_BG, foreground=TEXT_COLOR, fieldbackground=WIDGET_BG, rowheight=24, font=default_font); style.map("Dark.Treeview", background=[('selected',HIGHLIGHT_BG)], foreground=[('selected',HIGHLIGHT_FG)])
        style.configure("Dark.Treeview.Heading", background=HEADER_BG, foreground=HEADER_FG, relief=tk.RAISED, padding=(6,4), font=default_font); style.map("Dark.Treeview.Heading", background=[('active',HIGHLIGHT_BG)])
        style.configure("Dark.Vertical.TScrollbar", background=BUTTON_BG, troughcolor=WIDGET_BG, bordercolor=BUTTON_BORDER, arrowcolor=TEXT_COLOR); style.map("Dark.Vertical.TScrollbar", background=[('active',HIGHLIGHT_BG)])
        style.configure("Dark.Horizontal.TScrollbar", background=BUTTON_BG, troughcolor=WIDGET_BG, bordercolor=BUTTON_BORDER, arrowcolor=TEXT_COLOR); style.map("Dark.Horizontal.TScrollbar", background=[('active',HIGHLIGHT_BG)])
        style.configure("TEntry", fieldbackground=INPUT_BG, foreground=TEXT_COLOR, insertcolor=TEXT_COLOR, bordercolor=BUTTON_BORDER, borderwidth=1, relief=tk.FLAT, font=default_font)
        style.configure("StatusBar.TLabel", background=STATUS_BAR_BG, foreground=TEXT_COLOR, padding=(5,3), relief=tk.FLAT, font=default_font)
        style.configure("Dialog.TFrame", background=BG_COLOR); style.configure("Dialog.TLabel", background=BG_COLOR, foreground=TEXT_COLOR); style.configure("Dialog.TLabelframe", background=BG_COLOR, bordercolor=TEXT_COLOR); style.configure("Dialog.TLabelframe.Label", background=BG_COLOR, foreground=TEXT_COLOR)
        style.configure("Dialog.TButton", background=BUTTON_BG, foreground=BUTTON_FG, bordercolor=BUTTON_BORDER); style.map("Dialog.TButton", background=[('pressed',BUTTON_ACTIVE_BG), ('active',HIGHLIGHT_BG)])
        style.configure("Dialog.TEntry", fieldbackground=INPUT_BG, foreground=TEXT_COLOR, insertcolor=TEXT_COLOR); style.configure("Dialog.Vertical.TScrollbar", background=BUTTON_BG, troughcolor=WIDGET_BG); style.map("Dialog.Vertical.TScrollbar", background=[('active',HIGHLIGHT_BG)])

    def log_message(self, message, level="INFO"):
        # ... (log_message - unchanged) ...
        try: timestamp = time.strftime("%H:%M:%S"); tag = level.lower(); self.log_text.config(state=tk.NORMAL); self.log_text.insert(tk.END, f"[{timestamp} {level}] ", ("timestamp", tag)); self.log_text.insert(tk.END, f"{message}\n", (tag,)); self.log_text.see(tk.END); self.log_text.config(state=tk.DISABLED); self.root.update_idletasks()
        except Exception as e: print(f"LOG ERROR: {e}"); print(f"Original ({level}): {message}")
    class PrintRedirector:
        # ... (PrintRedirector - unchanged) ...
        def __init__(self, log_method): self.log_method = log_method; self.buffer = ""
        def write(self, message): self.buffer += message;
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
        if dirty == self.is_dirty: return; self.is_dirty = dirty; title = "BurgerSoftware (Kuriimu2 Python Fork) - MT ARC Tool"; # Updated title
        if self.arc.source_filepath: title += f" - {self.arc.source_filepath.name}"
        elif self.arc.entries: title += " - [New ARC]"
        if self.is_dirty: title += "*"; self.root.title(title); self.update_button_states()
    def update_button_states(self):
        # ... (update_button_states - unchanged) ...
        has_entries = bool(self.arc.entries); has_selection = bool(self.tree.selection())
        single_file_selected = False; can_popout = False
        if has_selection:
             iid = self.tree.selection()[0];
             try: tags = self.tree.item(iid, "tags")
             except tk.TclError: tags = ()
             if tags and 'file' in tags: single_file_selected = (len(self.tree.selection()) == 1); can_popout = True
        can_save = has_entries or self.is_dirty
        self.file_menu.entryconfig("Save ARC As...", state=tk.NORMAL if can_save else tk.DISABLED)
        self.extract_selected_btn.config(state=tk.NORMAL if single_file_selected else tk.DISABLED)
        self.extract_all_btn.config(state=tk.NORMAL if has_entries else tk.DISABLED)
        self.add_files_btn.config(state=tk.NORMAL if (self.arc.source_filepath or has_entries) else tk.DISABLED)
        self.remove_selected_btn.config(state=tk.NORMAL if single_file_selected else tk.DISABLED)
        self.replace_selected_btn.config(state=tk.NORMAL if single_file_selected else tk.DISABLED)
        if hasattr(self, 'hex_editor_view') and hasattr(self.hex_editor_view, 'popout_btn'): self.hex_editor_view.popout_btn.config(state=tk.NORMAL if can_popout and not self.hex_editor_popup else tk.DISABLED)

    def populate_tree(self):
        # ... (populate_tree - unchanged) ...
        for item in self.tree.get_children(): self.tree.delete(item); self.tree_item_map = {}; self.tree_iid_to_entry = {}
        if not self.arc.entries: self.update_button_states(); return
        sorted_entries = sorted(self.arc.entries, key=lambda e: e.get_full_name())
        for entry in sorted_entries:
            full_path = entry.get_full_name().replace('\\', '/'); path_parts = full_path.split('/'); filename = path_parts[-1]; parent_iid = ""
            current_path = ""
            for i, part in enumerate(path_parts[:-1]):
                current_path = f"{current_path}/{part}" if current_path else part
                if current_path not in self.tree_item_map: folder_iid = self.tree.insert(parent_iid, tk.END, text=part, open=False, tags=('folder',)); self.tree_item_map[current_path] = folder_iid; parent_iid = folder_iid
                else: parent_iid = self.tree_item_map[current_path]
            size=entry.get_decompressed_size(self.arc.platform); comp_size_val=entry.comp_size if entry.comp_size!=-1 else -1; offset_val=entry.offset if entry.offset!=-1 else -1
            comp_size_disp=f"{comp_size_val:,}" if comp_size_val!=-1 else "N/A"; offset_disp=f"{offset_val:#0X}" if offset_val!=-1 else "N/A"
            file_iid = id(entry); self.tree_iid_to_entry[file_iid] = entry # Store mapping
            self.tree.insert(parent_iid, tk.END, iid=file_iid, text=filename, values=(f"{size:,}", comp_size_disp, offset_disp), tags=('file',)) # Use file tag only
        self.update_button_states()
    def get_selected_entries(self) -> list[IMtEntryPy]:
        # ... (get_selected_entries - unchanged) ...
        selected_iids = self.tree.selection(); entries = []
        for iid_str in selected_iids:
            try: iid_int = int(iid_str);
            except ValueError: continue
            if iid_int in self.tree_iid_to_entry: entries.append(self.tree_iid_to_entry[iid_int])
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
                tags=self.tree.item(child_iid,"tags"); is_folder='folder' in tags;
                iid_int = int(child_iid) # Convert iid string to int
                entry_obj = self.tree_iid_to_entry.get(iid_int) if not is_folder else None # Use mapping
                item_text=self.tree.item(child_iid,"text"); name_val=item_text; size_val=-1; compsize_val=-1; offset_val=-1
                if entry_obj:
                    try: size_val_str=self.tree.set(child_iid,"Size").replace(',',''); size_val=int(size_val_str) if size_val_str.isdigit() else -1
                    except: pass
                    try: compsize_str=self.tree.set(child_iid,"CompSize").replace(',',''); compsize_val=int(compsize_str) if compsize_str.isdigit() else -1
                    except: pass
                    try: offset_str=self.tree.set(child_iid,"Offset"); offset_val=int(offset_str,16) if offset_str.startswith('0x') else -1
                    except: pass
                sort_val=name_val
                if sort_key=="size": sort_val=size_val
                elif sort_key=="compsize": sort_val=compsize_val
                elif sort_key=="offset": sort_val=offset_val
                items_data.append({'iid':child_iid, 'sort_key':sort_val, 'is_folder':is_folder})
            try: items_data.sort(key=lambda x:(not x['is_folder'], x['sort_key']), reverse=reverse)
            except TypeError: self.log_message(f"Cannot sort col '{col}' mixed types under '{parent_iid or 'root'}'. Sort by name.", "WARN"); items_data.sort(key=lambda x:(not x['is_folder'], self.tree.item(x['iid'],"text")), reverse=reverse)
            for i, item_info in enumerate(items_data): self.tree.move(item_info['iid'], parent_iid, i)
        self.tree.heading(col, command=lambda: self.sort_tree_column(col, not reverse))

    def on_tree_select(self, event=None): # Updated with fix
        self.log_message(f"on_tree_select triggered (Event: {event})", "DEBUG")
        selected_iids = self.tree.selection()
        self.log_message(f"  Selected IDs tuple: {selected_iids}", "DEBUG")
        if not selected_iids: self.log_message(f"  No selection.", "DEBUG"); self.hex_editor_view.clear(); self.update_button_states(); return
        iid_str = selected_iids[0]
        try: iid_int = int(iid_str); self.log_message(f"  Processing iid: {iid_str} (int: {iid_int})", "DEBUG")
        except ValueError: self.log_message(f"  Bad iid '{iid_str}'.", "ERROR"); self.hex_editor_view.clear(); self.update_button_states(); return
        if iid_int in self.tree_iid_to_entry: # Check mapping
            entry = self.tree_iid_to_entry[iid_int]; self.log_message(f"  Selected is file: {entry.get_full_name()}", "DEBUG")
            self.log_message(f"Loading '{entry.get_full_name()}' into Hex Editor..."); self.set_status(f"Loading {entry.get_full_name()}...")
            try:
                self.log_message(f"  Calling get_entry_data...", "DEBUG"); data = self.arc.get_entry_data(entry, compressed=False)
                data_len = len(data) if data is not None else "None"; self.log_message(f"  get_entry_data returned length: {data_len}", "DEBUG")
                if data is None: messagebox.showerror("Load Error", f"Failed get data {entry.get_full_name()}."); self.hex_editor_view.clear()
                else: self.log_message(f"  Calling hex_editor_view.load_data...", "DEBUG"); self.hex_editor_view.load_data(entry, data); self.log_message(f"  Finished hex_editor_view.load_data.", "DEBUG")
                self.set_status(f"Viewing {entry.get_full_name()}")
            except Exception as e: self.log_message(f"Error loading data for hex view: {e}\n{traceback.format_exc()}", "ERROR"); messagebox.showerror("Load Error", f"Failed load data:\n{e}"); self.hex_editor_view.clear(); self.set_status("Error loading data.")
        else:
            try: item_text = self.tree.item(iid_str, "text")
            except tk.TclError: item_text = f"[Item {iid_str} not found]"
            self.log_message(f"  Selected item '{item_text}' (iid: {iid_str}) is not a file entry.", "DEBUG"); self.hex_editor_view.clear(); self.set_status("Select a file to view hex.")
        self.update_button_states()
    def popout_hex_editor(self):
        if self.hex_editor_popup or not self.hex_editor_view.current_entry: self.log_message("Hex editor already popped out or no file loaded.", "WARN"); return
        self.hex_editor_popup = tk.Toplevel(self.root); self.hex_editor_popup.title(f"Hex Editor - {self.hex_editor_view.current_entry.get_full_name()}"); self.hex_editor_popup.geometry("800x600"); self.hex_editor_popup.configure(bg=BG_COLOR)
        self.hex_editor_popup.transient(self.root); self.hex_editor_popup.protocol("WM_DELETE_WINDOW", self.popin_hex_editor)
        self.hex_editor_view.grid_forget(); self.hex_editor_view.master = self.hex_editor_popup; self.hex_editor_view.is_popup = True
        popup_frame = ttk.Frame(self.hex_editor_popup, style="Dark.TFrame", padding=5); popup_frame.pack(expand=True, fill=tk.BOTH); popup_frame.grid_rowconfigure(1, weight=1); popup_frame.grid_columnconfigure(0, weight=1)
        self.hex_editor_view.hex_toolbar.grid_forget(); self.hex_editor_view.hex_toolbar.master = popup_frame; self.hex_editor_view.hex_toolbar.grid(row=0, column=0, sticky=tk.EW, pady=(0, 5))
        self.hex_editor_view.show_toolbar(); self.hex_editor_view.grid(row=1, column=0, sticky="nsew")
        self.log_message("Hex editor popped out."); self.update_button_states()
    def popin_hex_editor(self):
        if not self.hex_editor_popup: return
        if self.hex_editor_view.current_entry and (self.hex_editor_view.hex_text.edit_modified() or self.hex_editor_view.ascii_text.edit_modified()):
             if messagebox.askyesno("Apply Changes?", "Apply changes before popping in?"): self.apply_hex_changes()
             else: self.log_message("Discarding hex editor changes.", "WARN"); self.on_tree_select()
        self.hex_editor_view.grid_forget(); self.hex_editor_view.master = self.hex_editor_frame_outer; self.hex_editor_view.is_popup = False
        self.hex_editor_view.hex_toolbar.grid_forget(); self.hex_editor_view.hex_toolbar.master = self.hex_editor_frame_outer; self.hex_editor_view.hex_toolbar.grid(row=0, column=0, sticky=tk.EW, pady=(0, 5))
        self.hex_editor_view.show_toolbar(); self.hex_editor_view.grid(row=1, column=0, sticky="nsew")
        self.hex_editor_popup.destroy(); self.hex_editor_popup = None; self.log_message("Hex editor popped in."); self.update_button_states()
    def apply_hex_changes(self):
        if self.hex_editor_view and self.hex_editor_view.current_entry: self.hex_editor_view.apply_changes()
        else: self.log_message("Cannot apply hex changes: editor not ready.", "WARN")

    # --- Action Methods ---
    def open_arc(self):
        if self.is_dirty:
             if not messagebox.askyesno("Unsaved Changes", "Discard unsaved changes and open a new file?"): return
        filepath = filedialog.askopenfilename(title="Open MT ARC File", filetypes=(("ARC files", "*.arc"), ("All files", "*.*")))
        if not filepath: return
        try:
            self.set_status(f"Loading {os.path.basename(filepath)}...")
            if self.arc: self.arc.close(); self.hex_editor_view.clear()
            self.arc = MtArc(); self.arc.set_logger(self.log_message)
            self.arc.load(filepath)
            self.populate_tree(); self.set_status(f"Loaded {len(self.arc.entries)} files from {os.path.basename(filepath)}")
            self.mark_dirty(False)
        except Exception as e: self.log_message(f"Failed load {filepath}: {e}", "ERROR"); messagebox.showerror("Error Loading", f"Failed:\n{e}\n\nSee log."); self.arc = MtArc(); self.arc.set_logger(self.log_message); self.populate_tree(); self.mark_dirty(False)
        finally: self.update_button_states()
    def save_arc_as(self):
        if not self.arc.entries and not self.is_dirty: messagebox.showwarning("Save Error", "No changes or entries to save."); return
        if self.hex_editor_view and self.hex_editor_view.current_entry and (self.hex_editor_view.hex_text.edit_modified() or self.hex_editor_view.ascii_text.edit_modified()):
            self.log_message("Applying hex changes before saving...", "INFO"); self.apply_hex_changes()
        initial_name = self.arc.source_filepath.name if self.arc.source_filepath else "Untitled.arc"
        filepath = filedialog.asksaveasfilename(title="Save ARC As", initialfile=initial_name, defaultextension=".arc", filetypes=(("ARC files", "*.arc"), ("All files", "*.*")))
        if not filepath: return
        try:
            self.set_status(f"Saving to {os.path.basename(filepath)}..."); start_time = time.time()
            self.arc.save(filepath); end_time = time.time()
            self.set_status(f"Saved {len(self.arc.entries)} files to {os.path.basename(filepath)} in {end_time - start_time:.2f}s")
            self.mark_dirty(False); self.populate_tree()
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
        dest_folder = "" # TODO: Ask user for dest folder
        self.set_status("Adding files..."); self.log_message(f"Adding {len(files_to_add)} file(s)...")
        added_count = 0; start_time = time.time()
        for f_path in files_to_add:
            archive_path = os.path.join(dest_folder, os.path.basename(f_path)).replace('\\', '/')
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
        removed_count = 0; start_time = time.time(); removed_current_hex = False
        for entry in selected_entries:
             if self.hex_editor_view.current_entry == entry: removed_current_hex = True
             if self.arc.remove_entry(entry): self.log_message(f"Removed '{entry.get_full_name()}'"); removed_count += 1
        end_time = time.time()
        if removed_count > 0:
            if removed_current_hex: self.hex_editor_view.clear()
            self.populate_tree(); self.mark_dirty(True); msg = f"Removed {removed_count} file(s) in {end_time - start_time:.2f}s. Save required."; self.log_message(msg); self.set_status(msg, duration_ms=5000)
    def replace_selected(self):
        selected_items = self.tree.selection()
        if not selected_items: messagebox.showwarning("Replace", "No file selected."); return
        if len(selected_items) > 1: messagebox.showwarning("Replace", "Select only one file."); return
        iid = selected_items[0];
        try: tags = self.tree.item(iid, "tags")
        except tk.TclError: messagebox.showwarning("Replace", "Selected item no longer exists."); return
        if not tags or 'file' not in tags or len(tags) < 2 or not isinstance(tags[1], IMtEntryPy): messagebox.showwarning("Replace", "Selection is not a file."); return
        entry_to_replace = tags[1]
        file_to_import = filedialog.askopenfilename(title=f"Replace '{entry_to_replace.get_full_name()}'")
        if not file_to_import: return
        self.log_message(f"Replacing '{entry_to_replace.get_full_name()}' with '{file_to_import}'...")
        try:
            start_time = time.time()
            with open(file_to_import, 'rb') as f_rep: new_data = f_rep.read()
            if self.arc.replace_entry_data(entry_to_replace, new_data):
                end_time = time.time()
                if self.hex_editor_view.current_entry == entry_to_replace: self.hex_editor_view.load_data(entry_to_replace, new_data) # Reload hex view
                self.populate_tree(); self.mark_dirty(True); msg = f"Staged replacement '{entry_to_replace.get_full_name()}' in {end_time - start_time:.2f}s. Save required."; self.log_message(msg); self.set_status(msg, duration_ms=5000)
            else: self.set_status(f"Replacement failed.", duration_ms=3000)
        except Exception as e: self.log_message(f"Replace failed: {e}", "ERROR"); messagebox.showerror("Replace Error", f"Failed:\n{e}"); self.set_status("Replacement error.")

    # --- Batch Operations ---
    def open_batch_inject_dialog(self):
        if self.is_dirty: messagebox.showwarning("Unsaved Changes", "Save or discard changes before batch op."); return
        if self.arc and self.arc.source_filepath: self.log_message("Closing current ARC before batch op."); self.arc.close(); self.arc = MtArc(); self.arc.set_logger(self.log_message); self.populate_tree(); self.mark_dirty(False); self.hex_editor_view.clear()
        dialog = BatchInjectDialog(self); dialog.wait_window()

    def run_batch_injection(self, original_dir, modified_base_dir, output_dir, log_callback):
        # ... (run_batch_injection - logic unchanged) ...
        arc_files_processed=0; arc_files_skipped=0; total_files_replaced=0; total_files_failed=0; start_batch_time=time.time()
        original_path=Path(original_dir); modified_base_path=Path(modified_base_dir); output_path=Path(output_dir)
        try: arc_filepaths=list(original_path.glob('*.arc'))
        except Exception as e: log_callback(f"[FATAL] Scan ARCs failed {original_path}: {e}"); return
        log_callback(f"Found {len(arc_filepaths)} ARCs in {original_path}")
        if not arc_filepaths: log_callback("No ARCs found."); return
        for i, arc_filepath in enumerate(arc_filepaths):
            arc_filename=arc_filepath.name; modified_arc_folder=modified_base_path/arc_filename
            log_callback(f"\n--- Processing ARC {i+1}/{len(arc_filepaths)}: {arc_filename} ---")
            if not modified_arc_folder.is_dir(): log_callback(f"  [SKIP] Mod folder not found: {modified_arc_folder}"); arc_files_skipped+=1; continue
            batch_arc=MtArc(); batch_arc.set_logger(lambda msg, level="INFO": log_callback(f"    {msg}", level))
            try: batch_arc.load(arc_filepath); log_callback(f"  Loaded original ({len(batch_arc.entries)} entries).")
            except Exception as e: log_callback(f"  [FAIL] Load {arc_filename} failed: {e}. Skipping."); arc_files_skipped+=1; continue
            files_replaced_in_arc=0; files_failed_in_arc=0; files_skipped_in_arc=0; arc_modified=False
            for entry in batch_arc.entries:
                entry_archive_path_str=entry.get_full_name().replace('\\','/'); expected_mod_filepath=modified_arc_folder/entry_archive_path_str
                if expected_mod_filepath.is_file():
                    try:
                        with open(expected_mod_filepath,'rb') as mod_f: new_data_bytes=mod_f.read()
                        if batch_arc.replace_entry_data(entry, new_data_bytes): files_replaced_in_arc+=1; arc_modified=True
                        else: files_failed_in_arc+=1
                    except Exception as read_err: log_callback(f"    [FAIL] Read mod file {expected_mod_filepath}: {read_err}"); files_failed_in_arc+=1
                else: files_skipped_in_arc+=1
            log_callback(f"  Scan done: {files_replaced_in_arc} replaced, {files_failed_in_arc} failed, {files_skipped_in_arc} skipped.")
            if arc_modified:
                output_arc_path=output_path/arc_filename; log_callback(f"  Saving modified: {output_arc_path}")
                try: batch_arc.save(output_arc_path); log_callback(f"  Saved {arc_filename}."); arc_files_processed+=1; total_files_replaced+=files_replaced_in_arc; total_files_failed+=files_failed_in_arc
                except Exception as e: log_callback(f"  [FAIL] Save error {output_arc_path}: {e}"); arc_files_skipped+=1; total_files_failed+=files_replaced_in_arc
            else: log_callback(f"  No mods needed {arc_filename}. Skipping save."); arc_files_skipped+=1
            batch_arc.close()
        end_batch_time=time.time(); log_callback("\n--- Batch Summary ---"); log_callback(f"Time: {end_batch_time - start_batch_time:.2f}s")
        log_callback(f"ARCs Saved: {arc_files_processed}"); log_callback(f"ARCs Skipped: {arc_files_skipped}")
        log_callback(f"Files Replaced: {total_files_replaced}"); log_callback(f"File Fails: {total_files_failed}")

    def open_batch_extract_dialog(self):
        """Opens the dialog for batch extraction."""
        if self.is_dirty:
             messagebox.showwarning("Unsaved Changes", "Save or discard changes before starting batch operation.")
             return
        if self.arc and self.arc.source_filepath:
             self.log_message("Closing current ARC before batch operation.")
             self.arc.close(); self.arc = MtArc(); self.arc.set_logger(self.log_message); self.populate_tree(); self.mark_dirty(False); self.hex_editor_view.clear()

        dialog = BatchExtractDialog(self) # Pass app instance
        dialog.wait_window()

    def run_batch_extraction(self, input_arc_dir, output_base_dir, log_callback):
        """Performs recursive batch extraction."""
        arc_files_processed = 0
        arc_files_failed_load = 0
        total_files_extracted = 0
        total_files_failed_extract = 0
        start_batch_time = time.time()

        input_path = Path(input_arc_dir)
        output_path = Path(output_base_dir)

        log_callback(f"Searching for *.arc files recursively in: {input_path}")
        try:
            # Use rglob to find ARC files recursively
            arc_filepaths = list(input_path.rglob('*.arc'))
        except Exception as e:
             log_callback(f"[FATAL] Error scanning for ARC files in {input_path}: {e}")
             return

        log_callback(f"Found {len(arc_filepaths)} .arc file(s).")
        if not arc_filepaths: log_callback("Nothing to extract."); return

        for i, arc_filepath in enumerate(arc_filepaths):
            # Construct output path mirroring the input structure
            try:
                relative_arc_path = arc_filepath.relative_to(input_path)
            except ValueError:
                 log_callback(f"  [WARN] Cannot determine relative path for {arc_filepath}. Skipping.")
                 arc_files_failed_load += 1
                 continue

            # Output dir will be output_base_dir / relative_path_including_arc_filename
            output_arc_extract_dir = output_path / relative_arc_path

            log_callback(f"\n--- Processing ARC {i+1}/{len(arc_filepaths)}: {relative_arc_path} ---")
            log_callback(f"  Outputting to: {output_arc_extract_dir}")

            # Ensure output directory exists for this ARC
            try:
                output_arc_extract_dir.mkdir(parents=True, exist_ok=True)
            except Exception as e:
                 log_callback(f"  [FAIL] Cannot create output directory {output_arc_extract_dir}: {e}. Skipping ARC.")
                 arc_files_failed_load += 1
                 continue

            batch_arc = MtArc()
            batch_arc.set_logger(lambda msg, level="INFO": log_callback(f"    {msg}", level)) # Indent logs
            try:
                batch_arc.load(arc_filepath)
                log_callback(f"  Loaded original ARC ({len(batch_arc.entries)} entries).")
            except Exception as e:
                log_callback(f"  [FAIL] Error loading {arc_filepath.name}: {e}. Skipping ARC.")
                arc_files_failed_load += 1
                continue

            # Extract all entries from this arc
            extracted_in_arc = 0
            failed_in_arc = 0
            log_callback(f"  Extracting files...")
            for entry in batch_arc.entries:
                if batch_arc.extract_entry(entry, str(output_arc_extract_dir)):
                    extracted_in_arc += 1
                else:
                    failed_in_arc += 1
            log_callback(f"  Extracted {extracted_in_arc}, Failed {failed_in_arc}")

            total_files_extracted += extracted_in_arc
            total_files_failed_extract += failed_in_arc
            arc_files_processed += 1
            batch_arc.close()

        # --- Final Summary ---
        end_batch_time = time.time()
        log_callback("\n--- Batch Extraction Summary ---")
        log_callback(f"Total Time: {end_batch_time - start_batch_time:.2f} seconds")
        log_callback(f"ARCs Processed: {arc_files_processed}")
        log_callback(f"ARCs Failed to Load: {arc_files_failed_load}")
        log_callback(f"Total Files Extracted: {total_files_extracted}")
        log_callback(f"Total Extraction Failures: {total_files_failed_extract}")


    def on_exit(self):
         # ... (on_exit - unchanged) ...
         if self.is_dirty:
              if not messagebox.askyesno("Exit", "Unsaved changes exist. Exit anyway?"): return
         if self.arc: self.arc.close()
         if self.hex_editor_popup:
              try: self.hex_editor_popup.destroy()
              except: pass
         self.log_message("Exiting BurgerSoftware (Kuriimu2 Python Fork).") # Updated exit message
         self.root.destroy()

# --- Batch Injection Dialog Class ---
# ... (BatchInjectDialog class - unchanged) ...
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
    def log_message(self, message, level="INFO"): # Matched signature
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
                  except Exception as e: messagebox.showerror("Error",f"Failed create output dir:\n{e}"); return
             else: return
        if Path(orig_dir).resolve()==out_path.resolve(): messagebox.showerror("Input Error","Output cannot be same as Original."); return
        if Path(mod_dir).resolve()==out_path.resolve(): messagebox.showerror("Input Error","Output cannot be same as Modified."); return
        self.log_text.config(state=tk.NORMAL); self.log_text.delete('1.0',tk.END); self.log_text.config(state=tk.DISABLED); self.log_message("Starting Batch Injection...")
        self.log_message(f"  Original: {orig_dir}"); self.log_message(f"  Modified: {mod_dir}"); self.log_message(f"  Output: {out_dir}"); self.log_message("-"*20); self.set_ui_state(False)
        try:
            # Call the method on the stored app instance now
            self.app_instance.run_batch_injection(orig_dir, mod_dir, out_dir, self.log_message)
            self.log_message("-"*20); self.log_message("Batch Finished."); messagebox.showinfo("Finished","Batch injection complete.")
        except Exception as e: self.log_message(f"\n--- BATCH FAILED ---"); self.log_message(f"Error: {e}"); self.log_message(traceback.format_exc()); messagebox.showerror("Batch Failed",f"Error:\n{e}\n\nCheck log.")
        finally: self.set_ui_state(True)
    def close_dialog(self):
         if self.is_running: messagebox.showwarning("Process Running","Wait for batch process."); return
         self.destroy()

# --- Batch Extraction Dialog Class ---
class BatchExtractDialog(tk.Toplevel):
    def __init__(self, app_instance):
        super().__init__(app_instance.root)
        self.app_instance = app_instance
        self.title("Batch Extract ARCs"); self.geometry("650x450"); self.resizable(True, True)
        self.grab_set(); self.transient(app_instance.root)
        self.main_frame = ttk.Frame(self, padding="10", style="Dialog.TFrame"); self.main_frame.pack(expand=True, fill=tk.BOTH)
        self.main_frame.grid_rowconfigure(2, weight=1); self.main_frame.grid_columnconfigure(1, weight=1) # Row 2 is log
        self.paths = {"input": tk.StringVar(), "output": tk.StringVar()}
        labels = {"input": "Input ARC Directory (Recursive):", "output": "Output Base Directory:"}
        row_num = 0
        for key, label_text in labels.items():
            ttk.Label(self.main_frame, text=label_text, style="Dialog.TLabel").grid(row=row_num, column=0, sticky=tk.W, pady=3, padx=2)
            entry = ttk.Entry(self.main_frame, textvariable=self.paths[key], width=60, style="Dialog.TEntry")
            entry.grid(row=row_num, column=1, sticky=(tk.W, tk.E), padx=5, pady=3)
            button = ttk.Button(self.main_frame, text="Browse...", style="Dialog.TButton", command=lambda k=key: self.browse_dir(k))
            button.grid(row=row_num, column=2, padx=2, pady=3); row_num += 1
        log_frame = ttk.LabelFrame(self.main_frame, text="Batch Log", padding="5", style="Dialog.TLabelframe")
        log_frame.grid(row=2, column=0, columnspan=3, sticky="nsew", pady=(10, 5)); log_frame.grid_rowconfigure(0, weight=1); log_frame.grid_columnconfigure(0, weight=1)
        self.log_text = tk.Text(log_frame, height=15, width=70, wrap=tk.WORD, state=tk.DISABLED, font=("Consolas", 9) if os.name == 'nt' else ("Monospace", 10), bg=WIDGET_BG, fg=TEXT_COLOR, relief=tk.FLAT, bd=0)
        log_scroll = ttk.Scrollbar(log_frame, orient=tk.VERTICAL, command=self.log_text.yview, style="Dialog.Vertical.TScrollbar")
        self.log_text['yscrollcommand'] = log_scroll.set; self.log_text.grid(row=0, column=0, sticky="nsew"); log_scroll.grid(row=0, column=1, sticky="ns")
        button_frame = ttk.Frame(self.main_frame, style="Dialog.TFrame"); button_frame.grid(row=3, column=0, columnspan=3, pady=(5, 0), sticky=tk.E)
        self.start_button = ttk.Button(button_frame, text="Start Batch Extract", command=self.start_extraction, style="Dialog.TButton"); self.start_button.pack(side=tk.RIGHT, padx=5)
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
    def start_extraction(self):
        in_dir = self.paths["input"].get(); out_dir = self.paths["output"].get()
        if not all([in_dir, out_dir]): messagebox.showerror("Input Error", "Please select both directories."); return
        if not Path(in_dir).is_dir(): messagebox.showerror("Input Error", f"Input ARC directory not found:\n{in_dir}"); return
        out_path = Path(out_dir)
        if not out_path.is_dir():
             if messagebox.askyesno("Create Dir?", f"Output directory does not exist:\n{out_dir}\nCreate it?"):
                  try: out_path.mkdir(parents=True, exist_ok=True)
                  except Exception as e: messagebox.showerror("Error", f"Failed create output dir:\n{e}"); return
             else: return
        self.log_text.config(state=tk.NORMAL); self.log_text.delete('1.0', tk.END); self.log_text.config(state=tk.DISABLED); self.log_message("Starting Batch Extraction...")
        self.log_message(f"  Input ARCs (Recursive): {in_dir}"); self.log_message(f"  Output Base: {out_dir}"); self.log_message("-" * 20); self.set_ui_state(False)
        try:
            # Run extraction in a separate thread to avoid freezing GUI
            thread = threading.Thread(target=self.app_instance.run_batch_extraction, args=(in_dir, out_dir, self.log_message), daemon=True)
            thread.start()
            # Optionally, monitor thread and show completion message later
            # Or just let it run and log - user sees completion in log
            self.log_message("Batch extraction started in background...") # Inform user
            # Re-enable UI immediately? Or wait? Let's wait for now in this sync version
            # If using thread: self.set_ui_state(True) here

            # --- Synchronous Version (will freeze GUI) ---
            self.app_instance.run_batch_extraction(in_dir, out_dir, self.log_message)
            self.log_message("-"*20); self.log_message("Batch Extraction Finished."); messagebox.showinfo("Finished","Batch extraction complete.")
            self.set_ui_state(True) # Re-enable UI after sync completion
            # --- End Synchronous Version ---

        except Exception as e:
            self.log_message(f"\n--- BATCH FAILED ---"); self.log_message(f"Error: {e}"); self.log_message(traceback.format_exc()); messagebox.showerror("Batch Failed",f"Error:\n{e}\n\nCheck log.")
            self.set_ui_state(True) # Ensure UI is enabled on error

    def close_dialog(self):
         if self.is_running: messagebox.showwarning("Process Running", "Wait for batch process."); return
         self.destroy()

# --- Main Execution ---
if __name__ == "__main__":
    if not _crcmod_available:
         root_check = tk.Tk(); root_check.withdraw()
         if not messagebox.askyesno("Missing Dependency", "Python library 'crcmod' required.\nInstall using:\npython -m pip install crcmod\n\nContinue anyway (extension handling will fail)?", icon='warning'): import sys; sys.exit(1)
         root_check.destroy()
    root = tk.Tk()
    app = MtArcToolApp(root)
    root.mainloop()