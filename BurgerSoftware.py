#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# BurgerSoftware (Kuriimu2 Python Fork) - MT Framework ARC Tool
# Based on analysis of Kuriimu2 C# code for MT Framework archives.
# Handles ARC archive reading, writing, extraction, and modification.
# Prerequisites: crcmod
# Install using: python -m pip install crcmod

import struct
import zlib
import io
import os
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import tkinter.font
from enum import Enum
from pathlib import Path
import inspect  # Might be needed for future TypeReader/Writer
import time
import traceback  # For logging detailed errors
from collections import defaultdict  # For folder tree
import math  # For hex editor rows
import threading  # For potentially non-blocking batch operations
import concurrent.futures
import queue
from typing import Optional, Dict, Any, Tuple, List, Set, Union, Callable

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
    def get_hash(input_string: str, encoding: str = 'utf-8') -> int:
        print("CRCMOD not found, cannot calculate hash!")
        return 0
    # Optionally: sys.exit(1) if crcmod is absolutely essential to run

# --- Color Scheme ---
BG_COLOR = '#2b2b2b'
TEXT_COLOR = '#ffebcd'        # Blanched Almond - Main text
WIDGET_BG = '#3c3f41'         # Darker Gray - Treeview/Text/Hex background
INPUT_BG = '#45494a'          # Slightly lighter gray - Entry background
BUTTON_BG = '#4d4d4d'         # Medium Gray - Button Background
BUTTON_FG = TEXT_COLOR        # Text on buttons
BUTTON_ACTIVE_BG = '#636363'  # Darker Gray - Button when pressed/active
BUTTON_BORDER = '#202020'     # Dark border for buttons
HEADER_BG = '#4d4d4d'         # Medium Gray - Treeview Header BG
HEADER_FG = TEXT_COLOR        # Text on headers
HIGHLIGHT_BG = '#556b7d'      # Steel Blue-ish Gray - Selection background
HIGHLIGHT_FG = '#ffffff'      # White - Selected text color
STATUS_BAR_BG = '#252526'     # Very Dark Gray - Status bar background
SASH_COLOR = '#45494a'        # Color for the paned window sash (Note: may not apply directly to tk.PanedWindow sash)
HEX_ADDR_FG = '#a9b7c6'       # Lighter gray for hex addresses
ASCII_NONPRINT_FG = '#606060' # Darker gray for non-printable chars in ASCII view
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

# Encoding assumed for filenames within ARC entries and for hashing string keys.
# Based on analysis and common use in Japanese games. Needs verification if issues arise.
FILENAME_ENCODING = 'shift_jis'

# --- CRC32 Calculation (Using crcmod) ---
_crc32_func: Optional[Callable[[bytes], int]] = None
if _crcmod_available:
    try:
        # Parameters derived from reverse engineering or observing the required MT Framework hashes.
        # They match the standard CRC-32 (ISO 3309) polynomial and settings with reflection.
        # Note: This configuration (rev=True) might differ from the specific internal details
        #       of the C# Kryptography.Hash.Crc.Crc32 class's "Normal" formula, but aims
        #       to produce the identical *final hash values* required by the archive format.
        # Polynomial: 0x104C11DB7 (Implied by 0x04C11DB7 standard and how crcmod handles it)
        # Initial XOR: 0xFFFFFFFF
        # Reflect In/Out: True (handled by rev=True)
        # Final XOR: 0x00000000 (applied *before* the final bitwise NOT)
        _crc32_func = crcmod.mkCrcFun(0x104C11DB7, initCrc=0xFFFFFFFF, rev=True, xorOut=0x00000000)

        def calculate_mt_crc32_intermediate(data_bytes: bytes) -> int:
            """Calculates the raw CRC value before the final ~ operation."""
            if not _crc32_func: raise RuntimeError("crcmod function not initialized")
            return _crc32_func(data_bytes)

        def get_hash(input_string: str, encoding: str = FILENAME_ENCODING) -> int:
            """
            Calculates the specific hash used for MT Framework extensions.
            Applies a bitwise NOT (~) to the result of the crcmod function.
            Assumes the provided encoding (defaulting to FILENAME_ENCODING) is
            correct for converting string keys to bytes before hashing.
            """
            if not _crc32_func: raise RuntimeError("crcmod function not initialized")
            try:
                # Encode the input string using the assumed encoding (Shift-JIS by default)
                input_bytes = input_string.encode(encoding, errors='replace')
                crc_val = calculate_mt_crc32_intermediate(input_bytes)
                # Apply the final bitwise NOT operation as required by the format
                return (~crc_val) & 0xFFFFFFFF
            except Exception as e:
                print(f"Error calculating hash for '{input_string}' with encoding '{encoding}': {e}")
                raise
    except Exception as e:
         print(f"Error initializing crcmod function: {e}")
         _crcmod_available = False
         # Redefine dummy function if initialization failed
         def get_hash(input_string: str, encoding: str = 'utf-8') -> int:
            print("CRCMOD init failed, cannot calculate hash!")
            return 0
elif not _crcmod_available: # If import failed earlier
    # Define dummy function if import failed initially
    def get_hash(input_string: str, encoding: str = 'utf-8') -> int:
            print("CRCMOD unavailable, cannot calculate hash!")
            return 0

# --- Precompute Extension Map ---
print("Calculating extension map hashes...")
EXTENSION_MAP_HASH_TO_EXT: Dict[int, str] = {}
EXTENSION_MAP_EXT_TO_HASH: Dict[str, int] = {}

# This map is based on the C# source and common MT Framework extensions.
# String keys will be hashed using get_hash() (which uses FILENAME_ENCODING).
# Integer keys are used directly.
_EXTENSION_MAP_RAW: Dict[Union[str, int], str] = {
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
    0x7E33A16C: ".spc", 0x7E4152FF: ".stg",
    # Additional entries found in some lists (ensure no overlap with C# unless intentional)
    0x17A550D: ".lom", 0x253F147: ".hit", 0x39D71F2: ".rvt", 0xDADAB62: ".oba", 0x10C460E6: ".msg",
    0x176C3F95: ".los", 0x19A59A91: ".lnk", 0x1BA81D3C: ".nck", 0x1ED12F1B: ".glp", 0x1EFB1B67: ".adh",
    0x2447D742: ".idm", 0x266E8A91: ".lku", 0x2C4666D1: ".smh", 0x2DC54131: ".cdf", 0x30ED4060: ".pth",
    0x36E29465: ".hkx", 0x38F66FC3: ".seg", 0x430B4FF4: ".ptl", 0x46810940: ".egv", 0x4D894D5D: ".cmi",
    0x4E2FEF36: ".mtg", 0x4F16B7AB: ".hri", 0x50F9DB3E: ".bfx", 0x5204D557: ".shp", 0x538120DE: ".eng",
    0x557ECC08: ".aef", 0x585831AA: ".pos", 0x5898749C: ".bgm", 0x60524FBB: ".shw", 0x60DD1B16: ".lsp",
    0x758B2EB7: ".cef", 0x7D1530C2: ".sngw", 0x46FB08BA: ".bmt", 0x285A13D9: ".vzo", 0x4323D83A: ".stex",
    0x6A5CDD23: ".occ", 0x62440501: ".lmd", 0x62A68441: ".thk", 0x4D3C70A1: ".bth", 0x244CC507: ".itr",
    0x6A9197ED: ".sss", 0x3B764DD4: ".sstr", 0x3516C3D2: ".lfd", 0x0CF7FB37: ".msf", 0x3D2E1661: ".ein",
    0x3B5A0DA5: ".idx", 0x354E1E08: ".ard", 0x5B9071CF: ".col", 0x342366F0: ".atk", 0x76042FD2: ".eco",
    0x052CCE4E: ".mef", 0x55E21D03: ".emp", 0x51BE0EC: ".rut", 0x70078B5: ".rmt", 0x949A1DA: ".adl",
    0x9C48A11: ".unk", 0xA736313: ".mdl", 0x108F442E: ".mdl", 0x130124FA: ".rmh", 0x18FF29AB: ".cut",
    0x1BE1DBEB: ".dom", 0x24339E8C: ".evl", 0x28D65BFA: ".pos", 0x2ADFA358: ".pvl", 0x348C831D: ".evc",
    0x375F06DA: ".evt", 0x40171000: ".dat", 0x42940D09: ".fmt", 0x4356673E: ".man", 0x46C78353: ".mes",
    0x5DF3D947: ".mry", 0x5FF4BE71: ".ene", 0x6505B384: ".ddsp", 0x681835FC: ".itm", 0x6A76E771: ".mes",
    0x6B0369B1: ".atr", 0x6B571E45: ".lgt", 0x6E69693A: ".obj", 0x7050198A: ".pmb", 0x74AFE18C: ".mdl",
    0x7618CC9A: ".mtn", 0x7D9D148B: ".eft", 0x7DB518E8: ".mdl", 0x7F68C6AF: ".mpac",
}

if _crcmod_available:
    for k, v in _EXTENSION_MAP_RAW.items():
        hash_val = 0
        if isinstance(k, str):
            try:
                # Hash the string key using the assumed FILENAME_ENCODING
                hash_val = get_hash(k, encoding=FILENAME_ENCODING)
            except Exception as e:
                print(f"[WARN] Failed to hash string key '{k}': {e}")
                pass # Skip if hashing fails
        elif isinstance(k, int):
            hash_val = k & 0xFFFFFFFF # Ensure uint32 range

        if hash_val != 0:
            if hash_val in EXTENSION_MAP_HASH_TO_EXT and EXTENSION_MAP_HASH_TO_EXT[hash_val] != v:
                 print(f"[WARN] Hash collision/override: {hash_val:#08X} maps to '{EXTENSION_MAP_HASH_TO_EXT[hash_val]}', overriding with '{v}'")
            EXTENSION_MAP_HASH_TO_EXT[hash_val] = v
            # Only add to ext->hash map if the extension isn't already mapped (first hash wins)
            if v not in EXTENSION_MAP_EXT_TO_HASH:
                EXTENSION_MAP_EXT_TO_HASH[v] = hash_val
            elif EXTENSION_MAP_EXT_TO_HASH[v] != hash_val:
                 print(f"[WARN] Extension '{v}' already mapped to hash {EXTENSION_MAP_EXT_TO_HASH[v]:#08X}, ignoring mapping for {hash_val:#08X}")

else:
    # Populate map only with integer keys if crcmod is unavailable
    print("Skipping string-based extension map generation as crcmod is unavailable.")
    for k, v in _EXTENSION_MAP_RAW.items():
         if isinstance(k, int):
              hash_val = k & 0xFFFFFFFF
              if hash_val in EXTENSION_MAP_HASH_TO_EXT and EXTENSION_MAP_HASH_TO_EXT[hash_val] != v:
                   print(f"[WARN] Hash collision/override: {hash_val:#08X} maps to '{EXTENSION_MAP_HASH_TO_EXT[hash_val]}', overriding with '{v}'")
              EXTENSION_MAP_HASH_TO_EXT[hash_val] = v
              if v not in EXTENSION_MAP_EXT_TO_HASH:
                  EXTENSION_MAP_EXT_TO_HASH[v] = hash_val
              elif EXTENSION_MAP_EXT_TO_HASH[v] != hash_val:
                  print(f"[WARN] Extension '{v}' already mapped to hash {EXTENSION_MAP_EXT_TO_HASH[v]:#08X}, ignoring mapping for {hash_val:#08X}")

print(f"Generated {len(EXTENSION_MAP_HASH_TO_EXT)} hash->ext entries.")
print(f"Generated {len(EXTENSION_MAP_EXT_TO_HASH)} ext->hash entries.")

def determine_extension(extension_hash: int) -> str:
    """Looks up the extension string for a given hash."""
    return EXTENSION_MAP_HASH_TO_EXT.get(extension_hash & 0xFFFFFFFF, f".{(extension_hash & 0xFFFFFFFF):08X}")

def determine_extension_hash(extension: str) -> int:
    """
    Determines the hash for a given extension string (e.g., '.tex').
    Tries direct lookup, then attempts parsing as hex, then raises error.
    """
    if not extension.startswith('.'):
        extension = '.' + extension

    # 1. Direct lookup in precomputed map
    hash_val = EXTENSION_MAP_EXT_TO_HASH.get(extension)
    if hash_val is not None:
        return hash_val

    # 2. Try parsing as hex (e.g. ".AABBCCDD") - deviates from C# but adds flexibility
    if len(extension) == 9:
        try:
            parsed_hash = int(extension[1:], 16)
            print(f"[WARN] Extension '{extension}' not in known map, using parsed hex value {parsed_hash:#08X}.")
            # Optionally, add this to the map runtime? EXTENSION_MAP_HASH_TO_EXT[parsed_hash] = extension; EXTENSION_MAP_EXT_TO_HASH[extension] = parsed_hash
            return parsed_hash
        except ValueError:
            pass # Not a valid hex string

    # 3. Cannot determine hash
    if not _crcmod_available:
        raise ValueError(f"Extension '{extension}' cannot be mapped to a known hash (crcmod missing/failed).")
    else:
        # Could attempt to hash it here, but it wasn't in the original known list
        # hash_val = get_hash(extension) # Hashing the *extension* might not be right
        raise ValueError(f"Extension '{extension}' cannot be mapped to a known hash.")


# --- IO Classes ---
class BinaryReaderXPy:
    """Reads standard data types from a stream, handles byte order and encoding."""
    def __init__(self, stream: io.BufferedIOBase, byte_order: ByteOrder = ByteOrder.LittleEndian, encoding: str = FILENAME_ENCODING):
        if not stream or not hasattr(stream, 'read'):
            raise ValueError("Invalid stream object provided.")
        self.base_stream = stream
        self.byte_order = byte_order
        self._encoding_default = encoding
        self._fmt_prefix = '<' if byte_order == ByteOrder.LittleEndian else '>'

    def close(self):
        # This reader doesn't own the stream, so don't close it here.
        # The owner of the stream (e.g., MtArc) is responsible for closing.
        self.base_stream = None

    def seek(self, offset: int, whence: int = io.SEEK_SET) -> int:
        if not self.base_stream or self.base_stream.closed: raise IOError("Stream is closed or invalid")
        return self.base_stream.seek(offset, whence)

    def tell(self) -> int:
        if not self.base_stream or self.base_stream.closed: raise IOError("Stream is closed or invalid")
        return self.base_stream.tell()

    def read_bytes(self, count: int) -> bytes:
        if not self.base_stream or self.base_stream.closed: raise IOError("Stream is closed or invalid")
        if count < 0: raise ValueError("Cannot read negative number of bytes")
        if count == 0: return b""
        data = self.base_stream.read(count)
        if len(data) != count:
            raise EOFError(f"Could not read {count} bytes (got {len(data)}). Stream ended prematurely.")
        return data

    # --- Primitive Read Methods ---
    def read_byte(self) -> int: return self.read_bytes(1)[0]
    def read_sbyte(self) -> int: return struct.unpack(self._fmt_prefix + 'b', self.read_bytes(1))[0]
    def read_int16(self) -> int: return struct.unpack(self._fmt_prefix + 'h', self.read_bytes(2))[0]
    def read_uint16(self) -> int: return struct.unpack(self._fmt_prefix + 'H', self.read_bytes(2))[0]
    def read_int32(self) -> int: return struct.unpack(self._fmt_prefix + 'i', self.read_bytes(4))[0]
    def read_uint32(self) -> int: return struct.unpack(self._fmt_prefix + 'I', self.read_bytes(4))[0]
    def read_int64(self) -> int: return struct.unpack(self._fmt_prefix + 'q', self.read_bytes(8))[0]
    def read_uint64(self) -> int: return struct.unpack(self._fmt_prefix + 'Q', self.read_bytes(8))[0]
    def read_float(self) -> float: return struct.unpack(self._fmt_prefix + 'f', self.read_bytes(4))[0]
    def read_double(self) -> float: return struct.unpack(self._fmt_prefix + 'd', self.read_bytes(8))[0]

    def read_string(self, length: int, encoding: Optional[str] = None) -> str:
        """Reads a fixed-length string, trims null bytes."""
        enc = encoding if encoding is not None else self._encoding_default
        raw_bytes = self.read_bytes(length)
        # Find first null byte and take data before it
        null_pos = raw_bytes.find(b'\0')
        if null_pos != -1:
            raw_bytes = raw_bytes[:null_pos]
        # Decode using specified encoding, replacing errors
        try:
            return raw_bytes.decode(enc, errors='replace')
        except Exception as e:
            print(f"[WARN] Failed to decode string bytes with {enc}: {raw_bytes!r}. Error: {e}. Falling back to ASCII.")
            # Fallback to ASCII if primary encoding fails
            return raw_bytes.decode('ascii', errors='replace')

    def peek_bytes(self, count: int, offset: int = 0) -> bytes:
         """Peeks ahead in the stream without changing the current position."""
         if not self.base_stream or self.base_stream.closed: raise IOError("Stream is closed or invalid")
         if not self.base_stream.seekable(): raise IOError("Stream does not support seeking (required for peeking)")
         current_pos = self.tell()
         target_pos = current_pos + offset
         data = b""
         try:
             self.seek(target_pos)
             data = self.base_stream.read(count)
         except EOFError: # Catch EOF during peek read
             raise EOFError(f"Could not peek {count} bytes (EOF reached).")
         except Exception as e:
             raise IOError(f"Error during peek operation: {e}")
         finally:
             # Always return to original position
             try:
                 self.seek(current_pos)
             except Exception as seek_err:
                 print(f"[ERROR] Failed to restore stream position after peek: {seek_err}")
                 # This is problematic, but we can't do much more here.
                 raise IOError("Failed to restore stream position after peek.") from seek_err

         # Check if the peek read was successful *after* restoring position
         if len(data) != count:
             raise EOFError(f"Could not peek {count} bytes (got {len(data)}).")
         return data

    def peek_string(self, length: int = 4, offset: int = 0, encoding: Optional[str] = None) -> str:
         """Peeks ahead and decodes a string, trims null bytes."""
         try:
             raw_bytes = self.peek_bytes(length, offset)
             enc = encoding if encoding is not None else self._encoding_default
             null_pos = raw_bytes.find(b'\0')
             if null_pos != -1:
                 raw_bytes = raw_bytes[:null_pos]
             return raw_bytes.decode(enc, errors='replace')
         except EOFError:
             # If peek fails due to EOF, return empty string gracefully
             return ""
         except Exception as e:
             print(f"[WARN] Failed to decode peeked string bytes with {encoding or self._encoding_default}: {raw_bytes!r}. Error: {e}. Falling back to ASCII.")
             return raw_bytes.decode('ascii', errors='replace') # Fallback

    # Bit reading methods remain placeholders
    def reset_bit_buffer(self): pass
    def read_bits(self, count: int): raise NotImplementedError("Bit reading not implemented yet.")
    def read_bit(self): raise NotImplementedError("Bit reading not implemented yet.")

class BinaryWriterXPy:
    """Writes standard data types to a stream, handles byte order and encoding."""
    def __init__(self, stream: io.BufferedIOBase, byte_order: ByteOrder = ByteOrder.LittleEndian, encoding: str = FILENAME_ENCODING):
        if not stream or not hasattr(stream, 'write'):
            raise ValueError("Invalid stream object provided.")
        self.base_stream = stream
        self.byte_order = byte_order
        self._encoding_default = encoding
        self._fmt_prefix = '<' if byte_order == ByteOrder.LittleEndian else '>'

    def close(self):
        # This writer doesn't own the stream.
        self.base_stream = None

    def seek(self, offset: int, whence: int = io.SEEK_SET) -> int:
        if not self.base_stream or self.base_stream.closed: raise IOError("Stream is closed or invalid")
        return self.base_stream.seek(offset, whence)

    def tell(self) -> int:
        if not self.base_stream or self.base_stream.closed: raise IOError("Stream is closed or invalid")
        return self.base_stream.tell()

    def write_bytes(self, data: bytes):
        if not self.base_stream or self.base_stream.closed: raise IOError("Stream is closed or invalid")
        self.base_stream.write(data)

    # --- Primitive Write Methods ---
    def write_byte(self, value: int): self.write_bytes(struct.pack(self._fmt_prefix + 'B', value))
    def write_sbyte(self, value: int): self.write_bytes(struct.pack(self._fmt_prefix + 'b', value))
    def write_int16(self, value: int): self.write_bytes(struct.pack(self._fmt_prefix + 'h', value))
    def write_uint16(self, value: int): self.write_bytes(struct.pack(self._fmt_prefix + 'H', value))
    def write_int32(self, value: int): self.write_bytes(struct.pack(self._fmt_prefix + 'i', value))
    def write_uint32(self, value: int): self.write_bytes(struct.pack(self._fmt_prefix + 'I', value))
    def write_int64(self, value: int): self.write_bytes(struct.pack(self._fmt_prefix + 'q', value))
    def write_uint64(self, value: int): self.write_bytes(struct.pack(self._fmt_prefix + 'Q', value))
    def write_float(self, value: float): self.write_bytes(struct.pack(self._fmt_prefix + 'f', value))
    def write_double(self, value: float): self.write_bytes(struct.pack(self._fmt_prefix + 'd', value))

    def write_string(self, value: str, length: int, encoding: Optional[str] = None, pad_byte: bytes = b'\0'):
        """Writes a string, padding or truncating to a fixed length."""
        if length <= 0: raise ValueError("Length must be positive for fixed-length string writing.")
        enc = encoding if encoding is not None else self._encoding_default
        try:
            encoded_bytes = value.encode(enc, errors='replace')
        except Exception as e:
            print(f"[WARN] Encoding string '{value}' failed with {enc}: {e}. Using ASCII fallback.")
            encoded_bytes = value.encode('ascii', errors='replace')

        if len(encoded_bytes) > length:
            truncated_bytes = encoded_bytes[:length]
            print(f"[WARN] String '{value}' ({len(encoded_bytes)} bytes) truncated to fit {length} bytes.")
            self.write_bytes(truncated_bytes)
        else:
            # Pad with the specified byte (usually null)
            padded_bytes = encoded_bytes.ljust(length, pad_byte)
            self.write_bytes(padded_bytes)

    def write_padding(self, count: int, pad_byte_val: int = 0x00):
        """Writes a specified number of padding bytes."""
        if count < 0: raise ValueError("Cannot write negative padding")
        if count > 0:
            pad_byte = bytes([pad_byte_val])
            padding = pad_byte * count
            self.write_bytes(padding)

    def write_alignment(self, alignment: int = 16, pad_byte_val: int = 0x00):
        """Writes padding bytes to align the stream position."""
        if alignment <= 0: raise ValueError("Alignment must be positive")
        current_pos = self.tell()
        remainder = current_pos % alignment
        if remainder > 0:
            bytes_to_write = alignment - remainder
            self.write_padding(bytes_to_write, pad_byte_val)

    # Bit writing methods remain placeholders
    def flush(self):
        if self.base_stream and not self.base_stream.closed and self.base_stream.writable():
            self.base_stream.flush()
    def write_bits(self, value: int, count: int): raise NotImplementedError("Bit writing not implemented yet.")
    def write_bit(self, value: int): raise NotImplementedError("Bit writing not implemented yet.")

# --- Data Structures ---
class MtHeaderPy:
    """Represents the MT Framework ARC header."""
    # Define struct formats for little and big endian
    STRUCT_FORMAT_LE = "<4shh"  # Magic (4s), Version (h), EntryCount (h)
    STRUCT_FORMAT_BE = ">4shh"
    SIZE = struct.calcsize(STRUCT_FORMAT_LE)  # Should be 8

    def __init__(self, magic: bytes = b'ARC\0', version: int = 7, entry_count: int = 0):
        self.magic: bytes = magic
        self.version: int = version # Store as native int
        self.entry_count: int = entry_count # Store as native int

    @classmethod
    def from_bytes(cls, data: bytes, platform: MtArcPlatform) -> 'MtHeaderPy':
        """Creates an MtHeaderPy object from byte data."""
        if len(data) < cls.SIZE:
            raise ValueError(f"Insufficient data for MtHeaderPy. Expected {cls.SIZE}, got {len(data)}.")

        fmt = cls.STRUCT_FORMAT_BE if platform == MtArcPlatform.BigEndian else cls.STRUCT_FORMAT_LE
        try:
            magic_bytes, version_s16, entry_count_s16 = struct.unpack(fmt, data[:cls.SIZE])
        except struct.error as e:
            raise IOError(f"Failed to unpack MtHeaderPy: {e}")

        # Validate magic bytes based on platform
        expected_magic = b'\0CRA' if platform == MtArcPlatform.BigEndian else b'ARC\0'
        if magic_bytes != expected_magic:
            # Log a warning but continue processing
            print(f"[WARN] Header magic mismatch! Expected {expected_magic!r}, got {magic_bytes!r} for platform {platform}. Assuming format based on platform detection.")

        # Convert shorts to native integers
        return cls(magic_bytes, int(version_s16), int(entry_count_s16))

    def to_bytes(self, platform: MtArcPlatform) -> bytes:
        """Converts the MtHeaderPy object back to bytes."""
        fmt = self.STRUCT_FORMAT_BE if platform == MtArcPlatform.BigEndian else self.STRUCT_FORMAT_LE

        # Ensure magic bytes match the target platform for writing
        magic_to_write = b'\0CRA' if platform == MtArcPlatform.BigEndian else b'ARC\0'

        # Clamp version and entry_count to signed short range before packing
        version_s16 = max(-32768, min(self.version, 32767))
        entry_count_s16 = max(-32768, min(self.entry_count, 32767))
        if version_s16 != self.version: print(f"[WARN] Header version {self.version} clamped to {version_s16} for packing.")
        if entry_count_s16 != self.entry_count: print(f"[WARN] Header entry count {self.entry_count} clamped to {entry_count_s16} for packing.")

        try:
            return struct.pack(fmt, magic_to_write, version_s16, entry_count_s16)
        except struct.error as e:
            raise IOError(f"Failed to pack MtHeaderPy: {e}")

class IMtEntryPy:
    """Interface defining common properties and methods for ARC entry types."""
    # Instance variables expected in implementing classes
    file_name_str: str
    extension_hash: int # Stored as uint32
    comp_size: int      # Stored as int32
    _decomp_size_raw: int # Stored as int32 (contains flags + size)
    offset: int         # Stored as int32
    is_dirty: bool      # Flag indicating if data has been modified
    data_to_write: Optional[bytes] # Holds modified data for saving

    def get_full_name(self) -> str:
        """Gets the full filename including the extension derived from the hash."""
        raise NotImplementedError

    def set_full_name(self, full_path_str: str):
        """Sets the filename and extension hash based on a full path string."""
        raise NotImplementedError

    def get_decompressed_size(self, platform: MtArcPlatform) -> int:
        """Gets the decompressed size, interpreting the raw size field based on platform."""
        raise NotImplementedError

    def set_decompressed_size(self, size: int, platform: MtArcPlatform):
        """Sets the decompressed size, updating the raw size field with flags based on platform."""
        raise NotImplementedError

    def to_bytes(self, platform: MtArcPlatform, encoding: str) -> bytes:
        """Serializes the entry metadata to bytes for writing to the ARC."""
        raise NotImplementedError

class BaseMtEntryPy(IMtEntryPy):
    """Base class for ARC entries, handling common logic."""
    def __init__(self, file_name: str = "", ext_hash: int = 0, comp_size: int = 0, decomp_size_raw: int = 0, offset: int = 0):
        self.file_name_str: str = file_name
        self.extension_hash: int = ext_hash & 0xFFFFFFFF # Ensure uint32
        self.comp_size: int = comp_size
        self._decomp_size_raw: int = decomp_size_raw # Store raw value including potential flags
        self.offset: int = offset
        # Runtime state
        self.is_dirty: bool = False
        self.data_to_write: Optional[bytes] = None # Holds data if modified/added

    def get_full_name(self) -> str:
        """Gets the full filename including the extension derived from the hash."""
        try:
            base_name = self.file_name_str
            extension = determine_extension(self.extension_hash)
            # Ensure path separators are consistent (e.g., use '/')
            full_name = (base_name + extension).replace('\\', '/')
            return full_name
        except Exception as e:
            print(f"[ERROR] Failed to determine extension for hash {self.extension_hash:#08X} ({self.file_name_str}): {e}")
            # Fallback if extension lookup fails
            return f"{self.file_name_str}.{self.extension_hash:08X}".replace('\\', '/')

    def set_full_name(self, full_path_str: str):
        """Sets the filename and extension hash based on a full path string."""
        # Normalize path separators
        normalized_path = full_path_str.replace('\\', '/')
        p = Path(normalized_path)
        ext = p.suffix # Includes the dot, e.g., ".tex"

        try:
            # Determine hash from extension (e.g., ".tex" -> 0x241F5DEB)
            self.extension_hash = determine_extension_hash(ext) & 0xFFFFFFFF
            # Store the path part without the extension
            self.file_name_str = str(p.with_suffix(''))
        except ValueError as e:
            print(f"[ERROR] Failed to set entry name '{full_path_str}': Cannot determine hash for extension '{ext}'. {e}")
            # Fallback: Use the full string as name, hash 0 (or keep existing?)
            # self.file_name_str = full_path_str
            # self.extension_hash = 0 # Or perhaps raise the error?
            raise # Re-raise the error for the caller to handle

    def get_decompressed_size(self, platform: MtArcPlatform) -> int:
        """Gets the decompressed size, interpreting the raw size field based on platform."""
        try:
            size_raw = int(self._decomp_size_raw) # Can be negative if read from file
        except (TypeError, ValueError):
            print(f"[WARN] Invalid raw decompressed size value: {self._decomp_size_raw!r}. Returning 0.")
            return 0

        # Logic derived from C# implementation
        if platform == MtArcPlatform.LittleEndian:
            # Mask out the upper byte (flags)
            return size_raw & 0x00FFFFFF
        elif platform == MtArcPlatform.BigEndian:
            # Shift right by 3 bits
            size_unsigned = size_raw & 0xFFFFFFFF
            return size_unsigned >> 3
        elif platform == MtArcPlatform.Switch:
             # C# returns the raw value directly.
             # Return the raw int value, matching C#.
             return size_raw
        else: # Default/Unknown platform - return raw value as int
            return size_raw

    def set_decompressed_size(self, size: int, platform: MtArcPlatform):
        """Sets the decompressed size, updating the raw size field with flags based on platform."""
        try:
            current_flags_raw = self._decomp_size_raw
            current_flags_int = int(current_flags_raw) if isinstance(current_flags_raw, int) else 0
            target_size = max(0, int(size)) # Ensure size is non-negative
        except (TypeError, ValueError) as e:
            print(f"[WARN] Failed to set decompressed size (size={size}, current_raw={self._decomp_size_raw!r}): {e}. Storing raw size.")
            self._decomp_size_raw = size
            return

        # Logic derived from C# implementation
        if platform == MtArcPlatform.LittleEndian:
            flags = current_flags_int & 0xFF000000
            new_size_part = target_size & 0x00FFFFFF
            self._decomp_size_raw = flags | new_size_part
        elif platform == MtArcPlatform.BigEndian:
            flags = current_flags_int & 0x00000007
            new_size_part = (target_size << 3) & 0xFFFFFFF8
            self._decomp_size_raw = flags | new_size_part
        elif platform == MtArcPlatform.Switch:
             # C# sets the value directly.
             self._decomp_size_raw = target_size
        else: # Default/Unknown platform
             self._decomp_size_raw = target_size

        # Ensure the final result fits in a signed 32-bit int for packing
        # Note: If target_size for Switch exceeds max_i32, this will clamp it.
        self._decomp_size_raw = self._pack_int32(self._decomp_size_raw)


    def to_bytes(self, platform: MtArcPlatform, encoding: str) -> bytes:
        """Serializes the entry metadata to bytes (must be implemented by subclasses)."""
        raise NotImplementedError("Subclasses must implement to_bytes")

    def _pack_int32(self, value: Union[int, Any]) -> int:
        """Safely converts value to int and clamps to signed 32-bit range."""
        try:
            int_value = int(value)
            # Clamp to min/max signed 32-bit values
            min_i32 = -2147483648
            max_i32 = 2147483647
            clamped_value = max(min_i32, min(int_value, max_i32))
            if clamped_value != int_value:
                print(f"[WARN] Clamped value {int_value} to {clamped_value} for int32 packing.")
            return clamped_value
        except (ValueError, TypeError):
            print(f"[WARN] Could not convert value {value!r} to int for packing. Using 0.")
            return 0


class MtEntryPy(BaseMtEntryPy):
    """Represents a standard ARC entry (64-byte filename)."""
    FILENAME_LEN = 64
    STRUCT_FORMAT_LE = f"< {FILENAME_LEN}s I i i i" # name, ext_hash (I), comp_size (i), decomp_size_raw (i), offset (i)
    STRUCT_FORMAT_BE = f"> {FILENAME_LEN}s I i i i"
    SIZE = struct.calcsize(STRUCT_FORMAT_LE) # Should be 64 + 4 + 4 + 4 + 4 = 80

    @classmethod
    def from_bytes(cls, data: bytes, platform: MtArcPlatform, encoding: str = FILENAME_ENCODING) -> 'MtEntryPy':
        """Creates an MtEntryPy from byte data."""
        if len(data) < cls.SIZE:
            raise ValueError(f"Insufficient data for MtEntryPy. Expected {cls.SIZE}, got {len(data)}.")

        fmt = cls.STRUCT_FORMAT_BE if platform == MtArcPlatform.BigEndian else cls.STRUCT_FORMAT_LE
        try:
            name_bytes, ext_hash, comp_size, decomp_size_raw, offset = struct.unpack(fmt, data[:cls.SIZE])
        except struct.error as e:
            raise IOError(f"Failed to unpack MtEntryPy: {e}")

        # Decode filename using specified encoding, trim nulls
        try:
            # Partition ensures we only take content before the first null byte
            file_name = name_bytes.partition(b'\0')[0].decode(encoding, errors='replace')
        except Exception as e:
            print(f"[WARN] Failed decoding filename bytes {name_bytes!r} with {encoding}: {e}. Using ASCII fallback.")
            file_name = name_bytes.partition(b'\0')[0].decode('ascii', errors='replace')

        return cls(file_name, ext_hash, comp_size, decomp_size_raw, offset)

    def to_bytes(self, platform: MtArcPlatform, encoding: str = FILENAME_ENCODING) -> bytes:
        """Serializes the entry metadata to bytes."""
        fmt = self.STRUCT_FORMAT_BE if platform == MtArcPlatform.BigEndian else self.STRUCT_FORMAT_LE

        # Encode filename
        try:
            name_bytes = self.file_name_str.encode(encoding, errors='replace')
        except Exception as e:
            print(f"[WARN] Failed encoding filename '{self.file_name_str}' with {encoding}: {e}. Using ASCII fallback.")
            name_bytes = self.file_name_str.encode('ascii', errors='replace')

        # Pad or truncate filename bytes
        padded_name = name_bytes.ljust(self.FILENAME_LEN, b'\0')[:self.FILENAME_LEN]
        if len(name_bytes) > self.FILENAME_LEN:
            print(f"[WARN] Filename '{self.file_name_str}' truncated to {self.FILENAME_LEN} bytes for entry.")

        # Pack values, ensuring they fit C types
        try:
            packed_data = struct.pack(fmt,
                                      padded_name,
                                      self.extension_hash & 0xFFFFFFFF, # Ensure uint32
                                      self._pack_int32(self.comp_size),
                                      self._pack_int32(self._decomp_size_raw),
                                      self._pack_int32(self.offset))
            return packed_data
        except Exception as e:
            raise IOError(f"Failed to pack MtEntryPy for '{self.get_full_name()}': {e}")

class MtEntryExtendedNamePy(MtEntryPy):
    """Represents an ARC entry with an extended (128-byte) filename."""
    FILENAME_LEN = 128
    STRUCT_FORMAT_LE = f"< {FILENAME_LEN}s I i i i"
    STRUCT_FORMAT_BE = f"> {FILENAME_LEN}s I i i i"
    SIZE = struct.calcsize(STRUCT_FORMAT_LE) # Should be 128 + 4 + 4 + 4 + 4 = 144
    # from_bytes and to_bytes are inherited, using the updated class variables

class MtEntrySwitchPy(BaseMtEntryPy):
    """Represents an ARC entry specific to the Switch platform."""
    FILENAME_LEN = 64
    # Switch format: name(64), hash(I), comp(i), decomp(i), unk1(i), offset(i)
    STRUCT_FORMAT_LE = f"< {FILENAME_LEN}s I i i i i"
    STRUCT_FORMAT_BE = f"> {FILENAME_LEN}s I i i i i" # Should not be used, Switch is LE
    SIZE = struct.calcsize(STRUCT_FORMAT_LE) # 64 + 4 + 4 + 4 + 4 + 4 = 84

    def __init__(self, file_name: str = "", ext_hash: int = 0, comp_size: int = 0, decomp_size_raw: int = 0, offset: int = 0, unk1: int = 0):
        super().__init__(file_name, ext_hash, comp_size, decomp_size_raw, offset)
        self.unk1: int = unk1 # Additional field for Switch

    @classmethod
    def from_bytes(cls, data: bytes, platform: MtArcPlatform, encoding: str = FILENAME_ENCODING) -> 'MtEntrySwitchPy':
        """Creates an MtEntrySwitchPy from byte data."""
        if platform != MtArcPlatform.Switch:
            print("[WARN] Reading Switch entry structure on a non-Switch detected platform.")
        if len(data) < cls.SIZE:
            raise ValueError(f"Insufficient data for MtEntrySwitchPy. Expected {cls.SIZE}, got {len(data)}.")

        # Switch is Little Endian
        fmt = cls.STRUCT_FORMAT_LE
        try:
            name_bytes, ext_hash, comp_size, decomp_size_raw, unk1, offset = struct.unpack(fmt, data[:cls.SIZE])
        except struct.error as e:
            raise IOError(f"Failed to unpack MtEntrySwitchPy: {e}")

        # Decode filename
        try:
            file_name = name_bytes.partition(b'\0')[0].decode(encoding, errors='replace')
        except Exception as e:
            print(f"[WARN] Failed decoding Switch filename bytes {name_bytes!r} with {encoding}: {e}. Using ASCII fallback.")
            file_name = name_bytes.partition(b'\0')[0].decode('ascii', errors='replace')

        return cls(file_name, ext_hash, comp_size, decomp_size_raw, offset, unk1)

    def to_bytes(self, platform: MtArcPlatform, encoding: str = FILENAME_ENCODING) -> bytes:
        """Serializes the Switch entry metadata to bytes."""
        # Switch is Little Endian
        fmt = self.STRUCT_FORMAT_LE

        # Encode filename
        try:
            name_bytes = self.file_name_str.encode(encoding, errors='replace')
        except Exception as e:
            print(f"[WARN] Failed encoding Switch filename '{self.file_name_str}' with {encoding}: {e}. Using ASCII fallback.")
            name_bytes = self.file_name_str.encode('ascii', errors='replace')

        # Pad or truncate filename bytes
        padded_name = name_bytes.ljust(self.FILENAME_LEN, b'\0')[:self.FILENAME_LEN]
        if len(name_bytes) > self.FILENAME_LEN:
            print(f"[WARN] Filename '{self.file_name_str}' truncated to {self.FILENAME_LEN} bytes for Switch entry.")

        # Pack values
        try:
            packed_data = struct.pack(fmt,
                                      padded_name,
                                      self.extension_hash & 0xFFFFFFFF, # Ensure uint32
                                      self._pack_int32(self.comp_size),
                                      self._pack_int32(self._decomp_size_raw),
                                      self._pack_int32(self.unk1),
                                      self._pack_int32(self.offset))
            return packed_data
        except Exception as e:
            raise IOError(f"Failed to pack MtEntrySwitchPy for '{self.get_full_name()}': {e}")

# Type alias for entry instances
AnyMtEntry = Union[MtEntryPy, MtEntryExtendedNamePy, MtEntrySwitchPy]

# --- Core ARC Logic ---
class MtArc:
    """Handles loading, manipulation, and saving of MT Framework ARC files."""
    def __init__(self):
        self.header: MtHeaderPy = MtHeaderPy()
        self.entries: list[AnyMtEntry] = []
        self.platform: MtArcPlatform = MtArcPlatform.LittleEndian
        self.file_handle: Optional[io.BufferedIOBase] = None
        self._is_extended_name: bool = False # Detected during load
        self._is_extended_header: bool = False # Detected during load
        self.encoding: str = FILENAME_ENCODING # Default encoding
        self.source_filepath: Optional[Path] = None
        self._log_callback: Callable[[str, str], None] = lambda msg, level: print(f"[{level}] {msg}") # Default logger

    def set_logger(self, log_func: Callable[[str, str], None]):
        """Sets a custom logging function (e.g., to update GUI)."""
        self._log_callback = log_func

    def log(self, message: str, level: str = "INFO"):
        """Logs a message using the configured callback."""
        if self._log_callback:
            # Add class context to the message
            self._log_callback(f"[MtArc] {message}", level)
        else:
            # Fallback to print if no callback is set
            print(f"[MtArc] {level}: {message}")

    def determine_platform(self, stream: io.BufferedIOBase) -> MtArcPlatform:
        """Determines the ARC platform (LE, BE, Switch) by peeking at the header."""
        if not stream.readable() or not stream.seekable():
            raise IOError("Stream must be readable and seekable to determine platform.")
        initial_pos = stream.tell()
        try:
            # Read enough bytes for the header
            header_bytes = stream.read(MtHeaderPy.SIZE)
            if len(header_bytes) < MtHeaderPy.SIZE:
                raise IOError("File too small to contain a valid ARC header.")

            # Try parsing as Little Endian
            magic_le: Optional[bytes] = None
            version_le: Optional[int] = None
            try:
                # Only unpack what's needed for detection
                magic_le, version_le_s16, _ = struct.unpack(MtHeaderPy.STRUCT_FORMAT_LE, header_bytes)
                version_le = int(version_le_s16)
            except struct.error:
                pass # Failed LE unpack

            # Try parsing as Big Endian
            magic_be: Optional[bytes] = None
            try:
                 # Only unpack magic needed for detection
                magic_be, _, _ = struct.unpack(MtHeaderPy.STRUCT_FORMAT_BE, header_bytes)
            except struct.error:
                 pass # Failed BE unpack

            # Determine platform based on magic and version
            if magic_le == b'ARC\0':
                # Version 9 strongly indicates Switch
                return MtArcPlatform.Switch if version_le == 9 else MtArcPlatform.LittleEndian
            elif magic_be == b'\0CRA':
                return MtArcPlatform.BigEndian
            else:
                # Could not determine based on standard magic bytes
                raise ValueError(f"Unknown ARC format: Magic bytes {header_bytes[:4]!r} did not match expected LE (ARC\\0) or BE (\\0CRA).")

        finally:
            # Always reset stream position
            stream.seek(initial_pos)

    def _get_entry_class_and_size(self) -> Tuple[type, int]:
        """Determines the correct entry class and its size based on platform and flags."""
        EntryClass: type = MtEntryPy # Default
        if self.platform == MtArcPlatform.Switch:
            EntryClass = MtEntrySwitchPy
        elif self._is_extended_name: # Check flag set during load
            EntryClass = MtEntryExtendedNamePy
        # Calculate size - assumes SIZE is defined on the class
        entry_struct_size = getattr(EntryClass, 'SIZE', 0)
        if entry_struct_size <= 0:
             raise TypeError(f"Could not determine struct size for entry class {EntryClass.__name__}")
        return EntryClass, entry_struct_size

    def load(self, filepath: Union[str, Path]):
        """Loads an ARC file from the given path."""
        self.close() # Close any previously opened file
        self.source_filepath = Path(filepath)
        self.entries = []
        self._is_extended_name = False
        self._is_extended_header = False

        self.log(f"Loading ARC file: {self.source_filepath}")
        temp_reader: Optional[BinaryReaderXPy] = None

        try:
            # Open file handle - will be kept open by MtArc instance
            f = open(self.source_filepath, 'rb')
            self.file_handle = f

            # Determine platform first
            self.platform = self.determine_platform(self.file_handle)

            # Create reader with correct byte order and encoding
            b_order = ByteOrder.BigEndian if self.platform == MtArcPlatform.BigEndian else ByteOrder.LittleEndian
            temp_reader = BinaryReaderXPy(self.file_handle, byte_order=b_order, encoding=self.encoding)
            self.log(f"Detected Platform: {self.platform}, Byte Order: {temp_reader.byte_order}")

            # Read Header
            header_bytes = temp_reader.read_bytes(MtHeaderPy.SIZE)
            self.header = MtHeaderPy.from_bytes(header_bytes, self.platform)
            self.log(f"Header: Magic={self.header.magic!r}, Version={self.header.version}, EntryCount={self.header.entry_count}")

            # Check for extended header (extra 4 bytes after header)
            # Condition based on C#: LE platform and version not 7 or 8
            entry_table_offset = MtHeaderPy.SIZE
            if self.platform == MtArcPlatform.LittleEndian and self.header.version not in [7, 8]:
                self._is_extended_header = True
                _ = temp_reader.read_int32() # Read and discard the extra int
                entry_table_offset += 4
                self.log("Detected Extended Header (4 extra bytes).")

            # Determine Entry Type (Standard, Extended Name, Switch)
            EntryClass: type = MtEntryPy # Default
            if self.platform == MtArcPlatform.Switch:
                EntryClass = MtEntrySwitchPy
                self.log("Using Switch Entry format (MtEntrySwitchPy).")
            elif self.platform == MtArcPlatform.LittleEndian and self.header.entry_count > 0:
                # Peek at the first entry to detect extended names
                # Use standard MtEntryPy size for the initial peek
                try:
                    first_entry_bytes = temp_reader.peek_bytes(MtEntryPy.SIZE, offset=0)
                    peek_entry = MtEntryPy.from_bytes(first_entry_bytes, self.platform, self.encoding)
                    # Heuristic based on C#: check for zero hash, size, or offset
                    peek_decomp_size = peek_entry.get_decompressed_size(self.platform)
                    if peek_entry.extension_hash == 0 or peek_decomp_size == 0 or peek_entry.offset == 0:
                        self._is_extended_name = True
                        EntryClass = MtEntryExtendedNamePy
                        self.log("Detected Extended Filenames (MtEntryExtendedNamePy).")
                    else:
                        self.log("Using Standard Entry format (MtEntryPy).")
                except EOFError:
                    self.log("Could not peek first entry (EOF). Assuming Standard Entry format.", "WARN")
                except Exception as e:
                    self.log(f"Error peeking first entry: {e}. Assuming Standard Entry format.", "WARN")
            else: # BigEndian or empty LE archive
                self.log("Using Standard Entry format (MtEntryPy).")

            entry_struct_size = getattr(EntryClass, 'SIZE', 0)
            if entry_struct_size <= 0: raise TypeError(f"Invalid size for entry class {EntryClass.__name__}")
            self.log(f"Reading {self.header.entry_count} entries (Class: {EntryClass.__name__}, Size: {entry_struct_size})...")

            # Ensure reader is positioned correctly after header/peek
            temp_reader.seek(entry_table_offset)

            # Read Entry Table
            for i in range(self.header.entry_count):
                try:
                    entry_bytes = temp_reader.read_bytes(entry_struct_size)
                    entry = EntryClass.from_bytes(entry_bytes, self.platform, self.encoding)
                    self.entries.append(entry)
                except EOFError:
                    self.log(f"EOF encountered while reading entry {i + 1}/{self.header.entry_count}. Stopping.", "ERROR")
                    self.header.entry_count = i # Adjust count to what was actually read
                    break
                except Exception as e:
                    self.log(f"Error reading entry {i + 1}: {e}", "ERROR")
                    self.log(traceback.format_exc(), "DEBUG")
                    # Decide whether to stop or skip? Stopping seems safer.
                    self.header.entry_count = i
                    raise IOError(f"Failed to read entry table at index {i}.") from e

            self.log(f"Successfully loaded {len(self.entries)} entries.")
            # Detach reader from the file handle so the handle stays open
            temp_reader.base_stream = None

        except FileNotFoundError:
            self.log(f"File not found: {self.source_filepath}", "ERROR")
            self.close() # Ensure handle is closed if opening failed
            raise
        except Exception as e:
            self.log(f"Failed to load ARC file: {e}", "ERROR")
            self.log(traceback.format_exc(), "DEBUG")
            self.close() # Ensure handle is closed on error
            raise
        finally:
            # If temp_reader still holds the stream (e.g., error before detaching), close reader
            if temp_reader and temp_reader.base_stream:
                temp_reader.close()

    def _determine_file_offset(self, entry_count: int, entry_size: int) -> int:
        """Calculates the starting offset for file data based on header and entry table."""
        # Base offset is header size
        header_size = MtHeaderPy.SIZE
        if self._is_extended_header:
            header_size += 4

        # Size of the entry table
        entry_table_size = entry_size * entry_count
        end_of_entries = header_size + entry_table_size

        # Determine alignment based on version and platform (derived from C#)
        alignment = 0
        v = self.header.version
        is_le = self.platform == MtArcPlatform.LittleEndian or self.platform == MtArcPlatform.Switch

        if v in [4, 7, 8, 16] and is_le:
            alignment = 0x8000
        elif v == 9: # Switch version
             alignment = 0x8000
        elif v == 17 and is_le: # Version 0x11
             alignment = 0x100

        # Apply alignment if needed
        if alignment > 0:
            # Calculate next multiple of alignment
            # Formula: (value + alignment - 1) // alignment * alignment
            # Bitwise equivalent: (value + alignment - 1) & ~(alignment - 1)
            mask = ~(alignment - 1)
            aligned_offset = (end_of_entries + alignment - 1) & mask
            # self.log(f"Applying alignment {alignment:#X}: Offset {end_of_entries:#X} -> {aligned_offset:#X}", "DEBUG")
            return aligned_offset
        else:
            # No alignment needed
            # self.log(f"No specific alignment for version {v} platform {self.platform}. Offset: {end_of_entries:#X}", "DEBUG")
            return end_of_entries

    def get_entry_data(self, entry: AnyMtEntry, compressed: bool = False) -> Optional[bytes]:
        """
        Retrieves the data for a given entry.
        Returns raw (decompressed) data by default, or compressed data if requested.
        Handles reading from the original file or using staged data_to_write.
        Returns None if data cannot be retrieved.
        """
        # 1. Check for staged data (added or replaced files)
        if entry.data_to_write is not None:
            self.log(f"Getting staged data for {entry.get_full_name()}", "DEBUG")
            raw_data = entry.data_to_write
            # Decide whether to compress the staged data
            should_compress = False
            # Always compress for Switch platform when writing
            if self.platform == MtArcPlatform.Switch and raw_data:
                should_compress = True
            # For other platforms, assume ZLIB if original comp != decomp,
            # but only if size > 0 (don't compress empty files)
            elif self.platform != MtArcPlatform.Switch and raw_data:
                 original_decomp_size = entry.get_decompressed_size(self.platform)
                 # If original entry indicated compression (comp != decomp), compress the new data too.
                 # Note: entry.comp_size might be -1 if newly added. Use original decomp size relation.
                 # If entry.is_dirty is True, we assume the *intent* is based on platform/original state.
                 # A simple check: if platform is Switch, compress. Otherwise, don't compress by default unless we know it *was* compressed.
                 # This logic needs refinement if we need to preserve original compression state more accurately.
                 # Current assumption: Compress Switch, don't compress others unless specifically told to.

            if compressed: # User explicitly wants potentially compressed data
                 if should_compress:
                     try:
                         # Use standard zlib compression level
                         return zlib.compress(raw_data, level=zlib.Z_DEFAULT_COMPRESSION)
                     except Exception as e:
                         self.log(f"Zlib compression failed for replaced entry {entry.get_full_name()}: {e}", "ERROR")
                         return raw_data # Fallback: return raw data if compression fails
                 else:
                     return raw_data # Return raw data if no compression needed/intended
            else: # User wants decompressed data
                 return raw_data # Staged data is always raw

        # 2. Read from the original file handle
        elif self.file_handle and not self.file_handle.closed and entry.offset >= 0 and entry.comp_size >= 0:
            try:
                self.file_handle.seek(entry.offset)
                comp_data = self.file_handle.read(entry.comp_size)
            except Exception as e:
                self.log(f"Failed to read data for {entry.get_full_name()} from offset {entry.offset:#X}: {e}", "ERROR")
                return None # Indicate read failure

            # Verify read amount
            if len(comp_data) != entry.comp_size:
                self.log(f"Read incomplete data for {entry.get_full_name()}. Expected {entry.comp_size}, got {len(comp_data)}.", "WARN")
                # Proceed with what was read, but it's likely corrupt

            # Determine if data is compressed (based on platform and size comparison)
            decomp_size = entry.get_decompressed_size(self.platform)
            is_zlib_compressed = False

            if entry.comp_size == 0:
                 is_zlib_compressed = False # Empty file
            elif self.platform == MtArcPlatform.Switch:
                 # Assume all non-empty Switch files are zlib compressed (based on C# observation)
                 is_zlib_compressed = True
            elif entry.comp_size != decomp_size:
                 # Standard heuristic: if sizes differ, assume compression.
                 # Check ZLIB header bytes (CMF/FLG) for confirmation.
                 if entry.comp_size >= 2:
                     # ZLIB header: CMF (1 byte), FLG (1 byte).
                     # Check Compression Method (CM = bits 0-3 of CMF) = 8 (DEFLATE)
                     # Check FCHECK (bits 0-4 of FLG). (CMF*256 + FLG) % 31 == 0
                     # Simpler check often used: CMF=0x78 usually indicates zlib/deflate.
                     # Let's use the check from C#: (compMagic & 0xF) != 8 || (compMagic & 0xF0) > 0x70
                     # This seems specific. Let's use a standard ZLIB header check.
                     # 0x78 0x01 - No Compression/low
                     # 0x78 0x9C - Default Compression
                     # 0x78 0xDA - Best Compression
                     cmf_flg = struct.unpack('>H', comp_data[:2])[0] # Read CMF+FLG as big-endian short
                     cmf = comp_data[0]
                     flg = comp_data[1]
                     is_zlib_header = (cmf == 0x78 and flg in [0x01, 0x9C, 0xDA]) or ((cmf*256 + flg) % 31 == 0)

                     if is_zlib_header:
                          is_zlib_compressed = True
                     else:
                          # Sizes differ, but no ZLIB header? Log warning.
                          self.log(f"Size mismatch for {entry.get_full_name()} (Comp:{entry.comp_size} != Decomp:{decomp_size}) but no ZLIB header found ({comp_data[:4]!r}). Assuming not compressed.", "WARN")
                          is_zlib_compressed = False
                 else:
                     # Too small to have header, but sizes differ? Assume compressed.
                     self.log(f"Size mismatch for {entry.get_full_name()} (Comp:{entry.comp_size} != Decomp:{decomp_size}) but data too small for header. Assuming compressed.", "WARN")
                     is_zlib_compressed = True

            # Return requested data (compressed or decompressed)
            if is_zlib_compressed:
                if compressed:
                    return comp_data # Return the original compressed data
                else:
                    try:
                        raw_data = zlib.decompress(comp_data)
                        # Verify decompressed size
                        if len(raw_data) != decomp_size:
                            self.log(f"Decompressed size mismatch for {entry.get_full_name()}. Expected {decomp_size}, got {len(raw_data)}.", "WARN") # <-- THIS IS WHERE THE WARNING COMES FROM
                        return raw_data
                    except zlib.error as e:
                        self.log(f"Zlib decompression failed for {entry.get_full_name()}: {e}. Returning raw compressed data.", "ERROR")
                        return comp_data # Return compressed data on error
                    except Exception as e:
                         self.log(f"Unexpected error during decompression for {entry.get_full_name()}: {e}", "ERROR")
                         return comp_data # Return compressed data on error
            else: # Not compressed
                # If user requested compressed, it's the same as raw
                return comp_data

        else:
            # No staged data and cannot read from file
            self.log(f"No data source available for {entry.get_full_name()} (No staged data, file handle issue, or invalid entry offset/size).", "WARN")
            return b'' # Return empty bytes instead of None for consistency

    def save(self, filepath: Union[str, Path]):
        """Saves the ARC archive to the specified path."""
        if not self.entries and not self.header:
            raise ValueError("No ARC data loaded or created to save.")

        # Close the input file handle if it's still open from loading
        # We'll write to a temporary file first.
        self.close()

        save_path = Path(filepath)
        self.log(f"Starting save process for ARC: {save_path}")

        # Determine the entry class and size based on current state
        EntryClass, entry_struct_size = self._get_entry_class_and_size()

        # Update header entry count
        current_entry_count = len(self.entries)
        self.header.entry_count = current_entry_count

        # Calculate data offset based on final entry count and type
        current_file_offset = self._determine_file_offset(current_entry_count, entry_struct_size)

        self.log(f"Save Parameters: Platform={self.platform}, Version={self.header.version}, "
                 f"Entry Count={current_entry_count}, Entry Class={EntryClass.__name__}, "
                 f"Entry Size={entry_struct_size}, Calculated Data Offset={current_file_offset:#0X}")

        # Use a temporary file for writing to prevent corruption on error
        temp_file_path = save_path.with_suffix(save_path.suffix + ".~tmp")
        self.log(f"Writing to temporary file: {temp_file_path}")

        saved_entries_meta: list[AnyMtEntry] = [] # Keep track of final metadata

        try:
            with open(temp_file_path, 'wb') as f:
                # Create writer with correct byte order and encoding
                b_order = ByteOrder.BigEndian if self.platform == MtArcPlatform.BigEndian else ByteOrder.LittleEndian
                writer = BinaryWriterXPy(f, byte_order=b_order, encoding=self.encoding)

                # --- Phase 1: Write File Data ---
                # Calculate required padding before data starts
                entry_table_start = MtHeaderPy.SIZE + (4 if self._is_extended_header else 0)
                entry_table_size = entry_struct_size * current_entry_count
                start_of_data_area = entry_table_start + entry_table_size

                # Pad up to the calculated data offset
                # We seek first, then align, as alignment might add bytes
                writer.seek(start_of_data_area)
                writer.write_alignment(current_file_offset) # Align to the calculated offset

                # Verify position after alignment
                if writer.tell() != current_file_offset:
                     self.log(f"Stream position {writer.tell():#X} after alignment does not match target data offset {current_file_offset:#X}! Seeking.", "WARN")
                     writer.seek(current_file_offset) # Force seek

                self.log(f"Writing file data starting at offset {writer.tell():#X}...")
                total_data_bytes_written = 0

                # Iterate through entries and write their data
                for i, entry in enumerate(self.entries):
                    entry_start_pos = writer.tell()
                    self.log(f"  Processing entry {i+1}/{current_entry_count}: {entry.get_full_name()} at {entry_start_pos:#X}", "DEBUG")

                    # Get raw (decompressed) data first
                    raw_data = self.get_entry_data(entry, compressed=False)

                    if raw_data is None:
                        # This indicates an error retrieving data earlier (already logged)
                        self.log(f"Skipping save for entry {entry.get_full_name()} as data could not be retrieved.", "ERROR")
                        # Update entry meta to reflect this for the table write
                        entry.offset = -1
                        entry.comp_size = 0
                        entry.set_decompressed_size(0, self.platform)
                        saved_entries_meta.append(entry) # Still need an entry in the table
                        continue

                    # Decide whether to compress based on platform/state
                    data_to_write = raw_data
                    is_compressed = False
                    raw_size = len(raw_data)

                    if self.platform == MtArcPlatform.Switch and raw_size > 0:
                        try:
                            data_to_write = zlib.compress(raw_data, level=zlib.Z_DEFAULT_COMPRESSION)
                            is_compressed = True
                        except Exception as comp_err:
                            self.log(f"Zlib compression failed for Switch entry {entry.get_full_name()}: {comp_err}. Writing raw.", "WARN")
                            data_to_write = raw_data # Fallback to raw
                    elif raw_size > 0 and entry.comp_size != entry.get_decompressed_size(self.platform) and not entry.is_dirty:
                        # If original was compressed (comp != decomp) and entry wasn't replaced (not dirty), re-compress
                        # Note: This might compress newly added files if their comp_size wasn't set properly. Refine if needed.
                         try:
                             # Check if raw_data actually looks like zlib already (shouldn't happen if get_entry_data worked)
                             if not (raw_data.startswith(b'\x78\x01') or raw_data.startswith(b'\x78\x9c') or raw_data.startswith(b'\x78\xda')):
                                 data_to_write = zlib.compress(raw_data, level=zlib.Z_DEFAULT_COMPRESSION)
                                 is_compressed = True
                             else:
                                 self.log(f"Data for {entry.get_full_name()} already looks compressed, writing as-is.", "DEBUG")
                                 data_to_write = raw_data # Already compressed?

                         except Exception as comp_err:
                             self.log(f"Zlib compression failed for non-Switch entry {entry.get_full_name()}: {comp_err}. Writing raw.", "WARN")
                             data_to_write = raw_data # Fallback to raw

                    # Write the final data (compressed or raw)
                    writer.write_bytes(data_to_write)
                    compressed_size = len(data_to_write)
                    total_data_bytes_written += compressed_size
                    self.log(f"    Wrote {compressed_size} bytes (Compressed: {is_compressed}, Raw Size: {raw_size})", "DEBUG")

                    # Update entry metadata for the table write
                    entry.offset = entry_start_pos
                    entry.comp_size = compressed_size
                    entry.set_decompressed_size(raw_size, self.platform) # Update raw size field
                    entry.is_dirty = False # Mark as no longer dirty after writing

                    saved_entries_meta.append(entry) # Add to list for final table write

                    # Optional: Align each file entry (e.g., to 4 bytes) - Not standard in all ARC versions
                    # writer.write_alignment(4)

                self.log(f"Finished writing file data. Total bytes: {total_data_bytes_written}. Final stream position: {writer.tell():#X}")

                # --- Phase 2: Write Header and Entry Table ---
                # Seek to the beginning to write header
                writer.seek(0)
                self.log(f"Writing header at offset 0...")
                writer.write_bytes(self.header.to_bytes(self.platform))

                # Write extended header int if necessary
                if self._is_extended_header:
                    writer.write_int32(0) # Seems to always be 0

                # Seek to the start of the entry table
                self.log(f"Writing entry table at offset {entry_table_start:#X}...")
                writer.seek(entry_table_start)

                # Verify entry count consistency
                if len(saved_entries_meta) != current_entry_count:
                    self.log(f"FATAL: Mismatch between saved metadata count ({len(saved_entries_meta)}) and header count ({current_entry_count})!", "FATAL")
                    # This indicates a logic error somewhere above.
                    raise RuntimeError("Internal error: Entry count mismatch during save.")

                # Write each entry's metadata
                for i, entry_meta in enumerate(saved_entries_meta):
                    if not isinstance(entry_meta, EntryClass):
                         self.log(f"FATAL: Entry {i} type mismatch during save. Expected {EntryClass.__name__}, got {type(entry_meta).__name__}. Aborting.", "FATAL")
                         raise TypeError("Internal error: Entry type mismatch during save.")
                    try:
                        entry_bytes = entry_meta.to_bytes(self.platform, self.encoding)
                        writer.write_bytes(entry_bytes)
                    except Exception as entry_write_err:
                        self.log(f"FATAL: Error writing entry metadata for {entry_meta.get_full_name()}: {entry_write_err}", "FATAL")
                        self.log(traceback.format_exc(), "DEBUG")
                        raise IOError(f"Failed to write entry metadata for {entry_meta.get_full_name()}") from entry_write_err

                # Verify final position after writing entry table
                expected_end_of_table = entry_table_start + entry_table_size
                if writer.tell() != expected_end_of_table:
                    self.log(f"Position after writing entry table ({writer.tell():#X}) doesn't match expected end ({expected_end_of_table:#X}).", "WARN")

                # Flush writer buffer
                writer.flush()
                self.log("Flush completed.")

            # --- Phase 3: Replace original file with temp file ---
            os.replace(temp_file_path, save_path)
            self.log(f"Successfully saved ARC to: {save_path}")
            self.source_filepath = save_path # Update source path
            # Re-open the newly saved file for subsequent operations? Optional.
            # self.load(save_path) # This would reset dirty flags etc.

        except Exception as e:
            self.log(f"Save operation failed: {e}", "ERROR")
            self.log(traceback.format_exc(), "DEBUG")
            # Attempt to clean up the temporary file if it exists
            if temp_file_path.exists():
                try:
                    os.remove(temp_file_path)
                    self.log(f"Removed temporary file: {temp_file_path}")
                except OSError as remove_err:
                    self.log(f"Error removing temporary file {temp_file_path}: {remove_err}", "ERROR")
            raise # Re-raise the original exception

    def extract_entry(self, entry: AnyMtEntry, output_dir: Union[str, Path]) -> bool:
        """Extracts a single entry to the specified output directory."""
        output_dir_path = Path(output_dir)
        # Use the entry's full name (potentially including subdirs)
        full_name = entry.get_full_name() # Already handles '/' separators
        output_path = output_dir_path / Path(full_name)

        try:
            # Create parent directories if they don't exist
            output_path.parent.mkdir(parents=True, exist_ok=True)
        except OSError as e:
             self.log(f"Failed to create directory structure for {output_path}: {e}", "ERROR")
             return False

        try:
            # Get decompressed data
            data = self.get_entry_data(entry, compressed=False)
            if data is None:
                # Error logged by get_entry_data
                return False

            # Write data to file
            with open(output_path, 'wb') as f_out:
                f_out.write(data)
            self.log(f"Extracted: {full_name} -> {output_path}", "DEBUG")
            return True
        except Exception as e:
            self.log(f"Failed to extract {full_name} to {output_path}: {e}", "ERROR")
            # Clean up partially written file?
            if output_path.exists():
                 try: output_path.unlink()
                 except OSError: pass
            return False

    def add_entry(self, file_path_to_add: Union[str, Path], path_in_archive: str) -> Optional[AnyMtEntry]:
        """Adds a file from the filesystem as a new entry in the archive."""
        p_add = Path(file_path_to_add)
        if not p_add.is_file():
            self.log(f"Cannot add file: Source file not found at '{p_add}'", "ERROR")
            return None

        try:
            # Read the content of the file to add
            with open(p_add, 'rb') as f_in:
                new_data = f_in.read()
        except Exception as e:
            self.log(f"Failed to read file content from '{p_add}': {e}", "ERROR")
            return None

        # Determine the correct entry class type
        EntryClass, _ = self._get_entry_class_and_size()
        # Create a new entry instance
        if EntryClass == MtEntrySwitchPy:
             entry = MtEntrySwitchPy()
        elif EntryClass == MtEntryExtendedNamePy:
             entry = MtEntryExtendedNamePy()
        else: # Default MtEntryPy
             entry = MtEntryPy()

        try:
            # Set filename and determine hash from the desired archive path
            entry.set_full_name(path_in_archive)
        except ValueError as e:
            # Error setting name/hash (logged by set_full_name)
            return None

        # Set sizes and stage data
        entry.set_decompressed_size(len(new_data), self.platform)
        entry.comp_size = -1 # Indicate size needs calculation on save
        entry.offset = -1    # Indicate offset needs calculation on save
        entry.data_to_write = new_data
        entry.is_dirty = True # Mark as needing to be written

        # Add to the list of entries
        self.entries.append(entry)
        self.log(f"Staged file '{p_add.name}' for addition as '{path_in_archive}' ({len(new_data)} bytes).")
        return entry

    def replace_entry_data(self, entry_to_replace: AnyMtEntry, new_data: bytes) -> bool:
        """Replaces the data of an existing entry with new data."""
        if entry_to_replace not in self.entries:
            # This shouldn't happen if the entry object is obtained correctly
            self.log(f"Cannot replace data: Entry '{entry_to_replace.get_full_name()}' not found in the current ARC.", "ERROR")
            return False

        try:
            # Update size fields based on new data
            entry_to_replace.set_decompressed_size(len(new_data), self.platform)
            # Stage the new data for writing
            entry_to_replace.data_to_write = new_data
            # Mark as dirty (needs saving)
            entry_to_replace.is_dirty = True
            # comp_size and offset will be recalculated during save
            entry_to_replace.comp_size = -1
            entry_to_replace.offset = -1

            self.log(f"Staged replacement data for '{entry_to_replace.get_full_name()}' ({len(new_data)} bytes).")
            return True
        except Exception as e:
            self.log(f"Failed to stage replacement data for {entry_to_replace.get_full_name()}: {e}", "ERROR")
            return False

    def remove_entry(self, entry_to_remove: AnyMtEntry) -> bool:
         """Removes an entry from the archive list."""
         if entry_to_remove in self.entries:
             self.entries.remove(entry_to_remove)
             self.log(f"Removed entry '{entry_to_remove.get_full_name()}' from list.", "INFO")
             # No need to mark dirty, saving implicitly handles removed entries
             return True
         else:
             self.log(f"Entry '{entry_to_remove.get_full_name()}' not found for removal.", "WARN")
             return False

    def close(self):
        """Closes the underlying file handle if it's open."""
        if self.file_handle:
            if not self.file_handle.closed:
                try:
                    self.file_handle.close()
                    self.log("Closed ARC file handle.", "DEBUG")
                except Exception as e:
                    self.log(f"Error closing file handle: {e}", "WARN")
            self.file_handle = None


# --- Hex Editor View Class ---
class HexEditorView(ttk.Frame):
    BYTES_PER_ROW = 16 # More standard hex view width
    BYTES_PER_GROUP = 8  # Group bytes (e.g., 8 bytes together)

    def __init__(self, parent, app_instance: 'MtArcToolApp', is_popup: bool = False):
        super().__init__(parent, style="Dark.TFrame")
        self.app = app_instance
        self.is_popup = is_popup
        self.current_entry: Optional[AnyMtEntry] = None
        self._raw_data = bytearray() # Current data being edited
        self._original_data = bytearray() # Data as initially loaded
        self._edit_debounce: Optional[str] = None # Timer ID for debouncing edits
        self._syncing_scroll: bool = False # Flag to prevent scroll recursion

        # Font setup
        self.font_size = 10 if os.name == 'nt' else 11
        self.hex_font = ("Consolas", self.font_size) if os.name == 'nt' else ("Monospace", self.font_size)

        # Layout: Make Text widgets expand
        self.grid_rowconfigure(1, weight=1)
        self.grid_columnconfigure(1, weight=3) # Hex view wider
        self.grid_columnconfigure(2, weight=1) # ASCII view narrower

        # --- Toolbar ---
        self.hex_toolbar = ttk.Frame(self, style="Dark.TFrame")
        self.hex_toolbar.grid(row=0, column=0, columnspan=3, sticky=tk.EW, pady=(0, 5))

        self.apply_btn = ttk.Button(self.hex_toolbar, text="Apply Changes", command=self.apply_changes, style="Dark.TButton", state=tk.DISABLED)
        self.popout_btn = ttk.Button(self.hex_toolbar, text="Pop Out", command=self.app.popout_hex_editor, style="Dark.TButton", state=tk.DISABLED)
        self.popin_btn = ttk.Button(self.hex_toolbar, text="Pop In", command=self.app.popin_hex_editor, style="Dark.TButton") # Initially hidden
        self.show_toolbar() # Show initial toolbar state

        # --- Address View ---
        addr_frame = ttk.Frame(self, style="Dark.TFrame")
        addr_frame.grid(row=1, column=0, sticky="nsew") # Span rows if needed
        self.addr_text = tk.Text(addr_frame, width=11, height=20, wrap=tk.NONE, state=tk.DISABLED,
                                 font=self.hex_font, bg=WIDGET_BG, fg=HEX_ADDR_FG, relief=tk.FLAT, bd=0,
                                 cursor="arrow")
        self.addr_text.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 5)) # Add padding

        # --- Hex View ---
        hex_frame = ttk.Frame(self, style="Dark.TFrame")
        hex_frame.grid(row=1, column=1, sticky="nsew")
        hex_frame.grid_rowconfigure(0, weight=1)
        hex_frame.grid_columnconfigure(0, weight=1)
        # Calculate width: 2 chars/byte, 1 space/byte, spaces for groups
        hex_width = self.BYTES_PER_ROW * 2 + (self.BYTES_PER_ROW -1) + (self.BYTES_PER_ROW // self.BYTES_PER_GROUP)
        self.hex_text = tk.Text(hex_frame, width=hex_width, height=20, wrap=tk.NONE,
                                font=self.hex_font, undo=True, maxundo=50, bg=WIDGET_BG, fg=TEXT_COLOR,
                                relief=tk.FLAT, bd=0, selectbackground=HIGHLIGHT_BG, selectforeground=HIGHLIGHT_FG,
                                insertbackground=TEXT_COLOR) # White cursor
        self.hex_v_scroll = ttk.Scrollbar(hex_frame, orient=tk.VERTICAL, command=self._scroll_views, style="Dark.Vertical.TScrollbar")

        # Link scrollbar and text widget
        self.hex_text['yscrollcommand'] = self._on_scroll
        self.hex_text.grid(row=0, column=0, sticky="nsew")
        self.hex_v_scroll.grid(row=0, column=1, sticky="ns")

        # --- ASCII View ---
        ascii_frame = ttk.Frame(self, style="Dark.TFrame")
        ascii_frame.grid(row=1, column=2, sticky="nsew")
        ascii_frame.grid_rowconfigure(0, weight=1)
        ascii_frame.grid_columnconfigure(0, weight=1)
        ascii_width = self.BYTES_PER_ROW + 2 # Allow some padding
        self.ascii_text = tk.Text(ascii_frame, width=ascii_width, height=20, wrap=tk.NONE,
                                  font=self.hex_font, undo=True, maxundo=50, bg=WIDGET_BG, fg=TEXT_COLOR,
                                  relief=tk.FLAT, bd=0, selectbackground=HIGHLIGHT_BG, selectforeground=HIGHLIGHT_FG,
                                  insertbackground=TEXT_COLOR)
        # Link ASCII view scroll to the main hex scrollbar command
        self.ascii_text['yscrollcommand'] = self._on_scroll
        self.ascii_text.grid(row=0, column=0, sticky="nsew")

        # --- Tag Configurations ---
        self.ascii_text.tag_configure("nonprintable", foreground=ASCII_NONPRINT_FG)
        self.hex_text.tag_configure("edited", foreground=EDITED_FG)
        self.ascii_text.tag_configure("edited", foreground=EDITED_FG)
        # Optional: Configure selection tags if needed (defaults are usually ok)
        # self.hex_text.tag_configure("sel", background=HIGHLIGHT_BG, foreground=HIGHLIGHT_FG)
        # self.ascii_text.tag_configure("sel", background=HIGHLIGHT_BG, foreground=HIGHLIGHT_FG)

        # --- Bindings ---
        # Use KeyRelease for less frequent updates than KeyPress
        self.hex_text.bind("<KeyRelease>", lambda e: self.schedule_update(e, 'hex'))
        self.ascii_text.bind("<KeyRelease>", lambda e: self.schedule_update(e, 'ascii'))
        # Use <<Modified>> event to track undo/redo and enable Apply button
        self.hex_text.bind("<<Modified>>", lambda e: self.on_modified(self.hex_text))
        self.ascii_text.bind("<<Modified>>", lambda e: self.on_modified(self.ascii_text))
        # Bind mouse wheel scrolling (platform-dependent)
        if os.name == 'nt':
             self.hex_text.bind("<MouseWheel>", self._on_mouse_wheel)
             self.ascii_text.bind("<MouseWheel>", self._on_mouse_wheel)
             self.addr_text.bind("<MouseWheel>", self._on_mouse_wheel)
        else: # Linux/macOS use Button-4/5
             self.hex_text.bind("<Button-4>", lambda e: self._scroll_views('scroll', -1, 'units'))
             self.hex_text.bind("<Button-5>", lambda e: self._scroll_views('scroll', 1, 'units'))
             self.ascii_text.bind("<Button-4>", lambda e: self._scroll_views('scroll', -1, 'units'))
             self.ascii_text.bind("<Button-5>", lambda e: self._scroll_views('scroll', 1, 'units'))
             self.addr_text.bind("<Button-4>", lambda e: self._scroll_views('scroll', -1, 'units'))
             self.addr_text.bind("<Button-5>", lambda e: self._scroll_views('scroll', 1, 'units'))

    def show_toolbar(self):
        """Configures which toolbar buttons are visible based on popup state."""
        # Hide all first
        self.apply_btn.pack_forget()
        self.popout_btn.pack_forget()
        self.popin_btn.pack_forget()
        # Show relevant buttons
        if self.is_popup:
            self.apply_btn.pack(side=tk.LEFT, padx=5, pady=2)
            self.popin_btn.pack(side=tk.RIGHT, padx=5, pady=2)
        else: # Embedded view
            # Apply button is not shown directly in embedded view
            self.popout_btn.pack(side=tk.RIGHT, padx=5, pady=2)

    def on_modified(self, widget: tk.Text):
        """Callback for <<Modified>> event to track changes."""
        # The 'modified' flag is set by Tkinter on user edits *and* programmatic changes.
        # We only care about user edits triggering the Apply button.
        # The flag is automatically cleared after this callback runs.
        # We'll use self.current_entry.is_dirty for the actual data state.
        is_modified = widget.edit_modified()
        if is_modified:
            # Only enable Apply button if it's the popup view
            if self.is_popup:
                 self.apply_btn.config(state=tk.NORMAL)
            # We need to reset the flag *after* checking it
            widget.edit_modified(False)

    def _on_scroll(self, first: str, last: str):
        """Callback when a Text widget scrolls vertically."""
        if self._syncing_scroll: return
        self._syncing_scroll = True
        try:
            # Update other views and the scrollbar itself
            self.addr_text.yview_moveto(first)
            self.hex_text.yview_moveto(first)
            self.ascii_text.yview_moveto(first)
            self.hex_v_scroll.set(first, last)
        finally:
            self._syncing_scroll = False

    def _scroll_views(self, *args):
         """Command for the Scrollbar to scroll all linked views."""
         if self._syncing_scroll: return
         self._syncing_scroll = True
         try:
             self.addr_text.yview(*args)
             self.hex_text.yview(*args)
             self.ascii_text.yview(*args)
             # Update scrollbar position based on hex_text's new view
             self.app.root.update_idletasks() # Allow view update
             first, last = self.hex_text.yview()
             self.hex_v_scroll.set(first, last)
         finally:
             self._syncing_scroll = False

    def _on_mouse_wheel(self, event):
        """Handles mouse wheel scrolling for linked views (Windows)."""
        if self._syncing_scroll: return
        # Determine scroll direction and amount
        delta = 0
        if event.num == 5 or event.delta < 0: delta = 1
        if event.num == 4 or event.delta > 0: delta = -1
        # Scroll all views
        self._scroll_views('scroll', delta, 'units')
        return "break" # Prevent default scrolling behavior


    def clear(self):
        """Clears the hex editor display and resets state."""
        self.current_entry = None
        self._raw_data = bytearray()
        self._original_data = bytearray()

        # Enable, clear, disable to ensure clean state
        for widget in [self.addr_text, self.hex_text, self.ascii_text]:
            widget.config(state=tk.NORMAL)
            widget.delete('1.0', tk.END)
            widget.config(state=tk.DISABLED if widget == self.addr_text else tk.NORMAL)

        # Reset undo stack and modified flag
        self.hex_text.edit_reset()
        self.ascii_text.edit_reset()
        self.hex_text.edit_modified(False)
        self.ascii_text.edit_modified(False)

        # Update button states
        self.apply_btn.config(state=tk.DISABLED)
        if not self.is_popup:
            self.app.update_button_states()
        self.set_status_message("Hex view cleared.")

    def set_status_message(self, msg: str):
        """Helper to update status bar (if available)"""
        if not self.is_popup and hasattr(self.app, 'set_status'):
            self.app.set_status(msg)

    def load_data(self, entry: AnyMtEntry, data: Optional[bytes]):
        """Loads byte data into the hex editor views."""
        self.clear() # Start fresh
        if data is None:
            self.app.log_message(f"HexEditor: No data provided for {entry.get_full_name()}.", "WARN")
            data = b'' # Use empty bytes if None is passed
        if not isinstance(data, (bytes, bytearray)):
             self.app.log_message(f"HexEditor: Invalid data type ({type(data)}) for {entry.get_full_name()}.", "ERROR")
             data = b''

        self.current_entry = entry
        self._raw_data = bytearray(data)
        self._original_data = bytearray(data) # Keep original copy for diffing
        self.app.log_message(f"HexEditor: Displaying {len(data):,} bytes for {entry.get_full_name()}", "DEBUG")
        self.set_status_message(f"Loading {len(data):,} bytes for {entry.get_full_name()}...")

        addr_lines, hex_lines_data, ascii_lines_data = [], [], []
        num_rows = math.ceil(len(self._raw_data) / self.BYTES_PER_ROW)

        # --- Build content strings ---
        for i in range(0, len(data) if data else 0, self.BYTES_PER_ROW):
            chunk = self._raw_data[i:min(i + self.BYTES_PER_ROW, len(data))]
            addr_lines.append(f"{i:08X}: ") # Address part

            # Hex part
            hex_row_parts = []
            for j in range(self.BYTES_PER_ROW):
                if j < len(chunk):
                    byte_val = chunk[j]
                    hex_byte = f"{byte_val:02X}"
                    hex_row_parts.append(hex_byte)
                else:
                    hex_row_parts.append("  ") # Pad if row is short

                # Add group separator
                if (j + 1) % self.BYTES_PER_GROUP == 0 and j < self.BYTES_PER_ROW - 1:
                    hex_row_parts.append(" ")
            hex_lines_data.append(" ".join(hex_row_parts)) # Join hex bytes with single space


            # ASCII part
            ascii_row = ""
            tags_ascii: List[Tuple[str, int, int]] = [] # (tag_name, start_col, end_col)
            for j, byte_val in enumerate(chunk):
                # Use a common encoding likely to show most printable ASCII/Extended chars
                try:
                    char = bytes([byte_val]).decode('cp1252') # Windows-1252 is often good for legacy data
                    if not char.isprintable() or ord(char) < 32:
                         char = '.' # Replace non-printable with dot
                except:
                     char = '.' # Replace decoding errors with dot

                ascii_row += char
                # Tag non-printable characters for visual distinction
                if char == '.':
                    tags_ascii.append(("nonprintable", j, j + 1))
            ascii_lines_data.append((ascii_row, tags_ascii))

        # --- Populate Text widgets ---
        # Enable widgets for update
        self.addr_text.config(state=tk.NORMAL)
        self.hex_text.config(state=tk.NORMAL)
        self.ascii_text.config(state=tk.NORMAL)

        # Clear existing content efficiently
        self.addr_text.delete('1.0', tk.END)
        self.hex_text.delete('1.0', tk.END)
        self.ascii_text.delete('1.0', tk.END)

        # Insert new content
        self.addr_text.insert('1.0', "\n".join(addr_lines))
        self.hex_text.insert('1.0', "\n".join(hex_lines_data))
        for idx, (line, tags) in enumerate(ascii_lines_data):
            start_index = f"{idx + 1}.0"
            end_index = f"{idx + 1}.{len(line)}"
            self.ascii_text.insert(start_index, line + "\n")
            # Apply tags for this line
            for tag_name, start_col, end_col in tags:
                try:
                    self.ascii_text.tag_add(tag_name, f"{idx + 1}.{start_col}", f"{idx + 1}.{end_col}")
                except tk.TclError as e:
                     # Handle cases where indices might be slightly off during rapid updates
                     print(f"[WARN] Error applying tag '{tag_name}' at line {idx+1}, cols {start_col}-{end_col}: {e}")

        # --- Finalize State ---
        # Scroll to top
        self._scroll_views('moveto', '0.0')

        # Set final widget states
        self.addr_text.config(state=tk.DISABLED) # Address view is read-only
        self.hex_text.config(state=tk.NORMAL)    # Editable
        self.ascii_text.config(state=tk.NORMAL)   # Editable

        # Reset modification state after programmatic changes
        self.hex_text.edit_reset()
        self.ascii_text.edit_reset()
        self.hex_text.edit_modified(False)
        self.ascii_text.edit_modified(False)

        self.apply_btn.config(state=tk.DISABLED) # No changes applied yet
        if not self.is_popup:
            self.app.update_button_states() # Update main window buttons
        self.set_status_message(f"Displayed {len(data):,} bytes for {entry.get_full_name()}")

    def schedule_update(self, event, source: str):
        """Schedules the handle_edit function to run after a short delay."""
        # Cancel any pending update
        if self._edit_debounce:
            self.after_cancel(self._edit_debounce)

        # Ignore modifier key releases
        if event.keysym in ('Shift_L', 'Shift_R', 'Control_L', 'Control_R', 'Alt_L', 'Alt_R', 'Caps_Lock', 'Num_Lock'):
            return

        # Schedule the update
        self._edit_debounce = self.after(300, lambda s=source: self.handle_edit(s))

    def handle_edit(self, source: str):
        """Parses the content of the edited view (hex or ASCII) and updates the internal data."""
        if not self.current_entry: return
        self._edit_debounce = None # Clear timer ID

        widget = self.hex_text if source == 'hex' else self.ascii_text
        try:
            # Get all content, excluding the automatic trailing newline Tk adds
            content = widget.get('1.0', tk.END + "-1c")
        except Exception as e:
            self.app.log_message(f"Hex Editor: Error getting text content from {source} view: {e}", "ERROR")
            return

        new_byte_list = bytearray()
        original_data_len = len(self._original_data)
        modified_offsets: Set[int] = set() # Track offsets changed from original

        try:
            lines = content.split('\n')
            if source == 'hex':
                current_offset = 0
                for line_idx, line in enumerate(lines):
                     # Clean up hex string: remove spaces, keep only valid hex chars
                     hex_chars = "".join(c for c in line if c in '0123456789abcdefABCDEF')
                     line_byte_count = 0
                     for j in range(0, len(hex_chars), 2):
                         if current_offset >= original_data_len: break # Stop if exceeding original length
                         byte_hex = hex_chars[j:j+2]
                         if len(byte_hex) == 2:
                             try:
                                 new_byte_val = int(byte_hex, 16)
                             except ValueError:
                                 self.app.log_message(f"Invalid hex sequence '{byte_hex}' on line {line_idx + 1}. Keeping original.", "WARN")
                                 new_byte_val = self._original_data[current_offset]
                         else: # Incomplete byte at end of line?
                             new_byte_val = self._original_data[current_offset]

                         if self._original_data[current_offset] != new_byte_val:
                             modified_offsets.add(current_offset)
                         new_byte_list.append(new_byte_val)
                         current_offset += 1
                         line_byte_count += 1
                         if line_byte_count >= self.BYTES_PER_ROW: break # Max bytes per line reached
                     if current_offset >= original_data_len: break # Stop if done

            elif source == 'ascii':
                current_offset = 0
                for line_idx, line in enumerate(lines):
                    for j in range(self.BYTES_PER_ROW):
                        if current_offset >= original_data_len: break
                        if j < len(line):
                             char = line[j]
                             try:
                                 # Encode using the same encoding used for display
                                 new_byte_val = char.encode('cp1252')[0]
                             except (UnicodeEncodeError, IndexError):
                                 new_byte_val = ord('.') # Default to '.' if cannot encode
                        else: # Line is shorter than BYTES_PER_ROW
                            new_byte_val = self._original_data[current_offset] # Keep original

                        if self._original_data[current_offset] != new_byte_val:
                            modified_offsets.add(current_offset)
                        new_byte_list.append(new_byte_val)
                        current_offset += 1
                    if current_offset >= original_data_len: break # Stop if done

            # Ensure the final byte list has the same length as the original
            if len(new_byte_list) > original_data_len:
                 new_byte_list = new_byte_list[:original_data_len] # Truncate if user added too much
                 self.app.log_message("Hex edit resulted in longer data, truncated to original length.", "WARN")
            elif len(new_byte_list) < original_data_len:
                 # Pad with original data if user deleted characters
                 new_byte_list.extend(self._original_data[len(new_byte_list):])
                 self.app.log_message("Hex edit resulted in shorter data, padded with original bytes.", "DEBUG")


            # --- Update internal data and the *other* view ---
            if bytes(new_byte_list) != self._raw_data:
                self.app.log_message(f"Hex data changed by user in {source} view. Staging update.", "DEBUG")
                self._raw_data = new_byte_list # Update the working buffer

                # Stage the data in the entry object for saving
                if self.current_entry:
                     self.current_entry.data_to_write = bytes(self._raw_data)
                     self.current_entry.is_dirty = True
                     self.app.mark_dirty(True) # Mark the whole archive as dirty

                # Refresh the *other* view based on the new _raw_data
                # Highlight bytes that differ from the _original_data
                other_view = 'ascii' if source == 'hex' else 'hex'
                self.update_view_from_data(other_view, modified_offsets)

                # Enable apply button only if in popup
                if self.is_popup:
                    self.apply_btn.config(state=tk.NORMAL)
            else:
                 self.app.log_message("Hex content unchanged after parsing edit.", "DEBUG")

        except Exception as parse_err:
             self.app.log_message(f"Error parsing hex/ASCII edit from {source} view: {parse_err}", "ERROR")
             self.app.log_message(traceback.format_exc(), "DEBUG")
             # Optionally revert the view? For now, just log the error.

        finally:
             # Reset the modified flag of the source widget *after* processing
             # Do this even if parsing failed to prevent infinite loops
             widget.edit_modified(False)


    def update_view_from_data(self, view_to_update: str, edited_offsets: Optional[Set[int]] = None):
        """
        Refreshes the specified view (hex or ASCII) based on the current self._raw_data.
        Highlights bytes whose offsets are in edited_offsets (compared to original).
        """
        if not self.current_entry: return
        if edited_offsets is None: edited_offsets = set()

        self.app.log_message(f"Refreshing {view_to_update} view (Highlighting {len(edited_offsets)} edits)...", "DEBUG")

        # Store scroll positions
        # Use try-except as yview might fail if widget is not fully initialized/visible
        try: hex_scroll = self.hex_text.yview()
        except tk.TclError: hex_scroll = (0.0, 0.0)
        try: ascii_scroll = self.ascii_text.yview()
        except tk.TclError: ascii_scroll = (0.0, 0.0)

        # Temporarily unbind to prevent feedback loops during update
        self.hex_text.unbind("<KeyRelease>")
        self.ascii_text.unbind("<KeyRelease>")
        self.hex_text.unbind("<<Modified>>")
        self.ascii_text.unbind("<<Modified>>")

        widget = self.hex_text if view_to_update == 'hex' else self.ascii_text

        # Enable, clear, and prepare for refill
        widget.config(state=tk.NORMAL)
        widget.delete('1.0', tk.END)
        widget.tag_remove("edited", "1.0", tk.END) # Clear previous edited tags

        # --- Refill content line by line ---
        current_line = 1
        for i in range(0, len(self._raw_data), self.BYTES_PER_ROW):
            chunk = self._raw_data[i:min(i + self.BYTES_PER_ROW, len(self._raw_data))]
            line_content = ""
            tags_this_line: List[Tuple[str, int, int]] = [] # (tag_name, start, end)

            if view_to_update == 'hex':
                hex_row_parts = []
                col = 0 # Character position in the hex line string
                for j in range(self.BYTES_PER_ROW):
                    current_offset = i + j
                    hex_byte_str = ""
                    byte_len_in_hex = 2 # How many chars represent this byte

                    if j < len(chunk):
                        byte_val = chunk[j]
                        hex_byte_str = f"{byte_val:02X}"
                    else:
                        hex_byte_str = "  " # Pad if row is short

                    hex_row_parts.append(hex_byte_str)

                    # Add edited tag if this byte offset was modified
                    if current_offset in edited_offsets:
                         tags_this_line.append(("edited", col, col + byte_len_in_hex))

                    col += byte_len_in_hex

                    # Add group separator space
                    if (j + 1) % self.BYTES_PER_GROUP == 0 and j < self.BYTES_PER_ROW - 1:
                        hex_row_parts.append(" ") # Add the visual space
                        col += 1 # Account for the space char

                line_content = "".join(hex_row_parts)

            else: # view_to_update == 'ascii'
                ascii_row_chars = []
                for j, byte_val in enumerate(chunk):
                    current_offset = i + j
                    try:
                        char = bytes([byte_val]).decode('cp1252')
                        if not char.isprintable() or ord(char) < 32: char = '.'
                    except:
                        char = '.'
                    ascii_row_chars.append(char)

                    # Add nonprintable tag
                    if char == '.':
                        tags_this_line.append(("nonprintable", j, j + 1))
                    # Add edited tag
                    if current_offset in edited_offsets:
                        tags_this_line.append(("edited", j, j + 1))
                line_content = "".join(ascii_row_chars)

            # Insert the line content
            start_index = f"{current_line}.0"
            widget.insert(start_index, line_content + "\n")

            # Apply all tags for this line
            for tag_name, start_col, end_col in tags_this_line:
                try:
                     tag_start = f"{current_line}.{start_col}"
                     tag_end = f"{current_line}.{end_col}"
                     widget.tag_add(tag_name, tag_start, tag_end)
                except tk.TclError as tag_err:
                     print(f"[WARN] Failed applying tag '{tag_name}' from {tag_start} to {tag_end}: {tag_err}")

            current_line += 1

        # --- Finalize state ---
        widget.config(state=tk.NORMAL) # Ensure still editable

        # Restore scroll positions AFTER inserting content and updating layout
        self.app.root.update_idletasks()
        try:
            self.hex_text.yview_moveto(hex_scroll[0])
            self.ascii_text.yview_moveto(ascii_scroll[0])
            self.addr_text.yview_moveto(hex_scroll[0]) # Keep addr view synced
        except tk.TclError as scroll_err:
             print(f"[WARN] Failed to restore scroll position: {scroll_err}")

        # Re-bind events
        self.hex_text.bind("<KeyRelease>", lambda e: self.schedule_update(e, 'hex'))
        self.ascii_text.bind("<KeyRelease>", lambda e: self.schedule_update(e, 'ascii'))
        self.hex_text.bind("<<Modified>>", lambda e: self.on_modified(self.hex_text))
        self.ascii_text.bind("<<Modified>>", lambda e: self.on_modified(self.ascii_text))

        # Crucial: Reset the modified flag AFTER programmatic changes
        widget.edit_modified(False)


    def apply_changes(self):
        """Explicitly applies staged changes from the hex editor to the current entry."""
        # This function is primarily for the popup window's button.
        # The actual data staging happens in handle_edit.
        if self.current_entry and self.current_entry.is_dirty:
            self.app.log_message(f"Applied hex editor changes to entry: {self.current_entry.get_full_name()}")
            # Data is already staged in self.current_entry.data_to_write by handle_edit
            # Mark the archive dirty (already done in handle_edit)
            self.app.mark_dirty(True)
            # Disable the apply button after applying
            self.apply_btn.config(state=tk.DISABLED)
            # Mark the original data as the new baseline for diffing
            self._original_data = bytearray(self._raw_data)
            # Reload views to remove 'edited' tags
            modified_offsets = set() # No differences from the new original
            self.update_view_from_data('hex', modified_offsets)
            self.update_view_from_data('ascii', modified_offsets)

        else:
            self.app.log_message("No hex changes detected to apply.", "INFO")


# --- Main GUI Application ---
class MtArcToolApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("BurgerSoftware (Kuriimu2 Python Fork) - MT ARC Tool")
        self.root.geometry("1100x750")
        self.root.configure(bg=BG_COLOR)

        self.arc = MtArc()
        self.arc.set_logger(self.log_message) # Route MtArc logs to the GUI logger

        self.is_dirty: bool = False # Tracks if archive has unsaved changes
        self.tree_item_map: Dict[str, str] = {} # Maps full path string to tree item ID (for folders)
        self.tree_iid_to_entry: Dict[int, AnyMtEntry] = {} # Maps tree item ID (int) to entry object (for files)
        self.tree_sort_column: str = "#0"
        self.tree_sort_reverse: bool = False
        self.hex_editor_popup: Optional[tk.Toplevel] = None

        self.setup_styles()
        self.setup_ui()
        self.redirect_print() # Redirect stdout/stderr to log widget

        self.set_status("Ready. Open an ARC file.")
        self.log_message("BurgerSoftware (Kuriimu2 Python Fork) - MT ARC Tool started.", level="INFO")
        self.log_message(f"Using filename encoding: {FILENAME_ENCODING}", level="DEBUG")
        if not _crcmod_available:
            self.log_message("crcmod library not found. Extension hashing will be limited.", level="WARN")
        self.update_button_states()

    def setup_styles(self):
        """Configures ttk styles for the dark theme."""
        style = ttk.Style(self.root)
        style.theme_use('clam') # Clam theme is usually better for custom styling

        # Try to increase default font size slightly
        try:
            default_font = tkinter.font.nametofont("TkDefaultFont")
            default_font.configure(size=default_font['size'] + 1)
            text_font = tkinter.font.nametofont("TkTextFont")
            text_font.configure(size=text_font['size'] + 1)
            fixed_font = tkinter.font.nametofont("TkFixedFont")
            fixed_font.configure(size=fixed_font['size'] + 1)
        except tk.TclError as font_error:
            self.log_message(f"Could not configure default fonts: {font_error}", "WARN")
            # Fallback font settings
            default_font = tkinter.font.Font(family="Segoe UI", size=10)

        # --- Configure Styles ---
        style.configure('.', background=BG_COLOR, foreground=TEXT_COLOR, fieldbackground=INPUT_BG,
                        bordercolor=BUTTON_BORDER, lightcolor=WIDGET_BG, darkcolor=BG_COLOR, font=default_font)
        style.map('.',
                  background=[('active', HIGHLIGHT_BG), ('disabled', '#555555')],
                  foreground=[('active', HIGHLIGHT_FG), ('disabled', '#999999')])

        style.configure("Dark.TFrame", background=BG_COLOR)
        style.configure("Dark.TLabelframe", background=BG_COLOR, bordercolor=TEXT_COLOR, relief=tk.GROOVE)
        style.configure("Dark.TLabelframe.Label", background=BG_COLOR, foreground=TEXT_COLOR, font=default_font)

        style.configure("Dark.TButton", background=BUTTON_BG, foreground=BUTTON_FG, relief=tk.RAISED,
                        borderwidth=1, bordercolor=BUTTON_BORDER, padding=6, focuscolor=HIGHLIGHT_FG, font=default_font)
        style.map("Dark.TButton",
                  background=[('pressed', BUTTON_ACTIVE_BG), ('active', HIGHLIGHT_BG)],
                  foreground=[('pressed', HIGHLIGHT_FG), ('active', HIGHLIGHT_FG)],
                  relief=[('pressed', tk.SUNKEN)])

        # Treeview Style
        style.configure("Dark.Treeview", background=WIDGET_BG, foreground=TEXT_COLOR,
                        fieldbackground=WIDGET_BG, rowheight=24, font=default_font)
        style.map("Dark.Treeview",
                  background=[('selected', HIGHLIGHT_BG)],
                  foreground=[('selected', HIGHLIGHT_FG)])

        # Treeview Heading Style
        style.configure("Dark.Treeview.Heading", background=HEADER_BG, foreground=HEADER_FG,
                        relief=tk.RAISED, padding=(6, 4), font=default_font)
        style.map("Dark.Treeview.Heading", background=[('active', HIGHLIGHT_BG)])

        # Scrollbar Styles
        style.configure("Dark.Vertical.TScrollbar", background=BUTTON_BG, troughcolor=WIDGET_BG,
                        bordercolor=BUTTON_BORDER, arrowcolor=TEXT_COLOR, relief=tk.FLAT)
        style.map("Dark.Vertical.TScrollbar", background=[('active', HIGHLIGHT_BG)])
        style.configure("Dark.Horizontal.TScrollbar", background=BUTTON_BG, troughcolor=WIDGET_BG,
                        bordercolor=BUTTON_BORDER, arrowcolor=TEXT_COLOR, relief=tk.FLAT)
        style.map("Dark.Horizontal.TScrollbar", background=[('active', HIGHLIGHT_BG)])

        # Entry Style
        style.configure("TEntry", fieldbackground=INPUT_BG, foreground=TEXT_COLOR, insertcolor=TEXT_COLOR,
                        bordercolor=BUTTON_BORDER, borderwidth=1, relief=tk.FLAT, font=default_font)

        # Status Bar Style
        style.configure("StatusBar.TLabel", background=STATUS_BAR_BG, foreground=TEXT_COLOR,
                        padding=(5, 3), relief=tk.FLAT, font=default_font)

        # --- Dialog Styles (Inherit where possible) ---
        style.configure("Dialog.TFrame", background=BG_COLOR)
        style.configure("Dialog.TLabel", background=BG_COLOR, foreground=TEXT_COLOR)
        style.configure("Dialog.TLabelframe", background=BG_COLOR, bordercolor=TEXT_COLOR)
        style.configure("Dialog.TLabelframe.Label", background=BG_COLOR, foreground=TEXT_COLOR)
        style.configure("Dialog.TButton", foreground=BUTTON_FG, bordercolor=BUTTON_BORDER) # Inherit background map
        style.map("Dialog.TButton",
                  background=[('pressed', BUTTON_ACTIVE_BG), ('active', HIGHLIGHT_BG), ('!active', BUTTON_BG)])
        style.configure("Dialog.TEntry", fieldbackground=INPUT_BG, foreground=TEXT_COLOR, insertcolor=TEXT_COLOR)
        style.configure("Dialog.Vertical.TScrollbar") # Inherit main scrollbar style
        style.map("Dialog.Vertical.TScrollbar", background=[('active', HIGHLIGHT_BG), ('!active', BUTTON_BG)])


    def setup_ui(self):
        """Creates and arranges all the GUI widgets."""
        # --- Menu Bar ---
        self.menu_bar = tk.Menu(self.root, bg=BG_COLOR, fg=TEXT_COLOR, activebackground=HIGHLIGHT_BG,
                                activeforeground=HIGHLIGHT_FG, relief=tk.FLAT, bd=0)
        # File Menu
        self.file_menu = tk.Menu(self.menu_bar, tearoff=0, bg=BUTTON_BG, fg=TEXT_COLOR,
                                 activebackground=HIGHLIGHT_BG, activeforeground=HIGHLIGHT_FG)
        self.file_menu.add_command(label="Open ARC", command=self.open_arc)
        self.file_menu.add_command(label="Save ARC As...", command=self.save_arc_as, state=tk.DISABLED)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="Batch Inject...", command=self.open_batch_inject_dialog)
        self.file_menu.add_command(label="Batch Extract...", command=self.open_batch_extract_dialog)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="Exit", command=self.on_exit)
        self.menu_bar.add_cascade(label="File", menu=self.file_menu)
        # Edit Menu (Placeholder)
        # self.edit_menu = tk.Menu(self.menu_bar, tearoff=0, ...)
        # self.menu_bar.add_cascade(label="Edit", menu=self.edit_menu, state=tk.DISABLED)

        self.root.config(menu=self.menu_bar)
        self.root.protocol("WM_DELETE_WINDOW", self.on_exit) # Handle window close button

        # --- Main Layout Panes ---
        # Horizontal split (Tree | Right Area)
        self.main_h_pane = tk.PanedWindow(self.root, orient=tk.HORIZONTAL, sashrelief=tk.RAISED,
                                         sashwidth=6, bg=BG_COLOR, sashpad=2) # Wider sash
        self.main_h_pane.pack(expand=True, fill=tk.BOTH, padx=5, pady=5)

        # --- Left Pane: Treeview ---
        self.tree_frame = ttk.Frame(self.main_h_pane, style="Dark.TFrame", padding="5")
        self.main_h_pane.add(self.tree_frame, stretch="never", minsize=350) # Initial width
        self.tree_frame.grid_rowconfigure(0, weight=1)
        self.tree_frame.grid_columnconfigure(0, weight=1)

        self.tree_scroll_y = ttk.Scrollbar(self.tree_frame, orient=tk.VERTICAL, style="Dark.Vertical.TScrollbar")
        self.tree_scroll_x = ttk.Scrollbar(self.tree_frame, orient=tk.HORIZONTAL, style="Dark.Horizontal.TScrollbar")

        self.tree = ttk.Treeview(self.tree_frame, columns=("Size", "CompSize", "Offset"),
                                 show="tree headings", yscrollcommand=self.tree_scroll_y.set,
                                 xscrollcommand=self.tree_scroll_x.set, selectmode="browse",
                                 style="Dark.Treeview")

        # Define headings
        self.tree.heading("#0", text="File Path", anchor=tk.W, command=lambda: self.sort_tree_column("#0", False))
        self.tree.heading("Size", text="Size", anchor=tk.E, command=lambda: self.sort_tree_column("Size", False))
        self.tree.heading("CompSize", text="Comp Size", anchor=tk.E, command=lambda: self.sort_tree_column("CompSize", False))
        self.tree.heading("Offset", text="Offset", anchor=tk.E, command=lambda: self.sort_tree_column("Offset", False))

        # Define column properties
        self.tree.column("#0", width=300, stretch=tk.YES, anchor=tk.W) # File path column
        self.tree.column("Size", width=90, stretch=tk.NO, anchor=tk.E)
        self.tree.column("CompSize", width=90, stretch=tk.NO, anchor=tk.E)
        self.tree.column("Offset", width=90, stretch=tk.NO, anchor=tk.E)

        # Link scrollbars
        self.tree_scroll_y.config(command=self.tree.yview)
        self.tree_scroll_x.config(command=self.tree.xview)

        # Grid layout for tree and scrollbars
        self.tree.grid(row=0, column=0, sticky="nsew")
        self.tree_scroll_y.grid(row=0, column=1, sticky="ns")
        self.tree_scroll_x.grid(row=1, column=0, columnspan=2, sticky="ew") # Span under tree and Y scroll

        # Bind events
        self.tree.bind('<<TreeviewSelect>>', self.on_tree_select)
        # self.tree.bind('<Double-1>', self.on_tree_double_click) # Optional: Add double-click action

        # --- Right Pane: Vertical Split (Hex Editor | Log) ---
        self.right_v_pane = tk.PanedWindow(self.main_h_pane, orient=tk.VERTICAL, sashrelief=tk.RAISED,
                                           sashwidth=6, bg=BG_COLOR, sashpad=2)
        self.main_h_pane.add(self.right_v_pane, stretch="always", minsize=550) # Allow right side to stretch

        # --- Top Right: Hex Editor ---
        self.hex_editor_frame_outer = ttk.LabelFrame(self.right_v_pane, text="Hex Editor",
                                                     style="Dark.TLabelframe", padding=5)
        self.right_v_pane.add(self.hex_editor_frame_outer, stretch="always", minsize=300) # Allow hex editor to stretch
        # Configure grid for HexEditorView inside the LabelFrame
        # self.hex_editor_frame_outer.grid_rowconfigure(0, weight=1) # Toolbar row (no weight)
        self.hex_editor_frame_outer.grid_rowconfigure(1, weight=1) # Hex view row should expand
        self.hex_editor_frame_outer.grid_columnconfigure(0, weight=1) # Make col 0 expand

        # Instantiate HexEditorView (will grid itself internally)
        self.hex_editor_view = HexEditorView(self.hex_editor_frame_outer, self, is_popup=False)
        # Grid HexEditorView in row 1 (below its own toolbar in row 0)
        self.hex_editor_view.grid(row=1, column=0, sticky="nsew")

        # --- Bottom Right: Log View ---
        self.log_frame = ttk.LabelFrame(self.right_v_pane, text="Console Log",
                                        style="Dark.TLabelframe", padding="5")
        self.right_v_pane.add(self.log_frame, stretch="never", minsize=150) # Fixed initial size for log
        self.log_frame.grid_rowconfigure(0, weight=1)
        self.log_frame.grid_columnconfigure(0, weight=1)

        log_font = ("Consolas", 10) if os.name == 'nt' else ("Monospace", 11)
        self.log_text = tk.Text(self.log_frame, height=10, width=80, wrap=tk.WORD, state=tk.DISABLED,
                                font=log_font, bg=WIDGET_BG, fg=TEXT_COLOR, relief=tk.FLAT, bd=0,
                                selectbackground=HIGHLIGHT_BG, selectforeground=HIGHLIGHT_FG,
                                insertbackground=TEXT_COLOR)
        log_scroll = ttk.Scrollbar(self.log_frame, orient=tk.VERTICAL, command=self.log_text.yview,
                                   style="Dark.Vertical.TScrollbar")
        self.log_text['yscrollcommand'] = log_scroll.set

        self.log_text.grid(row=0, column=0, sticky="nsew")
        log_scroll.grid(row=0, column=1, sticky="ns")

        # Configure log message tags
        self.log_text.tag_configure("timestamp", foreground="#888888") # Gray
        self.log_text.tag_configure("info", foreground=TEXT_COLOR)
        self.log_text.tag_configure("debug", foreground="cyan")
        self.log_text.tag_configure("print", foreground="lightblue") # For redirected print
        self.log_text.tag_configure("warn", foreground="yellow")
        self.log_text.tag_configure("error", foreground="orange")
        log_fatal_font = tkinter.font.Font(family=log_font[0], size=log_font[1], weight="bold")
        self.log_text.tag_configure("fatal", foreground="red", font=log_fatal_font)

        # --- Bottom Button Bar ---
        self.button_frame = ttk.Frame(self.root, style="Dark.TFrame", padding=(5, 0, 5, 5))
        self.button_frame.pack(fill=tk.X, side=tk.BOTTOM)

        self.extract_selected_btn = ttk.Button(self.button_frame, text="Extract Selected", command=self.extract_selected, state=tk.DISABLED, style="Dark.TButton")
        self.extract_all_btn = ttk.Button(self.button_frame, text="Extract All", command=self.extract_all, state=tk.DISABLED, style="Dark.TButton")
        self.add_files_btn = ttk.Button(self.button_frame, text="Add Files...", command=self.add_files, state=tk.DISABLED, style="Dark.TButton")
        self.remove_selected_btn = ttk.Button(self.button_frame, text="Remove Selected", command=self.remove_selected, state=tk.DISABLED, style="Dark.TButton")
        self.replace_selected_btn = ttk.Button(self.button_frame, text="Replace Selected...", command=self.replace_selected, state=tk.DISABLED, style="Dark.TButton")

        # Pack buttons left-to-right
        self.extract_selected_btn.pack(side=tk.LEFT, padx=5, pady=5)
        self.extract_all_btn.pack(side=tk.LEFT, padx=5, pady=5)
        self.add_files_btn.pack(side=tk.LEFT, padx=5, pady=5)
        self.remove_selected_btn.pack(side=tk.LEFT, padx=5, pady=5)
        self.replace_selected_btn.pack(side=tk.LEFT, padx=5, pady=5)

        # --- Status Bar ---
        self.status_var = tk.StringVar()
        self.status_bar = ttk.Label(self.root, textvariable=self.status_var, relief=tk.FLAT, anchor=tk.W,
                                    padding=(5, 3), style="StatusBar.TLabel")
        # Pack status bar *before* button bar if you want buttons above it
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)


    def log_message(self, message: str, level: str = "INFO"):
        """Appends a formatted message to the log Text widget."""
        try:
            timestamp = time.strftime("%H:%M:%S")
            tag = level.lower()
            if tag not in ["timestamp", "info", "debug", "print", "warn", "error", "fatal"]:
                tag = "info" # Default tag

            self.log_text.config(state=tk.NORMAL)
            # Insert timestamp and level marker with tags
            self.log_text.insert(tk.END, f"[{timestamp} ", ("timestamp",))
            self.log_text.insert(tk.END, f"{level}] ", (tag, "timestamp")) # Apply level tag too
            # Insert message with level tag
            self.log_text.insert(tk.END, f"{message}\n", (tag,))
            # Auto-scroll to the end
            self.log_text.see(tk.END)
            self.log_text.config(state=tk.DISABLED)
            # Update GUI immediately to show log message
            self.root.update_idletasks()
        except Exception as e:
            # Fallback to print if logging fails
            print(f"LOGGING ERROR: {e}")
            print(f"Original Message ({level}): {message}")

    class PrintRedirector:
        """Helper class to redirect stdout/stderr to the log_message method."""
        def __init__(self, log_method: Callable[[str, str], None]):
            self.log_method = log_method
            self.buffer = ""

        def write(self, message: str):
            self.buffer += message
            # Log complete lines immediately
            if '\n' in self.buffer:
                 lines = self.buffer.split('\n')
                 for line in lines[:-1]: # Log all lines except the potential partial last one
                      if line.strip(): # Avoid logging empty lines
                           self.log_method(line.strip(), "PRINT")
                 self.buffer = lines[-1] # Keep the partial line in buffer

        def flush(self):
            # Log any remaining buffer content on flush
            if self.buffer.strip():
                self.log_method(self.buffer.strip(), "PRINT")
            self.buffer = ""

    def redirect_print(self):
        """Redirects Python's print statements and stderr to the GUI log."""
        import sys
        sys.stdout = self.PrintRedirector(self.log_message)
        sys.stderr = self.PrintRedirector(self.log_message)

    def set_status(self, text: str, duration_ms: int = 0):
        """Updates the status bar text, optionally clearing it after a delay."""
        self.status_var.set(text)
        self.root.update_idletasks() # Ensure status bar updates immediately
        # If duration is set, schedule clearing the status bar
        if duration_ms > 0:
            # Use lambda to capture current text for comparison check
            current_text = text
            self.root.after(duration_ms,
                            lambda: self.status_var.set("Ready.") if self.status_var.get() == current_text else None)

    def mark_dirty(self, dirty: bool = True):
        """Updates the dirty state and window title."""
        if dirty == self.is_dirty:
            return # No change needed
        self.is_dirty = dirty

        # Update window title
        title = "BurgerSoftware (Kuriimu2 Python Fork) - MT ARC Tool"
        if self.arc.source_filepath:
            title += f" - {self.arc.source_filepath.name}"
        elif self.arc.entries: # Has entries but no source file (new ARC)
            title += " - [New ARC]"
        # Add asterisk if dirty
        if self.is_dirty:
            title += "*"

        self.root.title(title)
        # Update button states that depend on dirty status
        self.update_button_states()

    def update_button_states(self):
        """Enables/disables buttons based on the current state."""
        has_entries = bool(self.arc.entries)
        selected_iids = self.tree.selection()
        selected_entry_count = 0
        single_file_selected = False
        can_popout = False

        if selected_iids:
            iid_str = selected_iids[0] # Focus on the first selected item for single-item actions
            try:
                iid_int = int(iid_str)
                if iid_int in self.tree_iid_to_entry: # Check if it's a file entry
                    selected_entry_count = len(selected_iids) # How many items total are selected
                    # Check if *only* one file is selected
                    single_file_selected = selected_entry_count == 1
                    can_popout = True # Can pop out if at least one file is selected
                # else: it's a folder or invalid iid
            except (ValueError, tk.TclError):
                pass # Ignore errors during state update

        # Determine if save is possible
        can_save = self.is_dirty # Only allow saving if changes have been made

        # Update Menu Items
        self.file_menu.entryconfig("Save ARC As...", state=tk.NORMAL if can_save else tk.DISABLED)

        # Update Button Bar
        self.extract_selected_btn.config(state=tk.NORMAL if single_file_selected else tk.DISABLED)
        self.extract_all_btn.config(state=tk.NORMAL if has_entries else tk.DISABLED)
        # Allow adding files if an ARC is loaded (has path) OR if entries exist (new ARC)
        self.add_files_btn.config(state=tk.NORMAL if (self.arc.source_filepath or has_entries) else tk.DISABLED)
        self.remove_selected_btn.config(state=tk.NORMAL if single_file_selected else tk.DISABLED)
        self.replace_selected_btn.config(state=tk.NORMAL if single_file_selected else tk.DISABLED)

        # Update Hex Editor Buttons (Popout)
        if hasattr(self, 'hex_editor_view') and hasattr(self.hex_editor_view, 'popout_btn'):
            # Enable popout if a single file is selected AND the hex editor isn't already popped out
            self.hex_editor_view.popout_btn.config(state=tk.NORMAL if single_file_selected and not self.hex_editor_popup else tk.DISABLED)


    def populate_tree(self):
        """Clears and repopulates the Treeview with ARC entries."""
        # Clear existing items and mappings
        for item in self.tree.get_children():
            self.tree.delete(item)
        self.tree_item_map = {} # folder path -> iid
        self.tree_iid_to_entry = {} # file iid -> entry object

        if not self.arc.entries:
            self.set_status("ARC loaded is empty or no ARC loaded.")
            self.update_button_states()
            return

        self.set_status(f"Populating tree with {len(self.arc.entries)} entries...")
        # Sort entries alphabetically by full path for consistent display
        try:
             sorted_entries = sorted(self.arc.entries, key=lambda e: e.get_full_name())
        except Exception as sort_err:
             self.log_message(f"Error sorting entries for tree view: {sort_err}. Displaying in original order.", "WARN")
             sorted_entries = self.arc.entries

        folder_nodes: Dict[str, str] = {} # path -> iid

        for entry in sorted_entries:
            try:
                full_path = entry.get_full_name() # Handles separators internally
                path_parts = full_path.split('/')
                filename = path_parts[-1]
                parent_path = ""
                parent_iid = "" # Root node iid

                # Create folder nodes recursively
                for i, part in enumerate(path_parts[:-1]):
                    current_path = "/".join(path_parts[:i+1])
                    if current_path not in folder_nodes:
                        # Create folder node
                        folder_iid = self.tree.insert(parent_iid, tk.END, text=part, open=False, tags=('folder',))
                        folder_nodes[current_path] = folder_iid
                        parent_iid = folder_iid
                    else:
                        # Get existing folder node iid
                        parent_iid = folder_nodes[current_path]

                # Get entry details for display
                size = entry.get_decompressed_size(self.arc.platform)
                comp_size_val = entry.comp_size if entry.comp_size != -1 else -1
                offset_val = entry.offset if entry.offset != -1 else -1

                # Format values for display
                size_disp = f"{size:,}" if size >= 0 else "N/A"
                comp_size_disp = f"{comp_size_val:,}" if comp_size_val != -1 else "N/A" # -1 usually means not saved yet
                offset_disp = f"{offset_val:#0X}" if offset_val != -1 else "N/A" # -1 usually means not saved yet

                # Use the object's id() as the unique tree item ID
                # Store mapping from this ID back to the entry object
                file_iid_int = id(entry)
                self.tree_iid_to_entry[file_iid_int] = entry

                # Insert file node under its parent folder (or root)
                self.tree.insert(parent_iid, tk.END, iid=str(file_iid_int), text=filename,
                                 values=(size_disp, comp_size_disp, offset_disp), tags=('file',))
            except Exception as tree_err:
                entry_name = getattr(entry, 'file_name_str', '[unknown]')
                self.log_message(f"Error adding entry '{entry_name}' to tree: {tree_err}", "ERROR")
                self.log_message(traceback.format_exc(), "DEBUG")

        self.set_status(f"Tree populated with {len(self.arc.entries)} entries.")
        self.update_button_states()


    def get_selected_entries(self) -> list[AnyMtEntry]:
        """Returns a list of MtEntry objects corresponding to selected file items in the tree."""
        selected_iids_str = self.tree.selection()
        entries: list[AnyMtEntry] = []
        for iid_str in selected_iids_str:
            try:
                iid_int = int(iid_str)
                # Use the mapping to get the entry object
                if iid_int in self.tree_iid_to_entry:
                    entries.append(self.tree_iid_to_entry[iid_int])
            except ValueError:
                self.log_message(f"Invalid tree item ID encountered: {iid_str}", "WARN")
        return entries

    def sort_tree_column(self, col: str, reverse: bool):
        """Sorts the treeview items under their parents based on the clicked column."""
        selected_iids = self.tree.selection()
        parents_to_sort: Set[str] = set() # Set of parent item IDs

        # Determine which parent nodes need sorting
        if selected_iids:
            # If items are selected, sort only within their parent(s)
            for iid in selected_iids:
                try: parents_to_sort.add(self.tree.parent(iid))
                except tk.TclError: pass # Item might disappear during processing
        else:
            # If no selection, sort the root level
            parents_to_sort.add("")

        # Map column identifier to a sort key type
        col_map = {"#0": "name", "Size": "size", "CompSize": "compsize", "Offset": "offset"}
        sort_key_type = col_map.get(col)
        if not sort_key_type:
            self.log_message(f"Cannot sort by unknown column: {col}", "WARN")
            return

        self.log_message(f"Sorting column '{col}' (type: {sort_key_type}), reverse: {reverse}", "DEBUG")

        for parent_iid in parents_to_sort:
            children = list(self.tree.get_children(parent_iid))
            if not children: continue

            items_data: list[Dict[str, Any]] = []
            for child_iid_str in children:
                try:
                    tags = self.tree.item(child_iid_str, "tags")
                    is_folder = 'folder' in tags
                    item_text = self.tree.item(child_iid_str, "text") # Display name

                    # Default sort value is name
                    sort_val: Union[str, int] = item_text

                    if not is_folder:
                        # Get numerical values for sorting if it's a file
                        try: iid_int = int(child_iid_str)
                        except ValueError: continue # Skip invalid iid

                        if iid_int in self.tree_iid_to_entry:
                            entry_obj = self.tree_iid_to_entry[iid_int]
                            if sort_key_type == "size":
                                sort_val = entry_obj.get_decompressed_size(self.arc.platform)
                            elif sort_key_type == "compsize":
                                sort_val = entry_obj.comp_size if entry_obj.comp_size != -1 else -2 # Sort unsaved lower
                            elif sort_key_type == "offset":
                                sort_val = entry_obj.offset if entry_obj.offset != -1 else -2 # Sort unsaved lower
                        else: # File node but entry not found in map? Problem!
                            self.log_message(f"Tree node {child_iid_str} ('{item_text}') is file but not in entry map!", "ERROR")
                            # Assign default values for sorting anyway
                            if sort_key_type != "name": sort_val = -1

                    items_data.append({
                        'iid': child_iid_str,
                        'sort_key': sort_val,
                        'is_folder': is_folder
                    })
                except tk.TclError: continue # Item might have been deleted

            # Sort the collected data: folders first, then by sort_key
            try:
                items_data.sort(key=lambda x: (not x['is_folder'], x['sort_key']), reverse=reverse)
            except TypeError:
                # Handle cases where sort_key types might be mixed (e.g., str and int) -> sort by name as fallback
                self.log_message(f"Mixed types in column '{col}', sorting by name instead.", "WARN")
                items_data.sort(key=lambda x: (not x['is_folder'], self.tree.item(x['iid'], "text")), reverse=reverse)

            # Reorder items in the treeview
            for i, item_info in enumerate(items_data):
                try:
                    self.tree.move(item_info['iid'], parent_iid, i)
                except tk.TclError: continue # Item might have gone

        # Update the heading command to toggle reverse sort
        self.tree.heading(col, command=lambda c=col: self.sort_tree_column(c, not reverse))
        # Store current sort state
        self.tree_sort_column = col
        self.tree_sort_reverse = reverse


    def on_tree_select(self, event=None):
        """Handles selection changes in the Treeview, loads data into Hex Editor."""
        selected_iids = self.tree.selection()
        if not selected_iids:
            # No selection, clear hex editor
            self.hex_editor_view.clear()
            self.set_status("No item selected.")
            self.update_button_states()
            return

        # Process the first selected item for hex view
        iid_str = selected_iids[0]
        try:
            iid_int = int(iid_str)
            # Check if the selected item corresponds to a file entry
            if iid_int in self.tree_iid_to_entry:
                entry = self.tree_iid_to_entry[iid_int]
                entry_name = entry.get_full_name()
                self.log_message(f"Loading entry '{entry_name}' into Hex Editor...")
                self.set_status(f"Loading {entry_name}...")

                try:
                    # Get decompressed data for the hex view
                    data = self.arc.get_entry_data(entry, compressed=False)
                    if data is None:
                         # Error logged by get_entry_data
                         messagebox.showerror("Load Error", f"Failed to retrieve data for {entry_name}.")
                         self.hex_editor_view.clear()
                         self.set_status(f"Error loading {entry_name}.")
                    else:
                         self.hex_editor_view.load_data(entry, data)
                         self.set_status(f"Viewing {entry_name} ({len(data):,} bytes)")
                except Exception as e:
                    self.log_message(f"Error loading data for hex view ({entry_name}): {e}", "ERROR")
                    self.log_message(traceback.format_exc(), "DEBUG")
                    messagebox.showerror("Load Error", f"Failed to load data for {entry_name}:\n{e}")
                    self.hex_editor_view.clear()
                    self.set_status(f"Error loading data for {entry_name}.")
            else:
                # Selected item is likely a folder or invalid
                self.hex_editor_view.clear()
                try: item_text = self.tree.item(iid_str, "text")
                except tk.TclError: item_text = "[Item not found]"
                self.set_status(f"Selected item '{item_text}' is not a file.")
        except ValueError:
             self.log_message(f"Invalid tree item ID selected: {iid_str}", "ERROR")
             self.hex_editor_view.clear()
             self.set_status("Invalid item selected.")
        except tk.TclError:
             self.log_message(f"Selected tree item {iid_str} no longer exists.", "WARN")
             self.hex_editor_view.clear()
             self.set_status("Selected item no longer exists.")
        finally:
             # Always update button states after selection change
             self.update_button_states()


    def popout_hex_editor(self):
        """Moves the HexEditorView to a separate Toplevel window."""
        if self.hex_editor_popup:
            self.log_message("Hex editor is already popped out.", "WARN")
            return
        if not self.hex_editor_view.current_entry:
            self.log_message("No file loaded in hex editor to pop out.", "WARN")
            return

        # Create the popup window
        self.hex_editor_popup = tk.Toplevel(self.root)
        self.hex_editor_popup.title(f"Hex Editor - {self.hex_editor_view.current_entry.get_full_name()}")
        self.hex_editor_popup.geometry("800x600")
        self.hex_editor_popup.configure(bg=BG_COLOR)
        self.hex_editor_popup.transient(self.root) # Keep it above the main window
        self.hex_editor_popup.protocol("WM_DELETE_WINDOW", self.popin_hex_editor) # Handle close button

        # Move the HexEditorView instance
        # 1. Remove from current parent's grid
        self.hex_editor_view.grid_forget()
        # 2. Change master and state
        self.hex_editor_view.master = self.hex_editor_popup
        self.hex_editor_view.is_popup = True
        # 3. Re-grid inside the popup window
        #   (Create an intermediate frame in popup for better layout control if needed)
        popup_main_frame = ttk.Frame(self.hex_editor_popup, style="Dark.TFrame", padding=5)
        popup_main_frame.pack(expand=True, fill=tk.BOTH)
        popup_main_frame.grid_rowconfigure(1, weight=1) # Make row 1 (hex view) expand
        popup_main_frame.grid_columnconfigure(0, weight=1) # Make col 0 expand

        # Move the toolbar as well
        self.hex_editor_view.hex_toolbar.grid_forget()
        self.hex_editor_view.hex_toolbar.master = popup_main_frame # Toolbar belongs to the popup frame now
        self.hex_editor_view.hex_toolbar.grid(row=0, column=0, sticky="ew", columnspan=3) # Grid toolbar above hex view

        self.hex_editor_view.grid(row=1, column=0, sticky="nsew") # Grid hex view below toolbar

        # Update toolbar buttons for popup mode
        self.hex_editor_view.show_toolbar()
        # Update main window button state (e.g., disable popout button)
        self.update_button_states()
        self.log_message("Hex editor popped out.")

    def popin_hex_editor(self):
        """Moves the HexEditorView back to the main window."""
        if not self.hex_editor_popup:
            self.log_message("Hex editor is not popped out.", "WARN")
            return

        # Check for unsaved changes in the popup before closing
        if self.hex_editor_view.current_entry and self.hex_editor_view.apply_btn['state'] == tk.NORMAL:
            # Check the actual data state, not just button state
            # if self.hex_editor_view.current_entry.is_dirty: # More reliable check
            response = messagebox.askyesnocancel("Unapplied Changes",
                                                 "Apply changes made in the hex editor before popping in?",
                                                 parent=self.hex_editor_popup) # Ensure dialog is modal to popup
            if response is True: # Apply
                self.apply_hex_changes()
            elif response is False: # Discard
                self.log_message("Discarding hex editor changes.", "WARN")
                # Reload original data when popping back in
                if self.hex_editor_view.current_entry:
                     original_data = self.arc.get_entry_data(self.hex_editor_view.current_entry, compressed=False)
                     # Temporarily store it to be loaded after re-parenting
                     self._data_to_reload_on_popin = original_data
                     # Reset dirty state on the entry if needed
                     self.hex_editor_view.current_entry.is_dirty = False
                     self.hex_editor_view.current_entry.data_to_write = None
                     self.mark_dirty(False) # May need re-evaluation if other things are dirty
                else:
                     self._data_to_reload_on_popin = None

            else: # Cancel
                return # Do nothing, keep popup open

        # Move the HexEditorView instance back
        # 1. Remove from popup grid
        self.hex_editor_view.grid_forget()
        self.hex_editor_view.hex_toolbar.grid_forget()
        # 2. Change master back to original frame and state
        self.hex_editor_view.master = self.hex_editor_frame_outer
        self.hex_editor_view.is_popup = False
        self.hex_editor_view.hex_toolbar.master = self.hex_editor_view # Toolbar belongs to hex view frame again
        # 3. Re-grid inside the main window's frame
        self.hex_editor_view.hex_toolbar.grid(row=0, column=0, columnspan=3, sticky=tk.EW, pady=(0, 5))
        self.hex_editor_view.grid(row=1, column=0, columnspan=3, sticky="nsew") # Span cols in main frame

        # Update toolbar buttons for embedded mode
        self.hex_editor_view.show_toolbar()
        # Destroy the popup window
        self.hex_editor_popup.destroy()
        self.hex_editor_popup = None

        # Reload data if discard was chosen
        if hasattr(self, '_data_to_reload_on_popin') and self._data_to_reload_on_popin is not None:
             if self.hex_editor_view.current_entry:
                  self.hex_editor_view.load_data(self.hex_editor_view.current_entry, self._data_to_reload_on_popin)
             del self._data_to_reload_on_popin # Clean up temp storage


        # Update main window button state
        self.update_button_states()
        self.log_message("Hex editor popped in.")

    def apply_hex_changes(self):
        """Applies changes from the HexEditorView to the underlying MtArc entry."""
        # Check if editor is active and has an entry
        if self.hex_editor_view and self.hex_editor_view.current_entry:
            self.hex_editor_view.apply_changes() # Let the view handle its logic
        else:
            self.log_message("Cannot apply hex changes: editor not active or no entry loaded.", "WARN")


    # --- Action Methods ---
    def open_arc(self):
        """Opens an ARC file using a file dialog."""
        if self.is_dirty:
            if not messagebox.askyesno("Unsaved Changes", "Discard unsaved changes and open a new file?"):
                return

        filepath = filedialog.askopenfilename(
            title="Open MT ARC File",
            filetypes=(("ARC files", "*.arc"), ("All files", "*.*"))
        )
        if not filepath:
            return # User cancelled

        try:
            self.set_status(f"Loading {os.path.basename(filepath)}...")
            # Close previous ARC and clear UI state
            if self.arc:
                self.arc.close()
            self.hex_editor_view.clear() # Clear hex view

            # Load new ARC
            self.arc = MtArc() # Create new instance
            self.arc.set_logger(self.log_message) # Set logger again
            self.arc.load(filepath)

            # Update UI
            self.populate_tree()
            self.set_status(f"Loaded {len(self.arc.entries)} files from {os.path.basename(filepath)}")
            self.mark_dirty(False) # Mark as clean after load

        except Exception as e:
            self.log_message(f"Failed to load ARC file '{filepath}': {e}", "ERROR")
            self.log_message(traceback.format_exc(), "DEBUG")
            messagebox.showerror("Error Loading ARC", f"Failed to load the ARC file:\n{e}\n\nSee log for details.")
            # Reset state
            self.arc = MtArc()
            self.arc.set_logger(self.log_message)
            self.populate_tree() # Clear tree
            self.mark_dirty(False)
            self.set_status("Failed to load ARC.")
        finally:
            # Always update button states after attempt
            self.update_button_states()


    def save_arc_as(self):
        """Saves the current ARC contents to a new file."""
        if not self.is_dirty:
             # Optional: Allow saving even if not dirty? For now, require changes.
            messagebox.showwarning("Save Error", "No unsaved changes to save.")
            return
        # If entries list is empty but header exists (maybe loaded an empty ARC?), allow save?
        # if not self.arc.entries and not self.arc.header: # Stricter check
        #     messagebox.showwarning("Save Error", "Nothing to save.")
        #     return

        # Ensure any pending hex changes are applied before saving
        if self.hex_editor_popup and self.hex_editor_view.apply_btn['state'] == tk.NORMAL:
             self.log_message("Applying pending hex changes from popup before saving...", "INFO")
             self.apply_hex_changes()
        # Check embedded editor too? If apply_changes is tied to the popup button,
        # embedded changes might be staged but not "applied".
        # The save logic uses entry.data_to_write, which *should* be up-to-date
        # if handle_edit ran correctly. Let's rely on that.

        # Suggest filename
        initial_name = self.arc.source_filepath.name if self.arc.source_filepath else "Untitled.arc"
        filepath = filedialog.asksaveasfilename(
            title="Save ARC As",
            initialfile=initial_name,
            defaultextension=".arc",
            filetypes=(("ARC files", "*.arc"), ("All files", "*.*"))
        )
        if not filepath:
            return # User cancelled

        try:
            self.set_status(f"Saving ARC to {os.path.basename(filepath)}...")
            start_time = time.time()

            # Perform the save operation
            self.arc.save(filepath)

            end_time = time.time()
            self.set_status(f"Saved {len(self.arc.entries)} files to {os.path.basename(filepath)} in {end_time - start_time:.2f}s")
            self.mark_dirty(False) # Mark as clean after successful save
            # Repopulate tree to show updated offsets/sizes
            self.populate_tree()

        except Exception as e:
            self.log_message(f"Failed to save ARC file to '{filepath}': {e}", "ERROR")
            self.log_message(traceback.format_exc(), "DEBUG")
            messagebox.showerror("Error Saving ARC", f"Failed to save the ARC file:\n{e}\n\nSee log for details.")
            self.set_status("Saving failed.")
        finally:
            self.update_button_states()


    def extract_selected(self):
        """Extracts the currently selected single file entry."""
        selected_entries = self.get_selected_entries()
        if not selected_entries:
            messagebox.showwarning("Extraction", "No file selected in the tree.")
            return
        if len(selected_entries) > 1:
             messagebox.showwarning("Extraction", "Please select only one file to extract.")
             return

        entry_to_extract = selected_entries[0]
        entry_name = entry_to_extract.get_full_name()

        output_dir = filedialog.askdirectory(title=f"Select Extraction Directory for '{entry_name}'")
        if not output_dir:
            return # User cancelled

        self.set_status(f"Extracting {entry_name}...")
        self.log_message(f"Extracting selected file '{entry_name}' to: {output_dir}")
        start_time = time.time()

        try:
            success = self.arc.extract_entry(entry_to_extract, output_dir)
            end_time = time.time()
            if success:
                msg = f"Extracted '{entry_name}' in {end_time - start_time:.2f}s."
                self.log_message(msg)
                self.set_status(msg, duration_ms=5000)
            else:
                # Error logged by extract_entry
                msg = f"Failed to extract '{entry_name}'."
                messagebox.showerror("Extraction Error", f"{msg}\nCheck log for details.")
                self.set_status(msg)
        except Exception as e:
            self.log_message(f"Extraction failed for {entry_name}: {e}", "ERROR")
            self.log_message(traceback.format_exc(), "DEBUG")
            messagebox.showerror("Extraction Error", f"An unexpected error occurred during extraction:\n{e}")
            self.set_status("Extraction failed.")


    def extract_all(self):
        """Extracts all entries from the ARC."""
        if not self.arc.entries:
            messagebox.showwarning("Extraction", "The ARC is empty, nothing to extract.")
            return

        output_dir = filedialog.askdirectory(title="Select Base Directory for Extraction")
        if not output_dir:
            return # User cancelled

        total_files = len(self.arc.entries)
        self.set_status(f"Starting extraction of {total_files} files...")
        self.log_message(f"Extracting all {total_files} files to: {output_dir}")
        extracted_count, failed_count = 0, 0
        start_time = time.time()

        try:
            for i, entry in enumerate(self.arc.entries):
                # Update status periodically
                if (i + 1) % 50 == 0 or i == total_files - 1:
                    self.set_status(f"Extracting {i + 1}/{total_files}...")

                if self.arc.extract_entry(entry, output_dir):
                    extracted_count += 1
                else:
                    failed_count += 1
                    # Error already logged by extract_entry

            end_time = time.time()
            msg = f"Extraction complete. Extracted: {extracted_count}, Failed: {failed_count}."
            elapsed = end_time - start_time
            self.log_message(f"{msg} Time: {elapsed:.2f}s.")
            if failed_count > 0:
                 messagebox.showwarning("Extraction Complete", f"{msg}\nCheck log for details on failures.")
            else:
                 messagebox.showinfo("Extraction Complete", msg)
            self.set_status(msg, duration_ms=5000)

        except Exception as e:
            self.log_message(f"Batch extraction failed: {e}", "ERROR")
            self.log_message(traceback.format_exc(), "DEBUG")
            messagebox.showerror("Extraction Error", f"An unexpected error occurred during batch extraction:\n{e}")
            self.set_status("Extraction failed.")


    def add_files(self):
        """Opens a dialog to select files from the filesystem to add to the ARC."""
        # Check if an ARC is loaded or being created
        if not self.arc.source_filepath and not self.arc.entries:
            messagebox.showwarning("Add Files Error", "Please open an ARC file first or start adding files to a new one.")
            return

        files_to_add = filedialog.askopenfilenames(title="Select Files to Add to ARC")
        if not files_to_add:
            return # User cancelled

        # TODO: Implement asking user for destination folder within the archive?
        # For now, add to root.
        dest_folder_in_archive = ""

        self.set_status(f"Adding {len(files_to_add)} file(s)...")
        self.log_message(f"Attempting to add {len(files_to_add)} file(s)...")
        added_count = 0
        failed_files = []
        start_time = time.time()

        for f_path_str in files_to_add:
            f_path = Path(f_path_str)
            file_name = f_path.name
            # Construct path within the archive (handle potential empty dest folder)
            archive_path = f"{dest_folder_in_archive}/{file_name}" if dest_folder_in_archive else file_name
            archive_path = archive_path.replace('\\', '/') # Ensure forward slashes

            self.log_message(f"Adding '{f_path}' as '{archive_path}'...", "DEBUG")
            added_entry = self.arc.add_entry(f_path, archive_path)

            if added_entry:
                added_count += 1
            else:
                failed_files.append(file_name)
                # Error logged by add_entry

        end_time = time.time()

        if added_count > 0:
            self.populate_tree() # Refresh tree view
            self.mark_dirty(True) # Mark archive as modified
            msg = f"Added {added_count} file(s) in {end_time - start_time:.2f}s."
            if failed_files:
                 msg += f" Failed to add: {', '.join(failed_files)}."
                 self.log_message(msg, "WARN")
            else:
                 self.log_message(msg)
            self.set_status(f"{msg} Save required.", duration_ms=5000)
        else:
            msg = "No files were added."
            if failed_files:
                msg += f" Failed attempts: {', '.join(failed_files)}."
            self.log_message(msg, "WARN")
            self.set_status(msg, duration_ms=3000)


    def remove_selected(self):
        """Removes the currently selected single file entry from the ARC."""
        selected_entries = self.get_selected_entries()
        if not selected_entries:
            messagebox.showwarning("Remove Error", "No file selected to remove.")
            return
        if len(selected_entries) > 1:
             messagebox.showwarning("Remove Error", "Please select only one file to remove.")
             return

        entry_to_remove = selected_entries[0]
        entry_name = entry_to_remove.get_full_name()

        confirm = messagebox.askyesno("Confirm Removal", f"Are you sure you want to remove '{entry_name}'?\n\nThis action requires saving the ARC afterwards.")
        if not confirm:
            return

        self.log_message(f"Removing selected file: {entry_name}")
        start_time = time.time()

        # Check if the removed entry is currently displayed in hex editor
        removed_current_hex = (self.hex_editor_view.current_entry == entry_to_remove)

        success = self.arc.remove_entry(entry_to_remove)
        end_time = time.time()

        if success:
            if removed_current_hex:
                self.hex_editor_view.clear() # Clear hex view if removed item was shown
            self.populate_tree() # Refresh tree view
            self.mark_dirty(True) # Mark archive as modified
            msg = f"Removed '{entry_name}' in {end_time - start_time:.2f}s. Save required."
            self.log_message(msg)
            self.set_status(msg, duration_ms=5000)
        else:
            # Error logged by remove_entry
            msg = f"Failed to remove '{entry_name}'."
            messagebox.showerror("Remove Error", msg)
            self.set_status(msg)


    def replace_selected(self):
        """Replaces the data of the selected file entry with data from a filesystem file."""
        selected_entries = self.get_selected_entries()
        if not selected_entries:
            messagebox.showwarning("Replace Error", "No file selected to replace.")
            return
        if len(selected_entries) > 1:
             messagebox.showwarning("Replace Error", "Please select only one file to replace.")
             return

        entry_to_replace = selected_entries[0]
        entry_name = entry_to_replace.get_full_name()

        # Ask user for the replacement file
        file_to_import = filedialog.askopenfilename(
            title=f"Select Replacement File for '{entry_name}'"
        )
        if not file_to_import:
            return # User cancelled

        self.log_message(f"Replacing '{entry_name}' with data from '{file_to_import}'...")
        start_time = time.time()

        try:
            # Read new data
            with open(file_to_import, 'rb') as f_rep:
                new_data = f_rep.read()

            # Replace data in the MtArc object
            success = self.arc.replace_entry_data(entry_to_replace, new_data)
            end_time = time.time()

            if success:
                # If the replaced entry is shown in hex view, reload it
                if self.hex_editor_view.current_entry == entry_to_replace:
                    self.hex_editor_view.load_data(entry_to_replace, new_data)

                # Refresh tree (sizes might change) and mark dirty
                self.populate_tree()
                self.mark_dirty(True)
                msg = f"Staged replacement for '{entry_name}' ({len(new_data):,} bytes) in {end_time - start_time:.2f}s. Save required."
                self.log_message(msg)
                self.set_status(msg, duration_ms=5000)
            else:
                # Error logged by replace_entry_data
                msg = f"Failed to stage replacement for '{entry_name}'."
                messagebox.showerror("Replace Error", f"{msg}\nCheck log for details.")
                self.set_status(msg)

        except Exception as e:
            self.log_message(f"Replacement failed for {entry_name}: {e}", "ERROR")
            self.log_message(traceback.format_exc(), "DEBUG")
            messagebox.showerror("Replace Error", f"An unexpected error occurred during replacement:\n{e}")
            self.set_status("Replacement error.")


    # --- Batch Operations ---
    def open_batch_inject_dialog(self):
        """Opens the dialog for batch injecting files into ARCs."""
        if self.is_dirty:
            messagebox.showwarning("Unsaved Changes", "Please save or discard changes to the current ARC before starting a batch operation.")
            return

        # Close current ARC if open
        if self.arc and (self.arc.source_filepath or self.arc.entries):
            self.log_message("Closing current ARC before batch injection.")
            self.arc.close()
            self.arc = MtArc()
            self.arc.set_logger(self.log_message)
            self.populate_tree()
            self.mark_dirty(False)
            self.hex_editor_view.clear()
            self.set_status("Ready for batch operation.")

        # Open dialog
        dialog = BatchInjectDialog(self)
        dialog.wait_window() # Wait for dialog to close

    def run_batch_injection(self, original_dir: str, modified_base_dir: str, output_dir: str, log_callback: Callable[[str, str], None]):
        """Performs the batch injection logic (called by the dialog)."""
        # Stats counters
        arc_files_processed = 0
        arc_files_skipped_no_mod_folder = 0
        arc_files_failed_load = 0
        arc_files_failed_save = 0
        arc_files_skipped_no_changes = 0
        total_files_replaced = 0
        total_files_failed_replace = 0 # Includes read/stage errors
        start_batch_time = time.time()

        original_path = Path(original_dir)
        modified_base_path = Path(modified_base_dir)
        output_path = Path(output_dir)

        try:
            # Find all .arc files directly in the original directory (not recursive)
            arc_filepaths = list(original_path.glob('*.arc'))
            total_arcs_found = len(arc_filepaths)
            log_callback(f"Found {total_arcs_found} ARC file(s) in {original_path}", "INFO")
        except Exception as e:
            log_callback(f"[FATAL] Error scanning for ARC files in {original_path}: {e}", "FATAL")
            return

        if not arc_filepaths:
            log_callback("No .arc files found in the original directory.", "INFO")
            return

        # Process each ARC file
        for i, arc_filepath in enumerate(arc_filepaths):
            arc_filename = arc_filepath.name
            # Corresponding folder in the modified directory structure
            modified_arc_folder = modified_base_path / arc_filename.replace(arc_filepath.suffix, '') # Use filename without .arc

            log_callback(f"\n--- Processing ARC {i + 1}/{total_arcs_found}: {arc_filename} ---", "INFO")

            # Check if the corresponding folder with modified files exists
            if not modified_arc_folder.is_dir():
                log_callback(f"  [SKIP] Modified files folder not found: {modified_arc_folder}", "WARN")
                arc_files_skipped_no_mod_folder += 1
                continue

            # Create a temporary MtArc instance for this file
            batch_arc = MtArc()
            # Use a lambda to prefix logs from this instance within the dialog log
            batch_arc.set_logger(lambda msg, level="INFO": log_callback(f"    {msg}", level))

            try:
                # Load the original ARC
                batch_arc.load(arc_filepath)
                log_callback(f"  Loaded original ARC ({len(batch_arc.entries)} entries).", "INFO")
            except Exception as e:
                log_callback(f"  [FAIL] Failed to load original ARC: {e}. Skipping.", "ERROR")
                log_callback(traceback.format_exc(), "DEBUG")
                arc_files_failed_load += 1
                batch_arc.close() # Ensure handle is closed
                continue

            # Iterate through entries and check for replacements
            files_replaced_in_arc = 0
            files_failed_in_arc = 0
            files_skipped_in_arc = 0
            arc_modified_flag = False

            for entry in batch_arc.entries:
                entry_archive_path_str = entry.get_full_name() # e.g., "native/path/to/file.tex"
                # Construct expected path for the modified file
                expected_mod_filepath = modified_arc_folder / entry_archive_path_str

                if expected_mod_filepath.is_file():
                    log_callback(f"    Found replacement: {expected_mod_filepath.relative_to(modified_base_path)}", "DEBUG")
                    try:
                        # Read replacement data
                        with open(expected_mod_filepath, 'rb') as mod_f:
                            new_data_bytes = mod_f.read()

                        # Stage the replacement
                        if batch_arc.replace_entry_data(entry, new_data_bytes):
                            files_replaced_in_arc += 1
                            arc_modified_flag = True # Mark ARC as needing save
                        else:
                            # Error staging (already logged by replace_entry_data)
                            files_failed_in_arc += 1
                    except Exception as read_err:
                        log_callback(f"    [FAIL] Error reading replacement file {expected_mod_filepath}: {read_err}", "ERROR")
                        files_failed_in_arc += 1
                else:
                    # No replacement file found for this entry
                    files_skipped_in_arc += 1

            log_callback(f"  Replacement scan done: Replaced={files_replaced_in_arc}, Failed={files_failed_in_arc}, Skipped={files_skipped_in_arc}.", "INFO")

            # Save the modified ARC if changes were made
            if arc_modified_flag:
                output_arc_path = output_path / arc_filename
                log_callback(f"  Saving modified ARC to: {output_arc_path}", "INFO")
                try:
                    # Ensure output directory exists
                    output_arc_path.parent.mkdir(parents=True, exist_ok=True)
                    batch_arc.save(output_arc_path)
                    log_callback(f"  Successfully saved {arc_filename}.", "INFO")
                    arc_files_processed += 1
                    total_files_replaced += files_replaced_in_arc
                    total_files_failed_replace += files_failed_in_arc
                except Exception as e:
                    log_callback(f"  [FAIL] Error saving modified ARC {output_arc_path}: {e}", "ERROR")
                    log_callback(traceback.format_exc(), "DEBUG")
                    arc_files_failed_save += 1
                    # Keep track of file failures even if save fails
                    total_files_failed_replace += files_failed_in_arc
            else:
                log_callback(f"  No modifications needed for {arc_filename}. Skipping save.", "INFO")
                arc_files_skipped_no_changes += 1

            # Clean up the temporary ARC instance
            batch_arc.close()

        # Batch finished, print summary
        end_batch_time = time.time()
        log_callback("\n" + "="*30, "INFO")
        log_callback("--- Batch Injection Summary ---", "INFO")
        log_callback(f"Total Time: {end_batch_time - start_batch_time:.2f} seconds", "INFO")
        log_callback(f"ARCs Found: {total_arcs_found}", "INFO")
        log_callback(f"ARCs Saved Successfully: {arc_files_processed}", "INFO")
        log_callback(f"ARCs Skipped (No Mod Folder): {arc_files_skipped_no_mod_folder}", "INFO")
        log_callback(f"ARCs Skipped (No Changes): {arc_files_skipped_no_changes}", "INFO")
        log_callback(f"ARCs Failed (Load Error): {arc_files_failed_load}", "INFO")
        log_callback(f"ARCs Failed (Save Error): {arc_files_failed_save}", "INFO")
        log_callback(f"Total Files Replaced Successfully (in saved ARCs): {total_files_replaced}", "INFO")
        log_callback(f"Total File Replacement Failures (Read/Stage errors): {total_files_failed_replace}", "INFO")
        log_callback("="*30, "INFO")


    def open_batch_extract_dialog(self):
        """Opens the dialog for batch extracting ARCs."""
        if self.is_dirty:
            messagebox.showwarning("Unsaved Changes", "Please save or discard changes to the current ARC before starting a batch operation.")
            return

        # Close current ARC if open
        if self.arc and (self.arc.source_filepath or self.arc.entries):
             self.log_message("Closing current ARC before batch extraction.")
             self.arc.close()
             self.arc = MtArc()
             self.arc.set_logger(self.log_message)
             self.populate_tree()
             self.mark_dirty(False)
             self.hex_editor_view.clear()
             self.set_status("Ready for batch operation.")

        # Open dialog
        dialog = BatchExtractDialog(self)
        dialog.wait_window() # Wait for dialog to close


    def run_batch_extraction(self, input_arc_dir: str, output_base_dir: str, log_callback: Callable[[str, str], None]):
        """Performs the batch extraction logic using threads (called by the dialog)."""
        # Stats counters
        arc_files_processed = 0
        arc_files_failed_load = 0
        arc_files_with_extract_errors = 0
        total_files_extracted = 0
        total_files_failed_extract = 0
        start_batch_time = time.time()

        input_path = Path(input_arc_dir)
        output_path = Path(output_base_dir)

        log_callback(f"Searching for *.arc files recursively in: {input_path}", "INFO")
        try:
            arc_filepaths = list(input_path.rglob('*.arc'))
            total_arcs_found = len(arc_filepaths)
            log_callback(f"Found {total_arcs_found} .arc file(s).", "INFO")
        except Exception as e:
            log_callback(f"[FATAL] Error scanning for ARC files in {input_path}: {e}", "FATAL")
            return

        if not arc_filepaths:
            log_callback("No .arc files found.", "INFO")
            return

        # Use ThreadPoolExecutor for concurrent extraction
        # Adjust max_workers based on CPU count, but keep it reasonable
        max_workers = min(16, (os.cpu_count() or 1) * 2)
        log_callback(f"Starting batch extraction with up to {max_workers} worker threads...", "INFO")

        # Use a queue for thread-safe logging from workers
        log_queue = queue.Queue()
        # Start a dedicated thread to process log messages from the queue
        log_thread = threading.Thread(target=self._log_updater_thread, args=(log_queue, log_callback), daemon=True)
        log_thread.start()

        futures: List[concurrent.futures.Future] = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
            # Submit all ARC processing tasks
            for arc_filepath in arc_filepaths:
                futures.append(executor.submit(self._process_single_arc_extraction, arc_filepath, input_path, output_path, log_queue))

            processed_count = 0
            # Process results as they complete
            for future in concurrent.futures.as_completed(futures):
                processed_count += 1
                try:
                    result = future.result() # Get result dictionary from worker
                    if result: # Check if result is not None (in case of early error)
                        if result["processed"]: arc_files_processed += 1
                        if result["load_fail"]: arc_files_failed_load += 1
                        if result["arc_had_error"]: arc_files_with_extract_errors += 1
                        total_files_extracted += result["extract_ok_count"]
                        total_files_failed_extract += result["extract_fail_count"]

                    # Log progress periodically
                    if processed_count % 100 == 0 or processed_count == total_arcs_found:
                        elapsed = time.time() - start_batch_time
                        log_queue.put(f"--- Progress: {processed_count}/{total_arcs_found} ARCs processed ({elapsed:.1f}s) ---")

                except Exception as exc:
                    # Catch errors from the worker thread itself (should ideally be caught within worker)
                    log_queue.put(f"[FATAL] Worker thread encountered an unhandled exception: {exc}")
                    log_queue.put(traceback.format_exc())
                    arc_files_failed_load += 1 # Count as a load failure

        # Signal logger thread to finish and wait for it
        log_callback("Waiting for final log messages...", "DEBUG")
        log_queue.put("---QUIT---") # Sentinel value to stop logger thread
        log_thread.join(timeout=5) # Wait max 5 seconds for logger to finish
        if log_thread.is_alive():
            log_callback("[WARN] Logger thread did not exit cleanly.", "WARN")

        # Batch finished, print summary using the main log_callback
        end_batch_time = time.time()
        log_callback("\n" + "="*30, "INFO")
        log_callback("--- Batch Extraction Summary ---", "INFO")
        log_callback(f"Total Time: {end_batch_time - start_batch_time:.2f} seconds", "INFO")
        log_callback(f"ARCs Found: {total_arcs_found}", "INFO")
        log_callback(f"ARCs Processed Successfully: {arc_files_processed}", "INFO")
        log_callback(f"ARCs Skipped/Failed Load: {arc_files_failed_load}", "INFO")
        log_callback(f"ARCs with Extraction Errors: {arc_files_with_extract_errors}", "INFO")
        log_callback(f"Total Files Extracted: {total_files_extracted}", "INFO")
        log_callback(f"Total File Extraction Failures: {total_files_failed_extract}", "INFO")
        log_callback("="*30, "INFO")


    # --- Worker function for batch extraction (runs in a separate thread) ---
    def _process_single_arc_extraction(self, arc_filepath: Path, input_path: Path, output_path: Path, log_queue: queue.Queue) -> Dict[str, Any]:
        """Processes a single ARC file for extraction."""
        # Helper function for logging from this thread via the queue
        def thread_log(message: str, level: str = "INFO"):
            # Add context (e.g., relative path) to the message
            log_queue.put(f"[{level}] {relative_arc_path_str}: {message}")

        relative_arc_path: Optional[Path] = None
        relative_arc_path_str = arc_filepath.name # Default context for logging early errors

        result = {
            "processed": False,
            "load_fail": False,
            "arc_had_error": False,
            "extract_ok_count": 0,
            "extract_fail_count": 0
        }

        try:
            # Calculate relative path for output structure
            abs_arc_filepath = arc_filepath.resolve()
            abs_input_path = input_path.resolve()
            relative_arc_path = abs_arc_filepath.relative_to(abs_input_path)
            relative_arc_path_str = str(relative_arc_path) # Update context for logging

            # Construct the specific output directory for this ARC's contents
            # Remove the .arc extension for the directory name
            output_arc_extract_dir = output_path / relative_arc_path.with_suffix('')
            thread_log(f"Starting extraction to {output_arc_extract_dir.relative_to(output_path)}", "DEBUG")

            # Ensure output directory exists
            output_arc_extract_dir.mkdir(parents=True, exist_ok=True)

            # Create temporary MtArc instance
            batch_arc = MtArc()
            # Suppress most INFO/DEBUG logs from MtArc within the thread log
            batch_arc.set_logger(lambda msg, level="INFO": thread_log(f"  {msg}", level) if level not in ["INFO", "DEBUG"] else None)

            # Load the ARC
            batch_arc.load(arc_filepath)

            # Extract entries
            for entry in batch_arc.entries:
                if batch_arc.extract_entry(entry, str(output_arc_extract_dir)):
                    result["extract_ok_count"] += 1
                else:
                    result["extract_fail_count"] += 1
                    result["arc_had_error"] = True # Mark ARC as having errors

            result["processed"] = True # Mark as processed if load succeeded

        except FileNotFoundError:
            thread_log(f"Original ARC not found (possibly deleted during scan?). Skipping.", "ERROR")
            result["load_fail"] = True
        except ValueError as ve: # Catches relative_to errors, unknown format
             thread_log(f"Skipping - Error determining relative path or unknown format: {ve}", "ERROR")
             result["load_fail"] = True
        except Exception as e:
             thread_log(f"Failed processing: {e}", "ERROR")
             thread_log(traceback.format_exc(), "DEBUG")
             result["load_fail"] = True # Treat any exception during load/process as load failure
             result["arc_had_error"] = True # Assume errors occurred if load failed mid-way
        finally:
            # Ensure ARC handle is closed if batch_arc was instantiated
            if 'batch_arc' in locals():
                 batch_arc.close()

        if result["processed"]:
             thread_log(f"Finished. Extracted: {result['extract_ok_count']}, Failed: {result['extract_fail_count']}", "INFO")
        else:
             thread_log(f"Finished with errors.", "WARN")

        return result

    # --- Log updater thread target ---
    def _log_updater_thread(self, log_queue: queue.Queue, main_log_callback: Callable[[str, str], None]):
        """Daemon thread function to get messages from queue and call the main logger."""
        while True:
            try:
                # Get message from queue, block if empty (with timeout to allow checking quit flag)
                message = log_queue.get(block=True, timeout=0.5)

                if message == "---QUIT---":
                    # print("Log updater thread received QUIT signal.") # Debug print
                    log_queue.task_done()
                    break # Exit the loop

                # Determine log level from message prefix (simple approach)
                level = "INFO" # Default
                if isinstance(message, str):
                    if message.startswith("[FATAL]"): level = "FATAL"
                    elif message.startswith("[ERROR]"): level = "ERROR"
                    elif message.startswith("[WARN]"): level = "WARN"
                    elif message.startswith("[DEBUG]"): level = "DEBUG"
                    elif message.startswith("---"): level = "INFO" # For separators

                # Use root.after_idle to safely call the main GUI logger from this thread
                self.root.after_idle(main_log_callback, message, level)
                log_queue.task_done() # Mark task as done

            except queue.Empty:
                # Timeout occurred, just continue loop to check quit flag again
                continue
            except Exception as e:
                # Log errors occurring *in the logger thread itself* to stderr
                print(f"Log updater thread error: {e}", file=sys.stderr)
                print(traceback.format_exc(), file=sys.stderr)


    def on_exit(self):
         """Handles application closing."""
         if self.is_dirty:
              if not messagebox.askyesno("Exit Confirmation", "There are unsaved changes. Are you sure you want to exit?"):
                  return # User cancelled exit

         # Close ARC file handle if open
         if self.arc:
             self.arc.close()

         # Destroy popup window if it exists
         if self.hex_editor_popup:
              try:
                  self.hex_editor_popup.destroy()
              except tk.TclError:
                  pass # Window might already be destroyed

         self.log_message("Exiting BurgerSoftware (Kuriimu2 Python Fork).")
         # Perform any other cleanup here
         self.root.destroy()


# --- Batch Injection Dialog Class ---
class BatchInjectDialog(tk.Toplevel):
    def __init__(self, app_instance: MtArcToolApp):
        super().__init__(app_instance.root)
        self.app_instance = app_instance # Store reference to main app
        self.title("Batch Inject Files")
        self.geometry("650x450")
        self.resizable(True, True)
        # Make dialog modal
        self.grab_set()
        self.transient(app_instance.root)

        # Configure styles for dialog widgets
        self.style = ttk.Style(self) # Use local style instance if needed
        # Styles are inherited from main app via setup_styles, but can be overridden

        # Main Frame
        self.main_frame = ttk.Frame(self, padding="10", style="Dialog.TFrame")
        self.main_frame.pack(expand=True, fill=tk.BOTH)
        # Configure grid weights
        self.main_frame.grid_rowconfigure(3, weight=1) # Log area expands
        self.main_frame.grid_columnconfigure(1, weight=1) # Entry fields expand

        # Path variables
        self.paths = {
            "original": tk.StringVar(),
            "modified": tk.StringVar(),
            "output": tk.StringVar()
        }

        # Path Input Fields
        labels = {
            "original": "Original ARC Directory:",
            "modified": "Modified Files Root Dir:",
            "output": "Output ARC Directory:"
        }
        self.input_widgets: Dict[str, Tuple[ttk.Entry, ttk.Button]] = {} # Store widgets for state toggling
        row_num = 0
        for key, label_text in labels.items():
            ttk.Label(self.main_frame, text=label_text, style="Dialog.TLabel").grid(row=row_num, column=0, sticky=tk.W, pady=3, padx=2)
            entry = ttk.Entry(self.main_frame, textvariable=self.paths[key], width=60, style="Dialog.TEntry")
            entry.grid(row=row_num, column=1, sticky=(tk.W, tk.E), padx=5, pady=3)
            button = ttk.Button(self.main_frame, text="Browse...", style="Dialog.TButton",
                                command=lambda k=key: self.browse_dir(k))
            button.grid(row=row_num, column=2, padx=2, pady=3)
            self.input_widgets[key] = (entry, button) # Store entry and button
            row_num += 1

        # Log Area
        log_frame = ttk.LabelFrame(self.main_frame, text="Batch Log", padding="5", style="Dialog.TLabelframe")
        log_frame.grid(row=row_num, column=0, columnspan=3, sticky="nsew", pady=(10, 5))
        log_frame.grid_rowconfigure(0, weight=1)
        log_frame.grid_columnconfigure(0, weight=1)

        log_font = ("Consolas", 9) if os.name == 'nt' else ("Monospace", 10)
        self.log_text = tk.Text(log_frame, height=15, width=70, wrap=tk.WORD, state=tk.DISABLED,
                                font=log_font, bg=WIDGET_BG, fg=TEXT_COLOR, relief=tk.FLAT, bd=0)
        log_scroll = ttk.Scrollbar(log_frame, orient=tk.VERTICAL, command=self.log_text.yview, style="Dialog.Vertical.TScrollbar")
        self.log_text['yscrollcommand'] = log_scroll.set
        self.log_text.grid(row=0, column=0, sticky="nsew")
        log_scroll.grid(row=0, column=1, sticky="ns")

        # Bottom Buttons
        button_frame = ttk.Frame(self.main_frame, style="Dialog.TFrame")
        button_frame.grid(row=row_num + 1, column=0, columnspan=3, pady=(5, 0), sticky=tk.E)

        self.start_button = ttk.Button(button_frame, text="Start Batch Inject", command=self.start_injection, style="Dialog.TButton")
        self.start_button.pack(side=tk.RIGHT, padx=5)
        self.close_button = ttk.Button(button_frame, text="Close", command=self.close_dialog, style="Dialog.TButton")
        self.close_button.pack(side=tk.RIGHT, padx=5)

        # State
        self.is_running = False
        self.protocol("WM_DELETE_WINDOW", self.close_dialog) # Handle close button

    def browse_dir(self, path_key: str):
        """Opens a directory browser for the specified path type."""
        current_path = self.paths[path_key].get()
        title_map = {
            "original": "Select Directory Containing Original ARC Files",
            "modified": "Select Root Directory of Modified Files",
            "output": "Select Directory for Output ARCs"
        }
        directory = filedialog.askdirectory(title=title_map.get(path_key, "Select Directory"),
                                           initialdir=current_path if current_path else None)
        if directory:
            self.paths[path_key].set(directory)

    def log_message(self, message: str, level: str = "INFO"):
        """Logs messages to the dialog's Text widget."""
        # Simplified log format for dialog
        timestamp = time.strftime("%H:%M:%S")
        log_entry = f"[{timestamp} {level}] {message}\n"
        try:
            self.log_text.config(state=tk.NORMAL)
            self.log_text.insert(tk.END, log_entry)
            self.log_text.see(tk.END)
            self.log_text.config(state=tk.DISABLED)
            self.update_idletasks() # Ensure log updates
        except tk.TclError as e:
             print(f"Error logging to batch dialog: {e}") # Fallback

    def set_ui_state(self, enabled: bool):
        """Enables or disables input widgets during processing."""
        state = tk.NORMAL if enabled else tk.DISABLED
        self.is_running = not enabled

        # Toggle buttons and entry fields using stored references
        self.start_button.config(state=state)
        for key in self.input_widgets:
             entry, button = self.input_widgets[key]
             try:
                 entry.config(state=state)
                 button.config(state=state)
             except tk.TclError:
                 self.log_message(f"Warning: Could not set state for widgets of '{key}'.", "WARN")

        # Close button should always be enabled (unless you want to force user to wait)
        self.close_button.config(state=tk.NORMAL)

    def validate_paths(self) -> bool:
        """Checks if selected paths are valid and suitable."""
        orig_dir = self.paths["original"].get()
        mod_dir = self.paths["modified"].get()
        out_dir = self.paths["output"].get()

        if not all([orig_dir, mod_dir, out_dir]):
            messagebox.showerror("Input Error", "Please select all three directories.", parent=self)
            return False

        orig_path = Path(orig_dir)
        mod_path = Path(mod_dir)
        out_path = Path(out_dir)

        if not orig_path.is_dir():
            messagebox.showerror("Input Error", f"Original ARC directory not found:\n{orig_dir}", parent=self)
            return False
        if not mod_path.is_dir():
            messagebox.showerror("Input Error", f"Modified files directory not found:\n{mod_dir}", parent=self)
            return False

        # Check if output needs creation
        if not out_path.exists():
            if messagebox.askyesno("Create Directory?", f"Output directory does not exist:\n{out_dir}\n\nCreate it?", parent=self):
                try:
                    out_path.mkdir(parents=True, exist_ok=True)
                except Exception as e:
                    messagebox.showerror("Error", f"Failed to create output directory:\n{e}", parent=self)
                    return False
            else:
                return False # User chose not to create
        elif not out_path.is_dir():
             messagebox.showerror("Input Error", f"Output path exists but is not a directory:\n{out_dir}", parent=self)
             return False


        # Prevent output being same as input
        try: # Use resolve to handle potential symlinks etc.
            if orig_path.resolve() == out_path.resolve():
                messagebox.showerror("Input Error", "Output directory cannot be the same as the Original ARC directory.", parent=self)
                return False
            if mod_path.resolve() == out_path.resolve():
                messagebox.showerror("Input Error", "Output directory cannot be the same as the Modified files directory.", parent=self)
                return False
        except OSError as e:
             messagebox.showwarning("Path Warning", f"Could not fully resolve paths for comparison: {e}", parent=self)
             # Allow continuing but warn user

        return True

    def start_injection(self):
        """Starts the batch injection process in a separate thread."""
        if self.is_running:
            self.log_message("Injection process is already running.", "WARN")
            return
        if not self.validate_paths():
            return

        orig_dir = self.paths["original"].get()
        mod_dir = self.paths["modified"].get()
        out_dir = self.paths["output"].get()

        # Clear log and disable UI
        self.log_text.config(state=tk.NORMAL)
        self.log_text.delete('1.0', tk.END)
        self.log_text.config(state=tk.DISABLED)
        self.log_message("Starting Batch Injection...", "INFO")
        self.log_message(f"  Original ARCs: {orig_dir}", "DEBUG")
        self.log_message(f"  Modified Files: {mod_dir}", "DEBUG")
        self.log_message(f"  Output ARCs: {out_dir}", "DEBUG")
        self.log_message("-" * 20, "INFO")
        self.set_ui_state(False) # Disable inputs

        # Run the actual logic in a separate thread to keep GUI responsive
        thread = threading.Thread(target=self._run_injection_thread, args=(orig_dir, mod_dir, out_dir), daemon=True)
        thread.start()

    def _run_injection_thread(self, orig_dir: str, mod_dir: str, out_dir: str):
        """Worker thread function for batch injection."""
        error_info = None # Variable to store potential exception info
        try:
            # Call the main app's batch logic function, passing the dialog's logger
            self.app_instance.run_batch_injection(orig_dir, mod_dir, out_dir, self.log_message)

            # Log completion in dialog
            self.log_message("-" * 20, "INFO")
            self.log_message("Batch Injection Finished.", "INFO")
            # Show completion popup using lambda and after_idle
            self.app_instance.root.after_idle(
                lambda: messagebox.showinfo("Finished", "Batch injection process complete.", parent=self)
            )

        except Exception as e:
            error_info = e # Store exception info
            # Log error in dialog
            self.log_message(f"\n--- BATCH FAILED ---", "FATAL")
            self.log_message(f"Error during batch injection: {e}", "FATAL")
            self.log_message(traceback.format_exc(), "DEBUG")
            # Show error popup using lambda and after_idle
            # Capture exception info for the lambda
            error_message = f"An error occurred during batch injection:\n{error_info}\n\nCheck the log for details."
            self.app_instance.root.after_idle(
                lambda msg=error_message: messagebox.showerror("Batch Failed", msg, parent=self)
            )
        finally:
            # Re-enable UI using after_idle
            self.app_instance.root.after_idle(self.set_ui_state, True)


    def close_dialog(self):
         """Closes the batch injection dialog."""
         if self.is_running:
             if not messagebox.askyesno("Process Running", "Batch process is still running. Close anyway?", parent=self):
                 return # Cancel closing
         self.grab_release()
         self.destroy()

# --- Batch Extraction Dialog Class ---
class BatchExtractDialog(tk.Toplevel):
    def __init__(self, app_instance: MtArcToolApp):
        super().__init__(app_instance.root)
        self.app_instance = app_instance # Store reference to main app
        self.title("Batch Extract ARCs")
        self.geometry("650x450")
        self.resizable(True, True)
        self.grab_set()
        self.transient(app_instance.root)

        self.style = ttk.Style(self)
        self.main_frame = ttk.Frame(self, padding="10", style="Dialog.TFrame")
        self.main_frame.pack(expand=True, fill=tk.BOTH)
        self.main_frame.grid_rowconfigure(2, weight=1) # Log area expands
        self.main_frame.grid_columnconfigure(1, weight=1) # Entry fields expand

        self.paths = {"input": tk.StringVar(), "output": tk.StringVar()}
        labels = {
            "input": "Input ARC Directory (Recursive):",
            "output": "Output Base Directory:"
        }
        self.input_widgets: Dict[str, Tuple[ttk.Entry, ttk.Button]] = {} # Store widgets
        row_num = 0
        for key, label_text in labels.items():
            ttk.Label(self.main_frame, text=label_text, style="Dialog.TLabel").grid(row=row_num, column=0, sticky=tk.W, pady=3, padx=2)
            entry = ttk.Entry(self.main_frame, textvariable=self.paths[key], width=60, style="Dialog.TEntry")
            entry.grid(row=row_num, column=1, sticky=(tk.W, tk.E), padx=5, pady=3)
            button = ttk.Button(self.main_frame, text="Browse...", style="Dialog.TButton", command=lambda k=key: self.browse_dir(k))
            button.grid(row=row_num, column=2, padx=2, pady=3)
            self.input_widgets[key] = (entry, button) # Store
            row_num += 1

        log_frame = ttk.LabelFrame(self.main_frame, text="Batch Log", padding="5", style="Dialog.TLabelframe")
        log_frame.grid(row=row_num, column=0, columnspan=3, sticky="nsew", pady=(10, 5))
        log_frame.grid_rowconfigure(0, weight=1)
        log_frame.grid_columnconfigure(0, weight=1)

        log_font = ("Consolas", 9) if os.name == 'nt' else ("Monospace", 10)
        self.log_text = tk.Text(log_frame, height=15, width=70, wrap=tk.WORD, state=tk.DISABLED,
                                font=log_font, bg=WIDGET_BG, fg=TEXT_COLOR, relief=tk.FLAT, bd=0)
        log_scroll = ttk.Scrollbar(log_frame, orient=tk.VERTICAL, command=self.log_text.yview, style="Dialog.Vertical.TScrollbar")
        self.log_text['yscrollcommand'] = log_scroll.set
        self.log_text.grid(row=0, column=0, sticky="nsew")
        log_scroll.grid(row=0, column=1, sticky="ns")

        button_frame = ttk.Frame(self.main_frame, style="Dialog.TFrame")
        button_frame.grid(row=row_num + 1, column=0, columnspan=3, pady=(5, 0), sticky=tk.E)

        self.start_button = ttk.Button(button_frame, text="Start Batch Extract", command=self.start_extraction, style="Dialog.TButton")
        self.start_button.pack(side=tk.RIGHT, padx=5)
        self.close_button = ttk.Button(button_frame, text="Close", command=self.close_dialog, style="Dialog.TButton")
        self.close_button.pack(side=tk.RIGHT, padx=5)

        self.is_running = False
        self.protocol("WM_DELETE_WINDOW", self.close_dialog)

    def browse_dir(self, path_key: str):
        """Opens a directory browser for the specified path type."""
        current_path = self.paths[path_key].get()
        title_map = {
            "input": "Select Root Directory Containing ARC Files (Recursive Scan)",
            "output": "Select Base Directory for Extracted Files"
        }
        directory = filedialog.askdirectory(title=title_map.get(path_key, "Select Directory"),
                                           initialdir=current_path if current_path else None)
        if directory:
            self.paths[path_key].set(directory)

    def log_message(self, message: str, level: str = "INFO"):
        """Logs messages to the dialog's Text widget."""
        timestamp = time.strftime("%H:%M:%S")
        log_entry = f"[{timestamp} {level}] {message}\n"
        try:
            self.log_text.config(state=tk.NORMAL)
            self.log_text.insert(tk.END, log_entry)
            self.log_text.see(tk.END)
            self.log_text.config(state=tk.DISABLED)
            self.update_idletasks()
        except tk.TclError as e:
            print(f"Error logging to batch dialog: {e}")

    def set_ui_state(self, enabled: bool):
        """Enables or disables input widgets during processing."""
        state = tk.NORMAL if enabled else tk.DISABLED
        self.is_running = not enabled

        self.start_button.config(state=state)
        for key in self.input_widgets:
             entry, button = self.input_widgets[key]
             try:
                 entry.config(state=state)
                 button.config(state=state)
             except tk.TclError:
                 self.log_message(f"Warning: Could not set state for widgets of '{key}'.", "WARN")

        self.close_button.config(state=tk.NORMAL) # Close always enabled

    def validate_paths(self) -> bool:
        """Checks if selected paths are valid."""
        in_dir = self.paths["input"].get()
        out_dir = self.paths["output"].get()

        if not all([in_dir, out_dir]):
            messagebox.showerror("Input Error", "Please select both input and output directories.", parent=self)
            return False

        in_path = Path(in_dir)
        out_path = Path(out_dir)

        if not in_path.is_dir():
            messagebox.showerror("Input Error", f"Input ARC directory not found:\n{in_dir}", parent=self)
            return False

        if not out_path.exists():
            if messagebox.askyesno("Create Directory?", f"Output directory does not exist:\n{out_dir}\n\nCreate it?", parent=self):
                try:
                    out_path.mkdir(parents=True, exist_ok=True)
                except Exception as e:
                    messagebox.showerror("Error", f"Failed to create output directory:\n{e}", parent=self)
                    return False
            else:
                return False
        elif not out_path.is_dir():
             messagebox.showerror("Input Error", f"Output path exists but is not a directory:\n{out_dir}", parent=self)
             return False

        return True

    def start_extraction(self):
        """Starts the batch extraction process in a separate thread."""
        if self.is_running:
            self.log_message("Extraction process is already running.", "WARN")
            return
        if not self.validate_paths():
            return

        in_dir = self.paths["input"].get()
        out_dir = self.paths["output"].get()

        self.log_text.config(state=tk.NORMAL)
        self.log_text.delete('1.0', tk.END)
        self.log_text.config(state=tk.DISABLED)
        self.log_message("Starting Batch Extraction...", "INFO")
        self.log_message(f"  Input ARCs (Recursive): {in_dir}", "DEBUG")
        self.log_message(f"  Output Base: {out_dir}", "DEBUG")
        self.log_message("-" * 20, "INFO")
        self.set_ui_state(False) # Disable inputs

        # Run extraction logic in a thread
        thread = threading.Thread(target=self._run_extraction_thread, args=(in_dir, out_dir), daemon=True)
        thread.start()

    def _run_extraction_thread(self, in_dir: str, out_dir: str):
        """Worker thread function for batch extraction."""
        error_info = None # Variable to store potential exception info
        try:
            # Call the main app's batch logic function
            self.app_instance.run_batch_extraction(in_dir, out_dir, self.log_message)

            self.log_message("-" * 20, "INFO")
            self.log_message("Batch Extraction Finished.", "INFO")
            # Use lambda to call showinfo with parent argument later via app_instance.root
            self.app_instance.root.after_idle(
                lambda: messagebox.showinfo("Finished", "Batch extraction process complete.", parent=self)
            )

        except Exception as e:
            error_info = e # Store exception info
            self.log_message(f"\n--- BATCH FAILED ---", "FATAL")
            self.log_message(f"Error during batch extraction: {e}", "FATAL")
            self.log_message(traceback.format_exc(), "DEBUG")
            # Use lambda to call showerror with parent argument later via app_instance.root
            # Capture exception info for the lambda
            error_message = f"An error occurred during batch extraction:\n{error_info}\n\nCheck the log for details."
            self.app_instance.root.after_idle(
                lambda msg=error_message: messagebox.showerror("Batch Failed", msg, parent=self)
            )
        finally:
            # Re-enable UI via main thread using app_instance.root
            self.app_instance.root.after_idle(self.set_ui_state, True)

    def close_dialog(self):
        """Closes the batch extraction dialog."""
        if self.is_running:
             if not messagebox.askyesno("Process Running", "Batch process is still running. Close anyway?", parent=self):
                 return
        self.grab_release()
        self.destroy()


# --- Main Execution ---
if __name__ == "__main__":
    # Check for crcmod before initializing Tkinter if possible
    if not _crcmod_available:
         root_check = tk.Tk()
         root_check.withdraw() # Hide the dummy window
         if not messagebox.askyesno("Missing Dependency",
                                    "Python library 'crcmod' is required for full functionality (extension hashing).\n\n"
                                    "Install using:\npython -m pip install crcmod\n\n"
                                    "Continue anyway (some features will be limited)?", icon='warning'):
             import sys
             sys.exit(1)
         root_check.destroy()

    # Create main window and application instance
    root = tk.Tk()
    app = MtArcToolApp(root)
    # Start the Tkinter event loop
    root.mainloop()
