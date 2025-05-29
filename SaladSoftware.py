# Handburger's MT Framework ARC Decryptor/Extractor
# This script is a Python port of the original C# code from IcySon55's Kuriimu and FanTranslatorsInternational's Kuriimu2.
# Kuriimu2 has a GPL-3.0 license, and this script is intended for strictly personal use.
# It is designed to process and extract files from MT Framework ARC archives.
# The script includes various utility functions, a GUI for user interaction, and support for Blowfish encryption/decryption.
VERSION = "1.3.6" # Updated for CLI addition
# Updated 2025-05-25


import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext, simpledialog
import tkinter.font as tkFont
import os
import sys
import struct
import zlib # Required for the final hash function
import io
import threading
import queue
import pathlib # For easier path manipulation and recursive glob
import concurrent.futures # For parallel processing
import traceback # For detailed error info
import time # For timing operations
from collections import namedtuple
from Crypto.Cipher import Blowfish
from datetime import datetime # For timestamps
import shutil # For moving files/folders
import re # For improved filename sanitization
import textwrap # Added for help dialog formatting
import argparse # ADDED: For CLI

# ADDED: For Drag and Drop
try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
except ImportError:
    TkinterDnD = None # Flag that it's not available

# ARCC_SKIP: Custom exception for intentionally skipped ARCC files
class ARCCSkippedError(ValueError): # Inheriting from ValueError is fine
    """Custom exception for when an ARCC file is intentionally skipped."""
    pass

# --- CONSTANTS ---
# --- Color Scheme ---
BG_COLOR='#2b2b2b';TEXT_COLOR='#ffebcd';WIDGET_BG='#3c3f41';INPUT_TEXT_COLOR='#f0f0f0'
BUTTON_BG='#4c4c4c';BUTTON_FG=TEXT_COLOR;BUTTON_ACTIVE_BG='#5c5c5c';BUTTON_PRESSED_BG='#636363'
BUTTON_BORDER='#1e1e1e';HEADER_BG='#4a4a4a';HEADER_TEXT=TEXT_COLOR;HEADER_ACTIVE_BG=WIDGET_BG
HEADER_ACTIVE_TEXT='#ffffff';HIGHLIGHT_BG='#52596b';HIGHLIGHT_TEXT='#00f7ff'
STATUS_ERROR_FG='#ff6b6b';STATUS_WARN_FG='#ffb366';STATUS_SUCCESS_FG='#86e3a0'
STATUS_INFO_FG=TEXT_COLOR;STATUS_DEBUG_FG='#999999';CHECKED_TEXT_FG='#00f7ff'
# --- Font ---
FONT_FAMILY="Ubuntu Mono";FONT_SIZE=13;FONT_SETTINGS=(FONT_FAMILY,FONT_SIZE) # MODIFIED: Font family changed
# --- Platform Enum ---
class Platform: UNKNOWN=0; PC=1; CTR=2; PS3=3; Switch=4
# --- ARC Constants ---
DEFAULT_VERSION=9;DEFAULT_BYTE_ORDER_CHAR='<';DEFAULT_PLATFORM=Platform.Switch # Default to Switch for rebuilds IF NO OTHER INFO
# --- Structs ---
def format_struct(e, p): return e + p
FMT_HEADER_COMMON="4sHH"; SIZE_HEADER_COMMON=8 # Magic, Version, EntryCount
FMT_HEADER_PC_EXTRA="I"; SIZE_HEADER_PC_EXTRA=4 # Extra field for some PC versions
FMT_ENTRY="64sIiii"; SIZE_ENTRY=80 # PC/PS3/CTR: Name, ExtHash, CompSize, UncompSize, Offset
FMT_ENTRY_SWITCH="64sIiiii"; SIZE_ENTRY_SWITCH=84 # Switch: Name, ExtHash, CompSize, UncompSize, Unknown1, Offset
# Kuriimu2 MtArc uses MtEntryExtendedName (128s) for some PC LE versions. This script currently uses 64s.
FMT_ENTRY_EXTENDED_NAME = "128sIiii"; SIZE_ENTRY_EXTENDED_NAME = 144 # Placeholder if 128-byte names are implemented

FMT_HFS_HEADER="4shhiI"; SIZE_HFS_HEADER=16; FMT_HFS_FOOTER="QQ"; SIZE_HFS_FOOTER=16
# --- Zlib/Align/Magic ---
ZLIB_COMPRESSION_LEVEL = 9; ALIGNMENT_SWITCH = 0x8000; ALIGNMENT_PC_DEFAULT = 0x100
ALIGNMENT_PC_V7_V10_LE = 0x8000 # For PC Little Endian Version 7 and 0x10 (16)
MAGIC_ARC_LE=b'ARC\x00'; # ARCC_REMOVED: MAGIC_ARCC_LE=b'ARCC';
MAGIC_ARC_BE=b'\x00CRA'; MAGIC_HFS_LE=b'HFS\x00'; MAGIC_HFS_BE=b'\x00SFH'
# --- Status Levels ---
STATUS_INFO="info"; STATUS_SUCCESS="success"; STATUS_WARN="warn"; STATUS_ERROR="error"; STATUS_DEBUG="debug"
# --- Parallel Processing ---
MAX_WORKERS = os.cpu_count() * 2 if os.cpu_count() else 4
MAX_WORKERS = max(4, MAX_WORKERS if MAX_WORKERS is not None else 4)
MAX_WORKERS = min(MAX_WORKERS, 32)
# --- Treeview Checkbox Characters ---
CHECK_UNCHECKED = "☐" # U+2610 BALLOT BOX
CHECK_CHECKED = "☑"   # U+2611 BALLOT BOX WITH CHECK


# --- Extension Map (Will be populated from file) ---
EXTENSION_MAP = {}
REV_EXTENSION_MAP = {}
EXTENSION_MAP_FILE = "unique_extensions.txt"
GAME_SPECIFIC_HASH_FILE = "extension_index_line.txt"

# Sourcing Files

def resource_path(relative_path):
    """ Get absolute path to resource, works for dev and for PyInstaller """
    try:
        # PyInstaller creates a temp folder and stores path in _MEIPASS
        base_path = sys._MEIPASS
    except Exception:
        # sys._MEIPASS is not defined, so we are not running from a PyInstaller bundle
        base_path = os.path.abspath(".") # Or pathlib.Path(__file__).parent

    return os.path.join(base_path, relative_path)
    # Or for pathlib: return pathlib.Path(base_path) / relative_path

# --- ARC UTILITIES & MTArc Class ---

# --- Data Structures ---
HFSHeader = namedtuple("HFSHeader", ["magic", "version", "type", "file_size", "padding"])
HFSFooter = namedtuple("HFSFooter", ["hash1", "hash2"])
ARCHeader = namedtuple("ARCHeader", ["magic", "version", "entry_count"])

def create_file_info():
    """Creates a dictionary to hold file metadata and data."""
    return {
        "filename_base":b'',"ext_hash":0,"compressed_size":0,"uncompressed_size_raw":0,
        "offset":0,"unknown1":None,"platform":Platform.UNKNOWN,"data":None,"full_filename":"",
        "is_compressed":False,"calculated_uncompressed_size":None, "arc_byte_order_char": DEFAULT_BYTE_ORDER_CHAR,
    }

def load_extension_map(primary_filepath: str, game_specific_filepath: str | None = None):
    """
    Loads the extension map from a primary text file and optionally a game-specific hash file.
    Primary file format:
    1. An 8-char hex hash (e.g., 241F5DEB)
    2. A plaintext extension string (e.g., tex)
    3. An assignment: 8-char hex hash = plaintext_ext (e.g., ABCDEF01 = custom)
    Game-specific file format (if provided):
    1. hash_hex_string, .extension_string (e.g., 79c47b59, .mca)
       Mappings from game-specific file will override primary file if hash conflicts.
    """
    global EXTENSION_MAP, REV_EXTENSION_MAP
    EXTENSION_MAP = {}
    REV_EXTENSION_MAP = {}

    # --- Load Primary Extension File ---
    if not os.path.isfile(primary_filepath):
        # This function might be called before GUI/CLI choice, so use print for now.
        print(f"Warning: Primary extension map file not found at '{primary_filepath}'. Using empty map initially.", file=sys.stderr)
    else:
        potential_hashes_from_primary_file = set()
        potential_extension_strings_primary = []
        direct_assignments_primary = {}

        try:
            with open(primary_filepath, 'r', encoding='utf-8') as f:
                for line_num, line in enumerate(f, 1):
                    line = line.strip()
                    if not line or line.startswith('#') or line.startswith('//'):
                        continue

                    if '=' in line: # HASH = ext format
                        parts = line.split('=', 1)
                        hash_str_part = parts[0].strip()
                        ext_str_part = parts[1].strip()
                        if len(hash_str_part) == 8 and all(c in "0123456789abcdefABCDEF" for c in hash_str_part) and \
                           ext_str_part and all(c.isalnum() or c == '_' for c in ext_str_part):
                            try:
                                hash_val = int(hash_str_part, 16)
                                ext_with_dot = "." + ext_str_part
                                direct_assignments_primary[hash_val] = ext_with_dot
                                REV_EXTENSION_MAP[ext_with_dot.lower()] = hash_val
                                continue
                            except ValueError:
                                print(f"Warning: Line {line_num} in {primary_filepath}: Invalid HASH in assignment '{line}'.", file=sys.stderr)
                                continue
                        else:
                            print(f"Warning: Line {line_num} in {primary_filepath}: Malformed HASH = ext assignment '{line}'.", file=sys.stderr)
                            continue

                    is_potential_hash = False
                    if len(line) == 8:
                        try:
                            # Check if this hash is already directly assigned, if so, ignore the raw entry
                            if int(line, 16) not in direct_assignments_primary:
                                hash_val = int(line, 16)
                                potential_hashes_from_primary_file.add(hash_val)
                                is_potential_hash = True
                        except ValueError: pass # Not a valid hex string

                    if not is_potential_hash:
                        # Treat as plaintext extension string
                        if line and all(c.isalnum() or c == '_' for c in line):
                             potential_extension_strings_primary.append(line)
                        else:
                            print(f"Warning: Line {line_num} in {primary_filepath}: Skipping unusual string '{line}'.", file=sys.stderr)

            for ext_str_no_dot in potential_extension_strings_primary:
                actual_ext_with_dot = "." + ext_str_no_dot
                hash_for_ext = calculate_arc_hash(ext_str_no_dot) # Use the final hash function
                if hash_for_ext not in EXTENSION_MAP and hash_for_ext not in direct_assignments_primary:
                    EXTENSION_MAP[hash_for_ext] = actual_ext_with_dot
                    # Add to REV_EXTENSION_MAP only if the extension isn't already mapped (direct assignments have precedence)
                    if actual_ext_with_dot.lower() not in REV_EXTENSION_MAP:
                        REV_EXTENSION_MAP[actual_ext_with_dot.lower()] = hash_for_ext
                if hash_for_ext in potential_hashes_from_primary_file:
                    potential_hashes_from_primary_file.remove(hash_for_ext)

            for hash_val, ext_str_with_dot in direct_assignments_primary.items():
                EXTENSION_MAP[hash_val] = ext_str_with_dot # Direct assignments override calculated ones

            num_mapped_primary = len(EXTENSION_MAP)
            num_unexplained_primary = len(potential_hashes_from_primary_file)
            print(f"Loaded {num_mapped_primary} mappings from primary map '{os.path.basename(primary_filepath)}'. "
                  f"({num_unexplained_primary} unexplained raw hashes remain from primary).")

        except Exception as e:
            print(f"Error loading primary extension map from {primary_filepath}: {e}", file=sys.stderr)
            traceback.print_exc()
            #EXTENSION_MAP, REV_EXTENSION_MAP remain empty or partially filled from previous attempts

    # --- Load Game-Specific Hash File (if provided and exists) ---
    if game_specific_filepath and os.path.isfile(game_specific_filepath):
        game_specific_loaded_count = 0
        try:
            with open(game_specific_filepath, 'r', encoding='utf-8') as f_game:
                for line_num, line in enumerate(f_game, 1):
                    line = line.strip()
                    if not line or line.startswith('#') or line.startswith('//'):
                        continue

                    # Expected format: hash_hex_string, .extension_string
                    parts = line.split(',', 1)
                    if len(parts) == 2:
                        hash_str_part = parts[0].strip()
                        ext_str_part = parts[1].strip() # Should include the leading dot

                        if len(hash_str_part) > 0 and all(c in "0123456789abcdefABCDEF" for c in hash_str_part) and \
                           ext_str_part.startswith('.') and len(ext_str_part) > 1 and \
                           all(c.isalnum() or c == '_' for c in ext_str_part[1:]): # Validate extension part
                            try:
                                hash_val = int(hash_str_part, 16)
                                # Game-specific mappings override primary ones
                                EXTENSION_MAP[hash_val] = ext_str_part
                                REV_EXTENSION_MAP[ext_str_part.lower()] = hash_val
                                game_specific_loaded_count += 1
                            except ValueError:
                                print(f"Warning: Line {line_num} in {game_specific_filepath}: Invalid HASH in game-specific entry '{line}'.", file=sys.stderr)
                        else:
                            print(f"Warning: Line {line_num} in {game_specific_filepath}: Malformed game-specific entry '{line}'. Expected 'hash, .ext'.", file=sys.stderr)
                    else:
                        print(f"Warning: Line {line_num} in {game_specific_filepath}: Skipping malformed line '{line}'. Expected 'hash, .ext'.", file=sys.stderr)
            print(f"Loaded {game_specific_loaded_count} mappings from game-specific file '{os.path.basename(game_specific_filepath)}'. These override primary mappings on conflict.")
        except Exception as e:
            print(f"Error loading game-specific extension map from {game_specific_filepath}: {e}", file=sys.stderr)
            traceback.print_exc()
    elif game_specific_filepath:
        print(f"Info: Game-specific extension map file not found at '{game_specific_filepath}'. Skipping.", file=sys.stderr)

    # Final summary
    final_total_mapped = len(EXTENSION_MAP)
    print(f"Total unique extension mappings loaded: {final_total_mapped}.")


def get_full_filename(file_info):
    """Constructs the full filename (preserving separators) from base name and extension hash, using loaded map."""
    try:
        name = "decode_error"
        filename_bytes = file_info.get("filename_base", b'')
        if not filename_bytes: name = ""
        else:
            # Try decoding in a common order
            try:
                 # Null-terminated string in filename_base
                 decoded_name = filename_bytes.split(b'\x00',1)[0].decode('ascii')
                 name = decoded_name
            except UnicodeDecodeError:
                 try:
                     decoded_name = filename_bytes.split(b'\x00',1)[0].decode('shift-jis') # Common for Japanese games
                     name = decoded_name
                 except (UnicodeDecodeError, LookupError): # LookupError for unknown encoding
                     try:
                         decoded_name = filename_bytes.split(b'\x00',1)[0].decode('utf-8', errors='replace') # Fallback to UTF-8
                         name = decoded_name
                     except Exception: # Should not happen with errors='replace'
                        name = "decode_error_utf8_fallback"
    except Exception: # Catch errors from .get or other unexpected issues
        name = "decode_error_outer"

    hash_val = file_info.get("ext_hash", 0)
    ext = EXTENSION_MAP.get(hash_val, f".{hash_val:08X}") # Use hex hash if not in map
    return name + ext # Name can contain path separators like "path/to/file" or "path\to\file"

def get_calculated_uncompressed_size(file_info):
    """Calculates the effective uncompressed size based on platform logic. Returns None if raw size is invalid."""
    p = file_info.get("platform", Platform.UNKNOWN)
    u = file_info.get("uncompressed_size_raw")
    arc_bo_char = file_info.get("arc_byte_order_char", DEFAULT_BYTE_ORDER_CHAR) # Get BO char from file_info

    if u is None: return None
    try: u = int(u)
    except (ValueError, TypeError):
         print(f"Warning: Raw uncompressed size '{u}' is not a valid integer for {file_info.get('full_filename','?')}. Cannot calculate.", file=sys.stderr)
         return None
    if u < 0: # Negative raw size is problematic
         print(f"Warning: Negative raw uncompressed size ({u}) for {file_info.get('full_filename','?')}. Cannot calculate meaningful size.", file=sys.stderr)
         return None

    # Kuriimu2 logic:
    # Ref: Kuriimu.Core.Archiving.MtFramework.MtEntry.DecompressedSize (get and set)
    if p == Platform.CTR or (p == Platform.PC and arc_bo_char == '<'): # Little Endian PC or CTR
        return u & 0x00FFFFFF
    elif p == Platform.PS3: # Big Endian (PS3)
        return u >> 3
    elif p == Platform.Switch: # Switch uses the raw value directly
        return u
    # Fallback for other PC (typically Big Endian if not covered above, or unknown platforms)
    # Kuriimu1 logic for PC was u >> 3
    else:
        # print(f"Debug: Platform {p}, BO '{arc_bo_char}' for '{file_info.get('full_filename','?')}' using fallback uncompressed size rule (raw >> 3).", file=sys.stderr)
        return u >> 3


def calculate_arc_hash(s: str) -> int:
    """
    Calculates the MT Framework ARC extension hash.
    This version matches Kuriimu1's ArcShared.GetHash, which produces standard CRC32 values
    consistent with keys found in Kuriimu2's _extensionMap.
    (Initial 0xFFFFFFFF, Reflected Poly 0xEDB88320, processes LSB of byte first, final value as is)
    """
    if not isinstance(s, str):
        return 0
    if not s: # Empty string hash is 0 in Kuriimu
        return 0

    byte_values = []
    for char_in_s in s: # Match (byte)char conversion from C#
        byte_values.append(ord(char_in_s) & 0xFF)

    h = 0xFFFFFFFF
    poly = 0xEDB88320 # Reflected polynomial for CRC32

    for byte_val in byte_values:
        h ^= byte_val # XOR byte into hash
        for _ in range(8): # LSB first processing
            if (h & 1): # If LSB is 1
                h = (h >> 1) ^ poly
            else:
                h >>= 1
    return h & 0xFFFFFFFF # Ensure it's an unsigned 32-bit int

# --- Alignment Helper ---
def pad_stream(stream, alignment):
    """Pads a stream with null bytes until it meets the alignment."""
    if not hasattr(stream, 'write') or not hasattr(stream, 'tell'):
         raise TypeError("Input to pad_stream must be a stream-like object.")
    if not isinstance(alignment, int) or alignment <= 0:
         raise ValueError("Alignment must be a positive integer.")

    current_pos=stream.tell();remainder=current_pos%alignment
    if remainder!=0:
        pad_size = alignment-remainder
        try: stream.write(b'\x00'*pad_size)
        except Exception as e: raise IOError(f"Failed to write padding to stream: {e}") from e


def compress_kontract_zlib(data, level=ZLIB_COMPRESSION_LEVEL):
    """Compresses data using standard Deflate with Kontract's 0x78 0xDA header and Adler32 footer."""
    if not isinstance(data, bytes):
         raise TypeError("Input to compress_kontract_zlib must be bytes.")
    if not data: return b''

    try:
        actual_level = max(-1, min(9, level))
        # wbits = -zlib.MAX_WBITS produces raw deflate stream (no zlib header/trailer)
        compressed_core=zlib.compress(data,level=actual_level,wbits=-zlib.MAX_WBITS)
        checksum=zlib.adler32(data)&0xFFFFFFFF # Adler32 of original uncompressed data
        header=b'\x78\xDA'
        footer=checksum.to_bytes(4,byteorder='big');
        return header+compressed_core+footer
    except Exception as e:
         raise RuntimeError(f"Kontract Zlib compression failed: {e}") from e


def decompress_kontract_zlib(compressed_data):
    """Decompresses data assuming Kontract's Zlib header (0x78) and trailer (4 bytes) format."""
    if not isinstance(compressed_data, bytes):
         raise TypeError("Input to decompress_kontract_zlib must be bytes.")
    if len(compressed_data) < 6:
         return compressed_data

    core_data=compressed_data[2:-4]
    if not core_data: return b''

    try:
        return zlib.decompress(core_data,wbits=-zlib.MAX_WBITS)
    except zlib.error as e_kontract:
        try:
            return zlib.decompress(compressed_data)
        except zlib.error as e_standard:
             raise RuntimeError(f"Kontract Zlib decompression failed ({e_kontract}). Standard Zlib also failed ({e_standard}). Data may be corrupt or not zlib.") from e_standard
    except Exception as e:
         raise RuntimeError(f"Unexpected decompression error: {e}") from e


# --- MT Framework Blowfish Crypto Wrapper (using pycryptodome) ---
class MTBlowfishCrypto:
    """Wraps pycryptodome Blowfish to mimic Kontract.Encryption.BlowFish with MTMethod."""
    def __init__(self, key: bytes):
        if not isinstance(key, bytes) or len(key) < 1 or len(key) > 56:
             raise ValueError(f"Invalid Blowfish key ({type(key).__name__}, {len(key) if isinstance(key, (bytes, bytearray)) else 'N/A'} bytes). Must be bytes 1-56 bytes.")
        self.key = key
        self.mt_method = True

    def _swap_block_endian(self, block_64bit: bytes) -> bytes:
        """Swaps the two 4-byte halves of an 8-byte block (LLLLRRRR -> RRRRLLLL)."""
        if not isinstance(block_64bit, bytes) or len(block_64bit) != 8:
            raise ValueError(f"Attempted to swap endian on non-8-byte block (type {type(block_64bit).__name__}, size {len(block_64bit) if isinstance(block_64bit, (bytes, bytearray)) else 'N/A'}).")
        left = block_64bit[0:4]
        right = block_64bit[4:8]
        return right + left

    def encrypt_ecb(self, data: bytes) -> bytes:
        """Encrypts data in ECB mode, applying MTMethod byte swapping and null padding."""
        if not isinstance(data, bytes):
             raise TypeError("Input to encrypt_ecb must be bytes.")
        if not data: return b''

        block_size = Blowfish.block_size
        pad_len = (block_size - (len(data) % block_size)) % block_size
        padded_data = data + (b'\x00' * pad_len)

        if len(padded_data) % block_size != 0:
             raise RuntimeError("Internal error: Padded data length is not a multiple of Blowfish block size after padding.")

        try:
            cipher = Blowfish.new(self.key, Blowfish.MODE_ECB)
            encrypted_data = bytearray()
            for i in range(0, len(padded_data), block_size):
                block = padded_data[i:i+block_size]
                if self.mt_method: block = self._swap_block_endian(block)
                encrypted_block = cipher.encrypt(block)
                if self.mt_method: encrypted_block = self._swap_block_endian(encrypted_block)
                encrypted_data.extend(encrypted_block)
            return bytes(encrypted_data)
        except Exception as e:
            raise RuntimeError(f"Blowfish encryption failed: {e}") from e

    def decrypt_ecb(self, data: bytes) -> bytes:
        """Decrypts data in ECB mode, applying MTMethod byte swapping. Assumes data is correctly padded if it was encrypted by this class."""
        if not isinstance(data, bytes):
             raise TypeError("Input to decrypt_ecb must be bytes.")
        if not data: return b''

        block_size = Blowfish.block_size
        if len(data) % block_size != 0:
            print(f"Warning: Blowfish input data length ({len(data)}) is not a multiple of block size ({block_size}). Decrypting portion that is a multiple.", file=sys.stderr)
            valid_len = len(data) - (len(data) % block_size)
            if valid_len <= 0:
                 print(f"Warning: Data chunk size ({len(data)} bytes) is less than Blowfish block size ({block_size} bytes). Cannot decrypt, returning raw data.", file=sys.stderr)
                 return data
            data_to_process = data[:valid_len]
            remaining_data = data[valid_len:]
        else:
            data_to_process = data
            remaining_data = b''


        try:
            cipher = Blowfish.new(self.key, Blowfish.MODE_ECB)
            decrypted_data_buffer = bytearray()
            for i in range(0, len(data_to_process), block_size):
                block = data_to_process[i:i+block_size]
                if self.mt_method: block = self._swap_block_endian(block)
                decrypted_block = cipher.decrypt(block)
                if self.mt_method: decrypted_block = self._swap_block_endian(decrypted_block)
                decrypted_data_buffer.extend(decrypted_block)

            if remaining_data:
                decrypted_data_buffer.extend(remaining_data)
            return bytes(decrypted_data_buffer)
        except Exception as e:
             print(f"Warning: Blowfish decryption failed: {e}. Returning raw input data.", file=sys.stderr)
             return data


# --- Main ARC Class ---
class MTArc:
    def __init__(self):
        self.hfs_header = None; self.hfs_footer = None; self.arc_header = None
        self.files = []; # List of file_info dictionaries
        self.byte_order_char = DEFAULT_BYTE_ORDER_CHAR
        self.platform = DEFAULT_PLATFORM
        self.version = DEFAULT_VERSION
        self.header_length = 0
        self.entry_struct_fmt = format_struct(DEFAULT_BYTE_ORDER_CHAR, FMT_ENTRY_SWITCH if DEFAULT_PLATFORM == Platform.Switch else FMT_ENTRY)
        self.entry_struct_size = SIZE_ENTRY_SWITCH if DEFAULT_PLATFORM == Platform.Switch else SIZE_ENTRY
        self.hfs_disk_header_length = 0
        self.is_encrypted = False # ARCC_REMOVED: Will remain False
        self.crypto = None; self._raw_file_path = None; self._decrypted_entries_bytes = None # ARCC_REMOVED: crypto will remain None
        self._data_offset = 0; self._file_size = None
        # ARCC_REMOVED: self.is_arcc = False # ARCC_REMOVED: This flag is no longer primary controller. Will default to False.
        self.entry_has_extended_names = False

    # ARCC_REMOVED: def _derive_mtf_key(self, key1: str, key2: str) -> bytes:
    # ARCC_REMOVED:      """ Derives Blowfish key using the MTFramework method (ported from Kuriimu2 Arcc.cs). """
    # ARCC_REMOVED:      if not isinstance(key1, str) or not isinstance(key2, str): raise TypeError("Keys must be strings.")
    # ARCC_REMOVED:      if len(key1) != len(key2): raise ValueError("Key parts must have equal length.")
    # ARCC_REMOVED:      if not key1: return b''
    # ARCC_REMOVED:      key1_rev = key1[::-1]; key_bytes = bytearray()
    # ARCC_REMOVED:      try:
    # ARCC_REMOVED:          for i in range(len(key1_rev)):
    # ARCC_REMOVED:              val = (ord(key1_rev[i]) ^ ord(key2[i])) | (i << 6)
    # ARCC_REMOVED:              key_bytes.append(val & 0xFF)
    # ARCC_REMOVED:          return bytes(key_bytes)
    # ARCC_REMOVED:      except Exception as e: raise RuntimeError(f"Key derivation failed: {e}") from e

    # ARCC_REMOVED: def _setup_encryption(self, key1=None, key2=None):
    # ARCC_REMOVED:     """Sets up the crypto object if valid keys are provided for ARCC."""
    # ARCC_REMOVED:     k1p = key1 is not None and key1 != ""
    # ARCC_REMOVED:     k2p = key2 is not None and key2 != ""
    # ARCC_REMOVED:     if k1p != k2p:
    # ARCC_REMOVED:         raise ValueError("Both key parts (key1 and key2) are required for encryption, or neither.")
    # ARCC_REMOVED:     if k1p and k2p:
    # ARCC_REMOVED:         try:
    # ARCC_REMOVED:             derived_key = self._derive_mtf_key(key1,key2)
    # ARCC_REMOVED:             if not derived_key:
    # ARCC_REMOVED:                 print("Warning: Derived Blowfish key is empty. Encryption will be ineffective.", file=sys.stderr)
    # ARCC_REMOVED:                 self.is_encrypted = False; self.crypto = None; return
    # ARCC_REMOVED:             self.crypto = MTBlowfishCrypto(derived_key)
    # ARCC_REMOVED:             self.is_encrypted = True
    # ARCC_REMOVED:         except Exception as e:
    # ARCC_REMOVED:             print(f"ERROR: Encryption setup failed during key derivation or Blowfish init: {e}",file=sys.stderr)
    # ARCC_REMOVED:             self.is_encrypted=False; self.crypto=None; raise
    # ARCC_REMOVED:     else:
    # ARCC_REMOVED:         self.is_encrypted=False; self.crypto=None


    def load(self, filepath, key1=None, key2=None, status_queue_or_callback=None): # MODIFIED: status_queue -> status_queue_or_callback
        self.files = []; self._raw_file_path = None; self._decrypted_entries_bytes = None; self._data_offset = 0; self._file_size = None
        self.hfs_header = None; self.hfs_footer = None; self.arc_header = None
        self.hfs_disk_header_length = 0;
        self.entry_has_extended_names = False

        # ADAPTED: Handle both queue and callback for status
        _q_status_actual = lambda msg, level: print(f"NO_CALLBACK [{level.upper()}]: {msg}", file=sys.stderr)
        if status_queue_or_callback:
            if hasattr(status_queue_or_callback, 'put') and callable(status_queue_or_callback.put): # It's a queue
                _q_status_actual = lambda msg, level: status_queue_or_callback.put({'type':'status','msg':msg,'level':level})
            elif callable(status_queue_or_callback): # It's a direct callback
                _q_status_actual = status_queue_or_callback
        _q_status = _q_status_actual

        # ARCC_SKIP: Explicitly check for ARCC magic at the very beginning
        try:
            with open(filepath, 'rb') as f_peek_magic:
                magic_peek = f_peek_magic.read(4)
            if magic_peek == b'ARCC': # Direct check for ARCC magic
                skip_msg = f"Skipped .arcc file: '{os.path.basename(filepath)}'. This tool does not process encrypted ARCC files."
                _q_status(skip_msg, STATUS_INFO)
                raise ARCCSkippedError(skip_msg)
        except ARCCSkippedError:
            raise
        except Exception as e_peek:
            _q_status(f"Notice: Initial magic peek for '{os.path.basename(filepath)}' encountered an issue ({e_peek}), proceeding with standard load attempt.", STATUS_DEBUG)
            pass


        try:
            if not os.path.isfile(filepath): raise FileNotFoundError(f"File not found: {filepath}");
            if not os.access(filepath,os.R_OK): raise PermissionError(f"Read permission denied: {filepath}");
            self._raw_file_path=filepath;
            try: self._file_size=os.path.getsize(filepath)
            except Exception as e: raise IOError(f"Failed to get file size for {filepath}: {e}") from e
            if self._file_size < SIZE_HEADER_COMMON: raise IOError(f"File too small ({self._file_size}b) to be an ARC file.");

            with open(filepath,'rb')as f_raw:
                magic_bytes_for_bo = f_raw.read(4); f_raw.seek(0)
                initial_bo_char = '>' if magic_bytes_for_bo == MAGIC_ARC_BE or magic_bytes_for_bo == MAGIC_HFS_BE else '<'

                temp_hdr_bytes = f_raw.read(SIZE_HEADER_COMMON); f_raw.seek(0)
                if len(temp_hdr_bytes) < SIZE_HEADER_COMMON: raise IOError("File too short for initial header read (second attempt).")
                try:
                    _, temp_version, _ = struct.unpack(format_struct(initial_bo_char, FMT_HEADER_COMMON), temp_hdr_bytes)
                except struct.error as e_unpack_temp:
                    _q_status(f"Warning: Could not unpack temporary header with BO '{initial_bo_char}'. Error: {e_unpack_temp}. Defaulting platform detection.", STATUS_WARN)
                    temp_version = -1

                if temp_version == 9:
                    self.platform = Platform.Switch
                    self.byte_order_char = '<'
                elif magic_bytes_for_bo == MAGIC_ARC_BE:
                    self.platform = Platform.PS3
                    self.byte_order_char = '>'
                else:
                    self.platform = Platform.PC
                    self.byte_order_char = '<'

                _q_status(f"Diag: File '{os.path.basename(filepath)}' - Initial Platform Logic: Magic={magic_bytes_for_bo!r}, TempVersion={temp_version}, InitialBO='{initial_bo_char}' -> Determined Platform={self.platform}, ByteOrder='{self.byte_order_char}'", STATUS_DEBUG)

                actual_magic_read = f_raw.read(4); f_raw.seek(0)
                is_hfs = (actual_magic_read == MAGIC_HFS_LE or actual_magic_read == MAGIC_HFS_BE)
                if is_hfs:
                    hfs_fmt = format_struct(self.byte_order_char, FMT_HFS_HEADER)
                    hfs_header_bytes = f_raw.read(SIZE_HFS_HEADER)
                    if len(hfs_header_bytes) < SIZE_HFS_HEADER: raise IOError("File too short for HFS header.")
                    try:
                        self.hfs_header = HFSHeader(*struct.unpack(hfs_fmt, hfs_header_bytes))
                    except struct.error as e: raise IOError(f"Failed to parse HFS header struct: {e}") from e
                    self.hfs_disk_header_length = 0x20000 if self.hfs_header.type == 0 else 0x10

                    if f_raw.tell() < self.hfs_disk_header_length :
                        f_raw.seek(self.hfs_disk_header_length)
                    elif f_raw.tell() > self.hfs_disk_header_length:
                         _q_status(f"Warning: HFS indicates ARC data starts at {self.hfs_disk_header_length}, but current stream position is {f_raw.tell()} (already past it). This might be unusual.", STATUS_WARN)
                else:
                    self.hfs_header = None; self.hfs_disk_header_length = 0

                if self._file_size - f_raw.tell() < SIZE_HEADER_COMMON:
                    raise IOError(f"File too short for ARC header after HFS processing. Remaining: {self._file_size - f_raw.tell()} bytes.")

                arc_header_common_fmt = format_struct(self.byte_order_char, FMT_HEADER_COMMON)
                arc_header_bytes_raw = f_raw.read(SIZE_HEADER_COMMON)
                if len(arc_header_bytes_raw) < SIZE_HEADER_COMMON: raise IOError("Incomplete ARC header read.")

                try:
                    self.arc_header = ARCHeader(*struct.unpack(arc_header_common_fmt, arc_header_bytes_raw))
                except struct.error as e: raise IOError(f"Failed to parse ARC header: {e}") from e

                self.version = self.arc_header.version
                _q_status(f"Diag: File '{os.path.basename(filepath)}' - Parsed ARC Header: Magic={self.arc_header.magic!r}, Version={self.version}, EntryCount={self.arc_header.entry_count}", STATUS_DEBUG)

                if self.arc_header.magic not in [MAGIC_ARC_LE, MAGIC_ARC_BE]:
                     _q_status(f"Warning: ARC header magic {self.arc_header.magic!r} is not standard ARC LE/BE.", STATUS_WARN)


                self.header_length = SIZE_HEADER_COMMON
                self.entry_struct_fmt = format_struct(self.byte_order_char, FMT_ENTRY)
                self.entry_struct_size = SIZE_ENTRY

                if self.platform == Platform.Switch:
                    self.entry_struct_fmt = format_struct('<', FMT_ENTRY_SWITCH)
                    self.entry_struct_size = SIZE_ENTRY_SWITCH
                elif self.platform == Platform.PC or self.platform == Platform.CTR:
                    if self.byte_order_char == '<' and self.version not in [7, 8]:
                        self.header_length += SIZE_HEADER_PC_EXTRA
                        if f_raw.tell() == (self.hfs_disk_header_length + SIZE_HEADER_COMMON):
                            extra_bytes = f_raw.read(SIZE_HEADER_PC_EXTRA)
                            if len(extra_bytes) < SIZE_HEADER_PC_EXTRA:
                                _q_status(f"Warning: Expected PC extra header field for LE v{self.version}, but file is too short at this point.", STATUS_WARN)
                    pass

                entry_count = self.arc_header.entry_count
                if entry_count < 0 : raise ValueError(f"Invalid negative entry_count: {entry_count}.")
                if entry_count == 0: _q_status("Info: ARC contains 0 file entries.", STATUS_INFO); self.files = []; return

                metadata_block_size_expected = entry_count * self.entry_struct_size
                if metadata_block_size_expected < 0 : raise ValueError("Invalid metadata size calculation (negative).")

                metadata_source_stream = f_raw

                remaining_file_after_arc_header = self._file_size - f_raw.tell()
                if remaining_file_after_arc_header < metadata_block_size_expected:
                        _q_status(f"Warning: File is too short for the declared metadata block. Expected {metadata_block_size_expected}b after ARC header, have {remaining_file_after_arc_header}b. Entry parsing may fail or be incomplete.", STATUS_WARN)
                        if self.entry_struct_size > 0:
                            actual_entries_possible = remaining_file_after_arc_header // self.entry_struct_size
                            if actual_entries_possible < entry_count:
                                _q_status(f"Warning: Will attempt to parse only {actual_entries_possible} entries instead of declared {entry_count}.", STATUS_WARN)
                                entry_count = actual_entries_possible
                                metadata_block_size_expected = entry_count * self.entry_struct_size
                        elif entry_count > 0:
                            raise ValueError("Entry struct size is zero, but entry count is non-zero. Cannot parse.")


                for i in range(entry_count):
                    entry_data_bytes = metadata_source_stream.read(self.entry_struct_size)
                    if len(entry_data_bytes) < self.entry_struct_size:
                        _q_status(f"Warning: Metadata stream ended prematurely while reading entry {i+1}. Expected {self.entry_struct_size} bytes, got {len(entry_data_bytes)}. Parsed {i} entries.", STATUS_WARN)
                        break

                    fi = create_file_info()
                    fi["platform"] = self.platform
                    fi["arc_byte_order_char"] = self.byte_order_char

                    try:
                        unpacked_entry = struct.unpack(self.entry_struct_fmt, entry_data_bytes)
                        if self.platform == Platform.Switch:
                            fi.update(zip(["filename_base","ext_hash","compressed_size","uncompressed_size_raw","unknown1","offset"], unpacked_entry))
                        else:
                            fi.update(zip(["filename_base","ext_hash","compressed_size","uncompressed_size_raw","offset"], unpacked_entry))
                            fi["unknown1"] = None

                        csz = fi.get("compressed_size")
                        calcsz = get_calculated_uncompressed_size(fi)

                        if self.platform == Platform.Switch:
                            fi["is_compressed"] = (csz is not None and csz > 0)
                        else:
                            fi["is_compressed"] = (csz is not None and calcsz is not None and
                                                  csz > 0 and csz != calcsz)

                        fi["full_filename"] = get_full_filename(fi)
                        fi["calculated_uncompressed_size"] = calcsz

                        if not isinstance(csz, int) or csz < 0:
                            _q_status(f"Warning: File '{fi['full_filename']}' (entry {i+1}) has invalid compressed size ({csz}). Skipping.",STATUS_WARN);continue
                        if calcsz is not None and calcsz < 0:
                            _q_status(f"Warning: File '{fi['full_filename']}' (entry {i+1}) has negative calculated uncompressed size ({calcsz}).",STATUS_WARN)

                        offset_val = fi.get("offset")
                        if not isinstance(offset_val, int) or offset_val < 0:
                            _q_status(f"Warning: File '{fi['full_filename']}' (entry {i+1}) has invalid data offset ({offset_val}). Skipping.",STATUS_WARN);continue

                        self.files.append(fi)
                    except struct.error as e_unpack_entry:
                        _q_status(f"Error parsing entry {i+1} data with format '{self.entry_struct_fmt}': {e_unpack_entry}. Entry might be corrupt. Skipping.", STATUS_WARN)
                    except Exception as e_process_entry:
                        _q_status(f"Unexpected error processing entry {i+1} ('{fi.get('full_filename','?')}'): {e_process_entry}. Skipping.", STATUS_WARN)
                        traceback.print_exc(file=sys.stderr)

                declared_entry_count = self.arc_header.entry_count
                if len(self.files) < declared_entry_count:
                    _q_status(f"Warning: Successfully parsed {len(self.files)} entries, but header declared {declared_entry_count}. File might be incomplete or corrupted.", STATUS_WARN)
                else:
                    _q_status(f"Info: Successfully parsed {len(self.files)} entries.", STATUS_INFO)

                # NEW: Attempt to read HFS Footer if it's an HFS file
                if is_hfs:
                    _q_status(f"Diag: HFS - Attempting to read HFS footer.", STATUS_DEBUG)
                    # HFS Footer is at the end of the file, preceded by 16-byte alignment padding
                    hfs_footer_start_offset = self._file_size - SIZE_HFS_FOOTER
                    if hfs_footer_start_offset >= 0:
                        f_raw.seek(hfs_footer_start_offset)
                        hfs_footer_bytes = f_raw.read(SIZE_HFS_FOOTER)
                        if len(hfs_footer_bytes) == SIZE_HFS_FOOTER:
                            hfs_footer_fmt = format_struct(self.byte_order_char, FMT_HFS_FOOTER)
                            try:
                                self.hfs_footer = HFSFooter(*struct.unpack(hfs_footer_fmt, hfs_footer_bytes))
                                _q_status(f"Diag: HFS - Footer read successfully: {self.hfs_footer}", STATUS_DEBUG)
                            except struct.error as e:
                                _q_status(f"Warning: Failed to parse HFS footer struct: {e}. Footer will not be re-saved.", STATUS_WARN)
                                self.hfs_footer = None
                        else:
                            _q_status(f"Warning: Incomplete HFS footer read. Expected {SIZE_HFS_FOOTER}b, got {len(hfs_footer_bytes)}b. Footer will not be re-saved.", STATUS_WARN)
                            self.hfs_footer = None
                    else:
                        _q_status(f"Warning: File too small to contain HFS footer. Footer will not be re-saved.", STATUS_WARN)
                        self.hfs_footer = None


        except (FileNotFoundError,PermissionError,IOError,ValueError,RuntimeError)as e: # ARCCSkippedError is caught by callers
            _q_status(f"Error loading ARC file {os.path.basename(filepath)}: {e}", STATUS_ERROR); raise
        except Exception as e:
            _q_status(f"CRITICAL UNHANDLED EXCEPTION during ARC load for {os.path.basename(filepath)}: {e}", STATUS_ERROR)
            traceback.print_exc(file=sys.stderr)
            raise IOError(f"Critical load failure for {os.path.basename(filepath)}: {e}") from e


    def extract_file(self, file_info, input_arc_path):
        if not self._raw_file_path or self._raw_file_path != input_arc_path or self._file_size is None:
            fn_display = file_info.get('full_filename', '?')
            arc_fn_display = os.path.basename(input_arc_path) if input_arc_path else '?'
            raise RuntimeError(f"MTArc state is invalid for extracting '{fn_display}' from '{arc_fn_display}'. Load may have failed or ARC not loaded.")

        try:
            offset_in_arc_struct = int(file_info.get("offset",0))
            data_disk_offset = self.hfs_disk_header_length + offset_in_arc_struct
        except Exception as e_offset:
            raise ValueError(f"Invalid offset '{file_info.get('offset')}' or HFS length '{self.hfs_disk_header_length}' for file '{file_info.get('full_filename','?')}': {e_offset}") from e_offset

        compressed_size_from_entry = file_info.get("compressed_size")
        raw_data_bytes = b''

        if not isinstance(compressed_size_from_entry, int) or compressed_size_from_entry < 0:
            print(f"Warning: Skipping extraction of '{file_info.get('full_filename','?')}' due to invalid compressed size ({compressed_size_from_entry}).",file=sys.stderr)
            return b''
        if compressed_size_from_entry == 0:
            return b''

        try:
            with open(self._raw_file_path,'rb') as f_arc_stream:
                if data_disk_offset < 0 or data_disk_offset >= self._file_size:
                    print(f"Warning: Calculated data offset {data_disk_offset} for '{file_info.get('full_filename','?')}' is out of file bounds (0-{self._file_size-1}). Skipping extraction.",file=sys.stderr)
                    return b''

                actual_read_size = compressed_size_from_entry
                if data_disk_offset + compressed_size_from_entry > self._file_size:
                    print(f"Warning: Requested read ({compressed_size_from_entry} bytes from offset {data_disk_offset}) for '{file_info.get('full_filename','?')}' exceeds file size ({self._file_size}). Truncating read to end of file.",file=sys.stderr)
                    actual_read_size = self._file_size - data_disk_offset
                    actual_read_size = max(0, actual_read_size)

                if actual_read_size <= 0:
                    return b''

                f_arc_stream.seek(data_disk_offset)
                read_bytes = f_arc_stream.read(actual_read_size)
                if len(read_bytes) != actual_read_size:
                     print(f"Warning: Short read for '{file_info.get('full_filename','?')}'. Expected {actual_read_size}, got {len(read_bytes)}. File may be corrupt or truncated.",file=sys.stderr)

                # ARCC_REMOVED: Entire block for ARCC data decryption
                # ARCC_REMOVED: if False: # ARCC_REMOVED: self.is_arcc would be False, crypto would be None. This block is effectively disabled.
                # ARCC_REMOVED:     # ... (decryption logic) ...
                # ARCC_REMOVED: else:
                raw_data_bytes = read_bytes # ARCC_REMOVED: This will now always be the case.

        except Exception as e_read:
            raise IOError(f"Failed to read raw data for '{file_info.get('full_filename','?')}' from offset {data_disk_offset}, size {compressed_size_from_entry}: {e_read}") from e_read

        final_data = raw_data_bytes
        if file_info.get("is_compressed"):
            if not raw_data_bytes:
                final_data = b''
            else:
                try:
                    final_data = decompress_kontract_zlib(raw_data_bytes)
                except Exception as e_decompress:
                    print(f"Warning: Zlib decompression failed for '{file_info.get('full_filename','?')}': {e_decompress}. Returning pre-decompression data (size {len(raw_data_bytes)}).",file=sys.stderr)
                    final_data = raw_data_bytes

        expected_uncompressed_size = file_info.get("calculated_uncompressed_size")
        actual_final_size = len(final_data)

        if isinstance(expected_uncompressed_size, int) and expected_uncompressed_size >= 0:
            if actual_final_size > expected_uncompressed_size:
                final_data = final_data[:expected_uncompressed_size]
            elif actual_final_size < expected_uncompressed_size and expected_uncompressed_size > 0 :
                 pass
        return final_data


    def save(self, output_path, input_file_infos, key1=None, key2=None,
             target_version=None, target_platform=None, target_byte_order_char=None,
             target_is_arcc=False,
             target_entry_has_extended_names=False):

        if not input_file_infos: raise ValueError("No file information provided to save.");
        if not isinstance(input_file_infos,list): raise TypeError("input_file_infos must be a list of dictionaries.");

        final_packed_entry_count = 0
        file_data_stream = io.BytesIO()

        try:
            # ARCC_REMOVED: self.is_arcc = target_is_arcc # ARCC_REMOVED: This will not make it an ARCC.
            self.entry_has_extended_names = target_entry_has_extended_names

            self.platform = target_platform if target_platform is not None else DEFAULT_PLATFORM
            self.byte_order_char = target_byte_order_char if target_byte_order_char is not None else DEFAULT_BYTE_ORDER_CHAR
            self.version = target_version if target_version is not None else DEFAULT_VERSION

            self.header_length = SIZE_HEADER_COMMON
            if self.platform == Platform.PC and self.byte_order_char == '<' and self.version not in [7, 8]:
                 self.header_length += SIZE_HEADER_PC_EXTRA

            current_entry_struct_format_string = FMT_ENTRY
            current_entry_struct_size_val = SIZE_ENTRY
            if self.platform == Platform.Switch:
                current_entry_struct_format_string = FMT_ENTRY_SWITCH
                current_entry_struct_size_val = SIZE_ENTRY_SWITCH
                if self.byte_order_char == '>':
                    print("Warning: Saving Switch ARC with Big Endian header is non-standard. Entry table remains Little Endian.", file=sys.stderr)
                self.entry_struct_fmt = format_struct('<', current_entry_struct_format_string)
            else:
                if self.entry_has_extended_names:
                    current_entry_struct_format_string = FMT_ENTRY_EXTENDED_NAME
                    current_entry_struct_size_val = SIZE_ENTRY_EXTENDED_NAME
                self.entry_struct_fmt = format_struct(self.byte_order_char, current_entry_struct_format_string)
            self.entry_struct_size = current_entry_struct_size_val

            hfs_disk_header_len_for_save = 0
            arc_content_start_on_disk = 0

            if self.hfs_header:
                hfs_disk_header_len_for_save = self.hfs_disk_header_length if self.hfs_disk_header_length > 0 else 0x20000
                if self.hfs_header.type == 0x10 and hfs_disk_header_len_for_save != 0x10:
                     hfs_disk_header_len_for_save = 0x10
                arc_content_start_on_disk = hfs_disk_header_len_for_save
                print(f"Diag: Save - HFS header detected. ARC content will start at {arc_content_start_on_disk:#x} (hfs_disk_header_len_for_save).")
            else:
                print("Diag: Save - No HFS header detected for original ARC. ARC content starts at 0.")

            num_entries_to_write = len(input_file_infos)
            data_payload_start_offset_in_arc_relative = self.header_length + (num_entries_to_write * self.entry_struct_size)

            alignment_value = 0
            if self.version == 9:
                alignment_value = ALIGNMENT_SWITCH
            elif self.version in [4, 7, 8, 0x10] and self.byte_order_char == '<':
                alignment_value = ALIGNMENT_PC_V7_V10_LE
            elif self.version == 0x11 and self.byte_order_char == '<':
                alignment_value = ALIGNMENT_PC_DEFAULT

            if alignment_value > 1:
                data_payload_start_offset_in_arc_relative = (data_payload_start_offset_in_arc_relative + alignment_value - 1) & ~(alignment_value - 1)
                print(f"Diag: Save - Aligned data payload start offset (relative to ARC header) to {data_payload_start_offset_in_arc_relative:#x} (alignment {alignment_value:#x}).")
            else:
                print(f"Diag: Save - No alignment applied. Data payload start offset (relative to ARC header): {data_payload_start_offset_in_arc_relative:#x}.")

            current_data_offset_for_entry = data_payload_start_offset_in_arc_relative

            updated_file_infos_for_metadata = []
            for idx, fi_original in enumerate(input_file_infos):
                original_data = fi_original.get("data", b"")
                full_fn_display = fi_original.get("full_filename", f"entry_{idx}")
                if not isinstance(original_data, bytes): original_data = b''

                uncompressed_size = len(original_data)

                original_raw_u_size_hint = fi_original.get("original_uncompressed_size_raw_hint")
                if original_raw_u_size_hint is not None and isinstance(original_raw_u_size_hint, int):
                    original_raw_u_size_for_calc = original_raw_u_size_hint
                else:
                    original_raw_u_size_for_calc = 0

                uncompressed_size_for_metadata_entry = 0
                if self.platform == Platform.CTR or (self.platform == Platform.PC and self.byte_order_char == '<'):
                    uncompressed_size_for_metadata_entry = (original_raw_u_size_for_calc & ~0x00FFFFFF) | (uncompressed_size & 0x00FFFFFF)
                elif self.platform == Platform.PS3:
                    uncompressed_size_for_metadata_entry = (original_raw_u_size_for_calc & 0x00000007) | (uncompressed_size << 3)
                elif self.platform == Platform.Switch:
                    uncompressed_size_for_metadata_entry = uncompressed_size
                else:
                    uncompressed_size_for_metadata_entry = (original_raw_u_size_for_calc & 0x00000007) | (uncompressed_size << 3)

                compressed_data = original_data
                is_actually_compressed_for_entry = False

                original_was_compressed_hint = fi_original.get("original_is_compressed_hint")
                attempt_compression = False

                if uncompressed_size > 0:
                    if original_was_compressed_hint is True:
                        attempt_compression = True
                    elif original_was_compressed_hint is False:
                        attempt_compression = False
                    else:
                        if self.platform == Platform.Switch:
                            attempt_compression = True
                        else:
                            attempt_compression = True

                if attempt_compression:
                    try:
                        compressed_attempt = compress_kontract_zlib(original_data, level=ZLIB_COMPRESSION_LEVEL)
                        if original_was_compressed_hint is True:
                            compressed_data = compressed_attempt
                            is_actually_compressed_for_entry = True
                        elif self.platform == Platform.Switch:
                            compressed_data = compressed_attempt
                            is_actually_compressed_for_entry = True
                        elif original_was_compressed_hint is None and len(compressed_attempt) < uncompressed_size:
                            compressed_data = compressed_attempt
                            is_actually_compressed_for_entry = True
                    except Exception as e_compress:
                        print(f"ERROR: Zlib compression failed for '{full_fn_display}': {e_compress}. Storing raw data.",file=sys.stderr)
                        compressed_data = original_data

                data_to_write_to_stream = compressed_data
                # ARCC_REMOVED: Data encryption block for ARCC.
                # ARCC_REMOVED: if False: # ... (encryption logic) ...

                fi_to_save_in_metadata = fi_original.copy()
                fi_to_save_in_metadata["offset"] = current_data_offset_for_entry
                fi_to_save_in_metadata["compressed_size"] = len(data_to_write_to_stream)
                fi_to_save_in_metadata["uncompressed_size_raw"] = uncompressed_size_for_metadata_entry
                fi_to_save_in_metadata["platform"] = self.platform
                fi_to_save_in_metadata["is_compressed_in_arc"] = is_actually_compressed_for_entry
                if self.platform == Platform.Switch:
                    fi_to_save_in_metadata["unknown1"] = fi_original.get("unknown1", 0)
                else:
                    fi_to_save_in_metadata["unknown1"] = None

                file_data_stream.write(data_to_write_to_stream)
                current_data_offset_for_entry += len(data_to_write_to_stream)
                updated_file_infos_for_metadata.append(fi_to_save_in_metadata)

            output_p_obj = pathlib.Path(output_path); output_p_obj.parent.mkdir(parents=True, exist_ok=True)
            with open(output_p_obj, 'wb') as f_out:
                if self.hfs_header:
                    hfs_header_struct_bytes = struct.pack(format_struct(self.byte_order_char, FMT_HFS_HEADER),
                                                          self.hfs_header.magic, self.hfs_header.version,
                                                          self.hfs_header.type, self.hfs_header.file_size, self.hfs_header.padding)
                    f_out.write(hfs_header_struct_bytes)
                    padding_needed_for_hfs = arc_content_start_on_disk - len(hfs_header_struct_bytes)
                    if padding_needed_for_hfs > 0: f_out.write(b'\x00' * padding_needed_for_hfs)
                    elif padding_needed_for_hfs < 0: raise RuntimeError(f"HFS header (size {len(hfs_header_struct_bytes)}) is larger than allocated HFS disk header space ({arc_content_start_on_disk}).")
                    f_out.seek(arc_content_start_on_disk)
                    print(f"Diag: Save - Wrote HFS header and padded to ARC content start at {arc_content_start_on_disk:#x}.")

                f_out.write(b'\x00' * self.header_length)
                print(f"Diag: Save - Wrote {self.header_length} bytes placeholder for ARC header.")

                metadata_block_plain = bytearray()
                name_field_len_for_packing = 128 if self.entry_has_extended_names else 64

                for fi_meta in updated_file_infos_for_metadata:
                    packed_name_bytes = fi_meta.get("filename_base", b"").ljust(name_field_len_for_packing, b'\x00')[:name_field_len_for_packing]

                    entry_values_tuple = ()
                    if self.platform == Platform.Switch:
                        entry_values_tuple = (packed_name_bytes, fi_meta.get("ext_hash",0),
                                              fi_meta.get("compressed_size",0), fi_meta.get("uncompressed_size_raw",0),
                                              fi_meta.get("unknown1",0), fi_meta.get("offset",0))
                    else:
                        entry_values_tuple = (packed_name_bytes, fi_meta.get("ext_hash",0),
                                              fi_meta.get("compressed_size",0), fi_meta.get("uncompressed_size_raw",0),
                                              fi_meta.get("offset",0))

                    if entry_values_tuple[2] < 0 or entry_values_tuple[-1] < 0:
                        print(f"Warning: Skipping packing entry for '{fi_meta.get('full_filename','?')}' due to invalid size/offset in metadata.",file=sys.stderr)
                        continue
                    try:
                        packed_entry_bytes = struct.pack(self.entry_struct_fmt, *entry_values_tuple)
                        metadata_block_plain.extend(packed_entry_bytes)
                        final_packed_entry_count += 1
                    except Exception as e_pack_entry:
                        print(f"ERROR: Failed to pack entry data for '{fi_meta.get('full_filename','?')}': {e_pack_entry}. Skipping this entry.",file=sys.stderr)

                metadata_to_write_to_disk = bytes(metadata_block_plain)
                # ARCC_REMOVED: Metadata encryption block for ARCC.
                # ARCC_REMOVED: if False: # ... (encryption logic) ...

                f_out.write(metadata_to_write_to_disk)
                print(f"Diag: Save - Wrote metadata block ({len(metadata_to_write_to_disk)} bytes).")

                current_pos_after_metadata_abs = f_out.tell()
                expected_data_payload_start_abs = arc_content_start_on_disk + data_payload_start_offset_in_arc_relative

                padding_needed_before_data = expected_data_payload_start_abs - current_pos_after_metadata_abs
                if padding_needed_before_data > 0:
                    f_out.write(b'\x00' * padding_needed_before_data)
                    print(f"Diag: Save - Wrote {padding_needed_before_data} bytes of padding before data payload.")
                elif padding_needed_before_data < 0:
                    raise RuntimeError(f"Internal Save Error: Metadata block (size {len(metadata_to_write_to_disk)}) overran calculated data payload start. Overrun by {-padding_needed_before_data} bytes. Expected meta end: {expected_data_payload_start_abs}, actual: {current_pos_after_metadata_abs}.")

                f_out.write(file_data_stream.getvalue())
                print(f"Diag: Save - Wrote data payload ({len(file_data_stream.getvalue())} bytes).")

                if self.hfs_header and self.hfs_footer:
                    f_out.seek(0, io.SEEK_END)
                    print(f"Diag: Save - Current end of file: {f_out.tell()} bytes. Padding for HFS footer (alignment 16).")
                    pad_stream(f_out, 16)
                    hfs_footer_struct_bytes = struct.pack(format_struct(self.byte_order_char, FMT_HFS_FOOTER), *self.hfs_footer)
                    f_out.write(hfs_footer_struct_bytes)
                    print(f"Diag: Save - Wrote HFS footer ({len(hfs_footer_struct_bytes)} bytes). New file size: {f_out.tell()} bytes.")

                f_out.seek(arc_content_start_on_disk)
                output_magic_bytes = (MAGIC_ARC_BE if self.byte_order_char == '>' else MAGIC_ARC_LE)


                final_arc_header_bytes_list = [
                    struct.pack(format_struct(self.byte_order_char, FMT_HEADER_COMMON),
                                output_magic_bytes, self.version, final_packed_entry_count)
                ]
                if self.platform == Platform.PC and self.byte_order_char == '<' and self.version not in [7, 8]:
                    final_arc_header_bytes_list.append(struct.pack(self.byte_order_char + "I", 0))

                f_out.write(b"".join(final_arc_header_bytes_list))
                print(f"Diag: Save - Wrote final ARC header to offset {arc_content_start_on_disk:#x}. Final entry count: {final_packed_entry_count}.")

            print(f"Successfully saved ARC to '{output_path}' with {final_packed_entry_count} files.")
        except Exception as e_save_main:
            print(f"ERROR: Failed to save ARC to '{output_path}': {e_save_main}",file=sys.stderr)
            traceback.print_exc(file=sys.stderr)
            if os.path.exists(output_path) and final_packed_entry_count == 0 :
                try: os.remove(output_path)
                except Exception as ce: print(f"Warning: Failed to clean up partially saved file '{output_path}': {ce}",file=sys.stderr)
            raise RuntimeError(f"Failed to save ARC to '{os.path.basename(output_path)}': {e_save_main}") from e_save_main
        finally:
            if file_data_stream: file_data_stream.close()


    def close(self):
        self.hfs_header = None; self.hfs_footer = None; self.arc_header = None; self.files = []
        self._raw_file_path = None; self._decrypted_entries_bytes = None
        self.crypto = None;
        self.entry_has_extended_names = False


# --- BATCH OPERATIONS (Workers and Orchestrators) ---
# MODIFIED: status_queue parameter to status_callback_worker
def _list_extract_worker(arc_path_str: str, output_base_dir_str: str | None, key1: str | None, key2: str | None, status_callback_worker: callable):
    arc_path = pathlib.Path(arc_path_str); arc = None
    try:
        arc_filename = arc_path.name; arc_basename = arc_path.stem
        output_folder = arc_path.parent / f"{arc_basename}_arc"

        status_callback_worker(f"Attempting to load {arc_filename}...", STATUS_DEBUG)
        arc = MTArc(); arc.load(str(arc_path), key1=key1, key2=key2, status_queue_or_callback=status_callback_worker)

        try: output_folder.mkdir(parents=True, exist_ok=True)
        except Exception as e: raise IOError(f"Failed to create output folder {output_folder}: {e}") from e
        if not os.access(output_folder, os.W_OK): raise PermissionError(f"Write permission denied for output folder: {output_folder}")

        platform_name_map = {Platform.UNKNOWN: "Unknown", Platform.PC: "PC", Platform.CTR: "CTR", Platform.PS3: "PS3", Platform.Switch: "Switch"}
        platform_name = platform_name_map.get(arc.platform, f"PVal {arc.platform}")

        relative_output_folder_str = f"./{output_folder.name}"
        status_callback_worker(f" Extracting {len(arc.files)} files from {platform_name} (v{arc.version}, BO:{arc.byte_order_char}) ARC '{arc_filename}' to '{relative_output_folder_str}'...", STATUS_INFO)


        processed_count = 0; error_count = 0
        for file_info in arc.files:
            if not isinstance(file_info, dict) or "full_filename" not in file_info:
                status_callback_worker(f"  Skipping invalid file info in {arc_filename}: {file_info!r}",STATUS_WARN)
                error_count += 1; continue
            try:
                file_data = arc.extract_file(file_info, str(arc_path))
                full_filename_from_arc = file_info.get("full_filename", "")
                path_obj_for_components = pathlib.Path(full_filename_from_arc)

                sanitized_disk_components = []
                for component_str in path_obj_for_components.parts:
                    current_component = re.sub(r'[\x00-\x1F]', '', component_str)
                    current_component = re.sub(r'[\\/:*?"<>|]', '_', current_component)
                    current_component = current_component.strip(' .')

                    if not current_component or ".." in current_component:
                        original_component_for_error_msg = component_str
                        status_callback_worker(f"  Skipping unsafe or empty path component '{original_component_for_error_msg}' (became '{current_component}') from ARC path '{full_filename_from_arc}'.",'level',STATUS_ERROR)
                        raise ValueError(f"Unsafe or empty path component: '{current_component}' (original: '{original_component_for_error_msg}')")
                    sanitized_disk_components.append(current_component)

                if not sanitized_disk_components:
                    sanitized_disk_components = [f"unnamed_file_{processed_count+error_count}_{file_info.get('ext_hash',0):08X}"]
                    status_callback_worker(f"  Filename for entry in {arc_filename} became invalid or empty after sanitization. Using '{sanitized_disk_components[0]}'. Original: '{full_filename_from_arc}'",'level',STATUS_WARN)

                output_file_path = output_folder.joinpath(*sanitized_disk_components)

                output_file_path.parent.mkdir(parents=True, exist_ok=True)
                with open(output_file_path, 'wb') as out_f: out_f.write(file_data)
                processed_count += 1
            except (OSError, ValueError, PermissionError) as e:
                status_callback_worker(f"  File System Error writing '{file_info.get('full_filename','?')}' from {arc_filename}: {e}", STATUS_ERROR)
                error_count += 1
            except Exception as e:
                status_callback_worker(f"  Error extracting '{file_info.get('full_filename','?')}' from {arc_filename}: {e}", STATUS_ERROR)
                status_callback_worker(f"  Trace: {traceback.format_exc()}",STATUS_DEBUG)
                error_count += 1

        success = (error_count == 0) if (processed_count > 0 or len(arc.files)==0) else False
        level = STATUS_SUCCESS if success and processed_count > 0 else \
                (STATUS_WARN if processed_count > 0 else \
                 (STATUS_ERROR if error_count > 0 else STATUS_INFO))
        msg_suffix = (f", {error_count} errors." if error_count else ".")
        msg = f"Finished {arc_filename}. {processed_count} extracted{msg_suffix}" if len(arc.files)>0 else f"No files in {arc_filename}."
        if not arc.files and error_count > 0 and processed_count == 0:
             msg = f"Failed loading/processing {arc_filename} (no files found or processed, {error_count} errors)."
        status_callback_worker(msg, level);
        return arc_filename, success
    except ARCCSkippedError as e:
        # status_callback_worker already handled by MTArc.load
        return arc_path.name, True
    except (FileNotFoundError, PermissionError, IOError, ValueError, RuntimeError) as e:
        status_callback_worker(f"Failed load/process ARC {arc_path.name}: {e}",STATUS_ERROR)
        return arc_path.name,False
    except Exception as e:
        status_callback_worker(f"Unexpected error processing ARC {arc_path.name}: {e}", STATUS_ERROR)
        status_callback_worker(f"Trace: {traceback.format_exc()}",STATUS_DEBUG)
        return arc_path.name, False
    finally:
        if arc: arc.close()

# MODIFIED: status_queue parameter to status_callback_worker
def _flatten_extract_worker(arc_path_str: str, common_output_dir_str: str, key1: str | None, key2: str | None, status_callback_worker: callable):
    arc_path = pathlib.Path(arc_path_str)
    common_output_dir = pathlib.Path(common_output_dir_str)
    arc = None
    try:
        arc_filename = arc_path.name
        arc_basename_no_ext = arc_path.stem

        status_callback_worker(f"Attempting to load {arc_filename} for flattened extraction...", STATUS_DEBUG)
        arc = MTArc()
        arc.load(str(arc_path), key1=key1, key2=key2, status_queue_or_callback=status_callback_worker)

        if not os.access(common_output_dir, os.W_OK):
            raise PermissionError(f"Write permission denied for common output folder: {common_output_dir}")

        platform_name_map = {Platform.UNKNOWN: "Unknown", Platform.PC: "PC", Platform.CTR: "CTR", Platform.PS3: "PS3", Platform.Switch: "Switch"}
        platform_name = platform_name_map.get(arc.platform, f"PVal {arc.platform}")
        status_callback_worker(f" Flatten extracting {len(arc.files)} files from {platform_name} (v{arc.version}) ARC '{arc_filename}' to '{common_output_dir.name}/'...", STATUS_INFO)

        processed_count = 0
        error_count = 0
        for file_info in arc.files:
            if not isinstance(file_info, dict) or "full_filename" not in file_info:
                status_callback_worker(f"  Skipping invalid file info in {arc_filename} (flattened): {file_info!r}",STATUS_WARN)
                error_count += 1
                continue
            try:
                file_data = arc.extract_file(file_info, str(arc_path))

                internal_full_path = pathlib.Path(file_info.get("full_filename", ""))
                sanitized_internal_basename = re.sub(r'[\x00-\x1F\\/:*?"<>|]', '_', internal_full_path.stem).strip(' .')
                sanitized_internal_ext = internal_full_path.suffix
                if not sanitized_internal_basename:
                    sanitized_internal_basename = f"unnamed_{file_info.get('ext_hash',0):08X}"

                flat_filename_str = f"{arc_basename_no_ext}_{sanitized_internal_basename}{sanitized_internal_ext}"
                flat_filename_str = re.sub(r'[\x00-\x1F\\/:*?"<>|]', '_', flat_filename_str).strip(' .')
                if not flat_filename_str:
                    flat_filename_str = f"{arc_basename_no_ext}_unnamed_{processed_count+error_count}_{file_info.get('ext_hash',0):08X}{sanitized_internal_ext}"

                output_file_path = common_output_dir / flat_filename_str

                with open(output_file_path, 'wb') as out_f:
                    out_f.write(file_data)
                processed_count += 1
            except (OSError, ValueError, PermissionError) as e:
                status_callback_worker(f"  File System Error writing '{file_info.get('full_filename','?')}' (flat) from {arc_filename}: {e}", STATUS_ERROR)
                error_count += 1
            except Exception as e:
                status_callback_worker(f"  Error flat-extracting '{file_info.get('full_filename','?')}' from {arc_filename}: {e}", STATUS_ERROR)
                status_callback_worker(f"  Trace: {traceback.format_exc()}",STATUS_DEBUG)
                error_count += 1

        success = (error_count == 0) if (processed_count > 0 or len(arc.files) == 0) else False
        level = STATUS_SUCCESS if success and processed_count > 0 else \
                (STATUS_WARN if processed_count > 0 else \
                 (STATUS_ERROR if error_count > 0 else STATUS_INFO))
        msg_suffix = (f", {error_count} errors." if error_count else ".")
        msg = f"Finished flat extraction for {arc_filename}. {processed_count} files extracted{msg_suffix}" if len(arc.files) > 0 else f"No files in {arc_filename} for flat extraction."
        status_callback_worker(msg, level)
        return arc_filename, success
    except ARCCSkippedError as e:
        return arc_path.name, True
    except (FileNotFoundError, PermissionError, IOError, ValueError, RuntimeError) as e:
        status_callback_worker(f"Failed load/process ARC {arc_path.name} (flattened): {e}",STATUS_ERROR)
        return arc_path.name, False
    except Exception as e:
        status_callback_worker(f"Unexpected error processing ARC {arc_path.name} (flattened): {e}", STATUS_ERROR)
        status_callback_worker(f"Trace: {traceback.format_exc()}",STATUS_DEBUG)
        return arc_path.name, False
    finally:
        if arc: arc.close()

# MODIFIED: status_queue parameter to status_callback_worker
def _list_inject_worker(source_folder_str: str, output_rebuilt_dir_str: str | None,
                        key1: str | None, key2: str | None, status_callback_worker: callable,
                        target_arc_filename_override: str | None = None,
                        original_arc_version: int | None = None,
                        original_arc_platform: Platform | None = None,
                        original_arc_byte_order_char: str | None = None,
                        target_is_arcc: bool = False,
                        original_file_order: list | None = None,
                        entry_has_extended_names_for_rebuild: bool = False,
                        original_file_metadata_map: dict | None = None):
    source_folder_path = pathlib.Path(source_folder_str)
    if not output_rebuilt_dir_str:
        status_callback_worker(f"Output dir not provided for '{source_folder_path.name}'.",STATUS_ERROR)
        return source_folder_path.name, False
    output_rebuilt_dir = pathlib.Path(output_rebuilt_dir_str); arc_saver = None
    try:
        folder_name_raw = source_folder_path.name
        arc_base_name = folder_name_raw[:-4] if folder_name_raw.endswith("_arc") else folder_name_raw
        output_arc_path = output_rebuilt_dir / (target_arc_filename_override if target_arc_filename_override else f"{arc_base_name}.arc")
        status_callback_worker(f"Processing folder '{folder_name_raw}' for rebuild as '{output_arc_path.name}'...", STATUS_DEBUG)

        files_to_pack = []; has_files_in_folder = False; error_reading_files = False
        name_field_len_for_fi_base = 128 if entry_has_extended_names_for_rebuild else 64

        try:
            if not source_folder_path.is_dir(): raise FileNotFoundError(f"Source folder not found: {source_folder_path.name}")
            if not os.access(source_folder_path, os.R_OK): raise PermissionError(f"Read permission denied for source folder: {source_folder_path.name}")

            for file_path_obj in source_folder_path.rglob('*'):
                if file_path_obj.is_file():
                    has_files_in_folder = True
                    if not os.access(str(file_path_obj), os.R_OK):
                        status_callback_worker(f"  Permission denied reading file '{file_path_obj.relative_to(source_folder_path)}'. Skipping.",STATUS_ERROR)
                        error_reading_files = True; continue
                    try:
                        with open(file_path_obj, 'rb') as f: data = f.read()
                        fi = create_file_info()
                        relative_arc_path = file_path_obj.relative_to(source_folder_path)
                        arc_internal_filename = str(relative_arc_path)
                        fi["full_filename"] = arc_internal_filename

                        base_for_arc, ext_for_arc_with_dot = os.path.splitext(arc_internal_filename)

                        try: fnb_encoded_str = base_for_arc.encode('ascii')
                        except UnicodeEncodeError: fnb_encoded_str = base_for_arc.encode('utf-8', errors='ignore')

                        fi["filename_base"] = fnb_encoded_str[:name_field_len_for_fi_base].ljust(name_field_len_for_fi_base,b'\x00')

                        assigned_hash = None
                        ext_no_dot = ext_for_arc_with_dot[1:] if ext_for_arc_with_dot.startswith('.') else ext_for_arc_with_dot

                        if ext_for_arc_with_dot.lower() in REV_EXTENSION_MAP:
                            assigned_hash = REV_EXTENSION_MAP[ext_for_arc_with_dot.lower()]
                        elif len(ext_no_dot) > 0 and len(ext_no_dot) <= 8 and all(c in "0123456789abcdefABCDEF" for c in ext_no_dot):
                            try: assigned_hash = int(ext_no_dot, 16)
                            except ValueError: pass
                        if assigned_hash is None and ext_no_dot:
                            assigned_hash = calculate_arc_hash(ext_no_dot)
                        elif assigned_hash is None:
                            assigned_hash = 0
                        fi["ext_hash"] = assigned_hash
                        fi["data"] = data

                        if original_file_metadata_map:
                            norm_disk_path_key = arc_internal_filename.lower().replace('\\', '/')
                            if norm_disk_path_key in original_file_metadata_map:
                                original_meta = original_file_metadata_map[norm_disk_path_key]
                                fi['original_is_compressed_hint'] = original_meta.get('is_compressed')
                                fi['original_uncompressed_size_raw_hint'] = original_meta.get('uncompressed_size_raw')

                        files_to_pack.append(fi)
                    except Exception as e_proc_file:
                        status_callback_worker(f"  Error processing file '{file_path_obj.relative_to(source_folder_path)}': {e_proc_file}",STATUS_ERROR)
                        traceback.print_exc(file=sys.stderr)
                        error_reading_files = True
        except (FileNotFoundError, PermissionError) as e_scan_folder:
            status_callback_worker(f"Error accessing input folder '{folder_name_raw}': {e_scan_folder}",STATUS_ERROR)
            return folder_name_raw,False
        except Exception as e_scan_unexpected:
            status_callback_worker(f"Unexpected error scanning folder '{folder_name_raw}': {e_scan_unexpected}",STATUS_ERROR)
            traceback.print_exc(file=sys.stderr)
            return folder_name_raw,False

        if not has_files_in_folder:
            status_callback_worker(f"Skipping empty folder: {folder_name_raw}",STATUS_WARN)
            return folder_name_raw,True
        if not files_to_pack and has_files_in_folder :
            status_callback_worker(f"Skipping '{folder_name_raw}', no files processed (all had errors or were unreadable).",STATUS_ERROR)
            return folder_name_raw,False

        if original_file_order:
            status_callback_worker(f" Sorting files for '{folder_name_raw}' based on original ARC order.",STATUS_DEBUG)
            file_map_by_norm_path = {
                fi['full_filename'].lower().replace('\\', '/'): fi
                for fi in files_to_pack
            }
            sorted_files = []

            original_filenames_normalized_lower_map = {
                orig_fn.lower().replace('\\', '/'): orig_fn
                for orig_fn in original_file_order
            }

            for orig_fn_norm_lower, orig_fn_case_preserved in original_filenames_normalized_lower_map.items():
                if orig_fn_norm_lower in file_map_by_norm_path:
                    sorted_files.append(file_map_by_norm_path.pop(orig_fn_norm_lower))
                else:
                    status_callback_worker(f"  Info: File '{orig_fn_case_preserved}' from original order not found in source folder '{folder_name_raw}'. It will be omitted.",STATUS_DEBUG)

            new_files_alpha_sorted = sorted(
                file_map_by_norm_path.values(),
                key=lambda fi: fi['full_filename'].lower().replace('\\', '/')
            )

            for new_fi in new_files_alpha_sorted:
                status_callback_worker(f"  Info: New file '{new_fi['full_filename']}' (not in original order) added to end of ARC for '{folder_name_raw}'.",STATUS_DEBUG)

            files_to_pack = sorted_files + new_files_alpha_sorted
        else:
            status_callback_worker(f" Sorting files for '{folder_name_raw}' alphabetically (no original order provided).",STATUS_DEBUG)
            try:
                files_to_pack.sort(key=lambda fi_sort: fi_sort.get("full_filename", "").lower().replace('\\', '/'))
            except Exception as e_sort:
                status_callback_worker(f"Warning: Alphabetical sort of files failed for '{folder_name_raw}': {e_sort}. Using unsorted order.",STATUS_WARN)

        arc_params_desc = "default (Switch v9, LE, 64b names)"
        if original_arc_version is not None and original_arc_platform is not None and original_arc_byte_order_char is not None:
            platform_map_names = {Platform.UNKNOWN: "?", Platform.PC: "PC", Platform.CTR: "CTR", Platform.PS3: "PS3", Platform.Switch: "Switch"}
            p_name_desc = platform_map_names.get(original_arc_platform, f"PVal?{original_arc_platform}")
            bo_name_desc = "BE" if original_arc_byte_order_char == '>' else "LE"
            name_len_desc = "128b" if entry_has_extended_names_for_rebuild else "64b"
            arcc_desc = ""

            using_original_params_for_non_default = not (
                original_arc_version == DEFAULT_VERSION and
                original_arc_platform == DEFAULT_PLATFORM and
                original_arc_byte_order_char == DEFAULT_BYTE_ORDER_CHAR and
                not entry_has_extended_names_for_rebuild and
                not target_is_arcc
            )
            if using_original_params_for_non_default or original_file_order is not None or original_file_metadata_map:
                arc_params_desc = f"original (v{original_arc_version}, P:{p_name_desc}, BO:{bo_name_desc}, Names:{name_len_desc}{arcc_desc})"
        key_info_desc = ""

        status_callback_worker(f" Rebuilding '{output_arc_path.name}' ({len(files_to_pack)} files) using params: {arc_params_desc}{key_info_desc}...",STATUS_INFO)

        arc_saver = MTArc();
        try:
            output_rebuilt_dir.mkdir(parents=True, exist_ok=True)
        except Exception as e_mkdir: raise IOError(f"Failed create output dir '{output_rebuilt_dir}': {e_mkdir}") from e_mkdir

        if output_arc_path.exists() and not os.access(output_arc_path, os.W_OK):
            raise PermissionError(f"Write permission denied for existing output file: '{output_arc_path.name}'")
        if not os.access(output_rebuilt_dir, os.W_OK):
            raise PermissionError(f"Write permission denied for output directory: '{output_rebuilt_dir.name}'")

        try:
            if source_folder_path.resolve(strict=True).is_dir() and \
               output_arc_path.resolve(strict=False).is_relative_to(source_folder_path.resolve(strict=True)):
                status_callback_worker(f"Error: Output file '{output_arc_path.name}' would be inside its source folder '{folder_name_raw}'. Aborting to prevent data loss/recursion.",STATUS_ERROR)
                return folder_name_raw, False
        except Exception as e_path_safety:
             status_callback_worker(f"Warning: Path safety check for output '{output_arc_path.name}' encountered an issue: {e_path_safety}. Proceeding with caution.",STATUS_WARN)

        arc_saver.save(str(output_arc_path), files_to_pack, key1=key1, key2=key2,
                       target_version=original_arc_version, target_platform=original_arc_platform,
                       target_byte_order_char=original_arc_byte_order_char, target_is_arcc=target_is_arcc,
                       target_entry_has_extended_names=entry_has_extended_names_for_rebuild)

        status_callback_worker(f"Successfully rebuilt '{output_arc_path.name}'", STATUS_SUCCESS)
        return folder_name_raw, True
    except (FileNotFoundError, PermissionError, IOError, ValueError, RuntimeError) as e_worker_main:
        status_callback_worker(f"Failed to process folder '{source_folder_path.name}': {e_worker_main}",STATUS_ERROR)
        traceback.print_exc(file=sys.stderr)
        return source_folder_path.name,False
    except Exception as e_worker_unexpected:
        status_callback_worker(f"Unexpected error processing folder '{source_folder_path.name}': {e_worker_unexpected}", STATUS_ERROR)
        traceback.print_exc(file=sys.stderr)
        return source_folder_path.name, False
    finally:
        if arc_saver: arc_saver.close()

# MODIFIED: Removed internal status_queue, workers now use status_callback directly
def run_batch_parallel(worker_func, item_list, output_dir: str | None, progress_callback, status_callback, key1, key2,
                       original_arc_params_list: list | None = None,
                       target_is_arcc_list: list | None = None,
                       original_file_orders_list: list | None = None,
                       original_file_metadata_map_list: list | None = None):
    if not item_list:
        status_callback("No items selected for batch operation.", STATUS_WARN)
        progress_callback(100); return

    if worker_func == _list_inject_worker or worker_func == _flatten_extract_worker:
        if output_dir:
            output_path_obj = pathlib.Path(output_dir)
            try:
                if output_path_obj.exists():
                    if not output_path_obj.is_dir():
                        raise NotADirectoryError(f"Output path '{output_dir}' exists but is not a directory.")
                    if not os.access(output_path_obj, os.W_OK):
                        raise PermissionError(f"Write permission denied for output directory: {output_dir}")
                else:
                    output_path_obj.mkdir(parents=True, exist_ok=True)
            except Exception as e:
                status_callback(f"Output directory error for '{output_dir}': {e}", STATUS_ERROR)
                progress_callback(0); return

    total_tasks = len(item_list)
    status_callback(f"Starting parallel batch operation ({total_tasks} items) using {worker_func.__name__}...", STATUS_INFO)
    start_time = time.perf_counter(); completed_tasks = 0; success_count = 0; failure_count = 0
    futures = []

    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        for i, item_path_str_or_obj in enumerate(item_list):
            item_path_str = str(item_path_str_or_obj)

            args_for_worker = [item_path_str]
            if worker_func == _list_extract_worker:
                args_for_worker.extend([None, key1, key2, status_callback]) # Pass main status_callback to worker
            elif worker_func == _flatten_extract_worker:
                args_for_worker.extend([output_dir, key1, key2, status_callback]) # Pass main status_callback
            elif worker_func == _list_inject_worker:
                args_for_worker.append(output_dir)
                args_for_worker.extend([key1, key2, status_callback]) # Pass main status_callback
                args_for_worker.append(None) # target_arc_filename_override

                params = (original_arc_params_list[i]
                          if original_arc_params_list and i < len(original_arc_params_list) else {})
                args_for_worker.extend([params.get("version"), params.get("platform"), params.get("bo_char")])

                is_arcc = (target_is_arcc_list[i]
                           if target_is_arcc_list and i < len(target_is_arcc_list) else False)
                args_for_worker.append(is_arcc)

                file_order = (original_file_orders_list[i]
                              if original_file_orders_list and i < len(original_file_orders_list) else None)
                args_for_worker.append(file_order)

                entry_ext_names = params.get("entry_has_extended_names", False)
                args_for_worker.append(entry_ext_names)

                file_meta_map = (original_file_metadata_map_list[i]
                                 if original_file_metadata_map_list and i < len(original_file_metadata_map_list) else None)
                args_for_worker.append(file_meta_map)
            else:
                status_callback(f"Unknown worker function: {worker_func.__name__}", STATUS_ERROR)
                return

            futures.append(executor.submit(worker_func, *args_for_worker))

        for future in concurrent.futures.as_completed(futures):
            # Worker messages are now directly handled by the passed status_callback
            try:
                item_name, success = future.result()
                if success: success_count += 1
                else: failure_count +=1
            except Exception as e_future:
                failure_count += 1
                status_callback(f"Critical error from worker result processing: {e_future}", STATUS_ERROR)
                traceback.print_exc(file=sys.stderr)
            completed_tasks += 1
            progress_callback(completed_tasks / total_tasks * 100)

    # Worker messages are directly handled. This final flush is not strictly necessary
    # if all workers have completed and their callbacks were synchronous (like print).
    # Kept for safety in case of complex callback chains, but likely redundant for CLI.

    end_time = time.perf_counter(); duration = end_time - start_time
    summary_msg = f"Batch operation complete. Time: {duration:.2f} seconds. "
    summary_msg += f"Succeeded: {success_count}, Failed: {failure_count} (out of {total_tasks} total)."
    final_status_level = STATUS_SUCCESS if failure_count == 0 and success_count > 0 else \
                         (STATUS_WARN if success_count > 0 else \
                          (STATUS_ERROR if total_tasks > 0 else STATUS_INFO) )
    if total_tasks == 0 : final_status_level = STATUS_INFO
    status_callback(summary_msg, final_status_level)


def recursive_batch_extract(source_root_dir: str, output_base_dir: str | None, progress_callback: callable, status_callback: callable, key1: str | None, key2: str | None, max_workers=None):
    status_callback("Scanning for ARC files for recursive extraction...", STATUS_INFO)
    source_path = pathlib.Path(source_root_dir)
    if not source_root_dir:
        status_callback("Input Missing: Select source directory for recursive extraction.", STATUS_ERROR)
        progress_callback(0); return
    if not source_path.is_dir():
        status_callback(f"Source '{source_root_dir}' is not a valid directory.", STATUS_ERROR)
        progress_callback(0); return
    if not os.access(source_path, os.R_OK):
        status_callback(f"Read permission denied for source directory: {source_root_dir}", STATUS_ERROR)
        progress_callback(0); return
    try:
        arc_files_generator = source_path.rglob('*.arc')
        arc_files = [f for f in arc_files_generator if f.is_file()]
    except Exception as e:
        status_callback(f"Error scanning for ARC files in '{source_root_dir}': {e}", STATUS_ERROR)
        progress_callback(0); return

    if not arc_files:
        status_callback(f"No *.arc files found in '{source_root_dir}' or its subdirectories.", STATUS_WARN)
        progress_callback(100); return
    run_batch_parallel(_list_extract_worker, arc_files, None, progress_callback, status_callback, key1, key2)


def recursive_flatten_extract(source_root_dir: str, common_output_dir: str, progress_callback: callable, status_callback: callable, key1: str | None, key2: str | None):
    status_callback("Scanning for ARC files for recursive flattened extraction...", STATUS_INFO)
    source_path = pathlib.Path(source_root_dir)
    if not source_root_dir:
        status_callback("Input Missing: Select source directory for recursive flattened extraction.", STATUS_ERROR)
        progress_callback(0); return
    if not source_path.is_dir():
        status_callback(f"Source '{source_root_dir}' is not a valid directory.", STATUS_ERROR)
        progress_callback(0); return
    if not os.access(source_path, os.R_OK):
        status_callback(f"Read permission denied for source directory: {source_root_dir}", STATUS_ERROR)
        progress_callback(0); return

    if not common_output_dir:
        status_callback("Output Missing: Select an output directory for flattened files.", STATUS_ERROR)
        progress_callback(0); return

    try:
        arc_files_generator = source_path.rglob('*.arc')
        arc_files = [f for f in arc_files_generator if f.is_file()]
    except Exception as e:
        status_callback(f"Error scanning for ARC files in '{source_root_dir}': {e}", STATUS_ERROR)
        progress_callback(0); return

    if not arc_files:
        status_callback(f"No *.arc files found in '{source_root_dir}' or its subdirectories for flattened extraction.", STATUS_WARN)
        progress_callback(100); return

    run_batch_parallel(_flatten_extract_worker, arc_files, common_output_dir, progress_callback, status_callback, key1, key2)


def folder_batch_inject(source_dir_str: str, progress_callback: callable, status_callback: callable,
                        key1: str | None, key2: str | None, max_workers=None):
    start_time_overall = time.perf_counter()
    status_callback("Scanning for edited folders (*_arc) and matching original ARCs for in-place rebuild...", STATUS_INFO)
    if not source_dir_str:
        status_callback("Input Missing: Select source directory for folder injection.", STATUS_ERROR)
        progress_callback(0); return

    source_path = pathlib.Path(source_dir_str)
    if not source_path.is_dir():
        status_callback(f"Source '{source_dir_str}' is not a valid directory.", STATUS_ERROR)
        progress_callback(0); return
    if not os.access(source_path, os.R_OK | os.W_OK): # Check for write permission as well for backups
        status_callback(f"Read/Write permission denied for source directory: {source_dir_str}", STATUS_ERROR)
        progress_callback(0); return

    original_backup_root = source_path / "original_arc_backups"
    original_backup_root.mkdir(parents=True, exist_ok=True)

    tasks_for_submission = []
    # For CLI, status_callback is directly usable. For GUI, we'd use the queue via self.queue_status
    # The status_callback passed to folder_batch_inject will be the one to use.
    temp_status_callback_for_scan = status_callback # Use the main callback

    try:
        for edited_folder in source_path.rglob('*_arc'):
            if not edited_folder.is_dir(): continue

            try:
                if original_backup_root.resolve(strict=True).is_dir() and \
                   (original_backup_root.resolve(strict=True) in edited_folder.resolve(strict=True).parents or \
                    original_backup_root.resolve(strict=True) == edited_folder.resolve(strict=True)):
                    temp_status_callback_for_scan(f"Skipping folder within backup directory: {edited_folder.relative_to(source_path)}", STATUS_DEBUG)
                    continue
            except Exception: pass

            arc_basename = edited_folder.name[:-4]
            original_arc_file_path = edited_folder.parent / (arc_basename + ".arc")
            archived_original_arc_path = original_backup_root / original_arc_file_path.relative_to(source_path)

            original_arc_exists_live = original_arc_file_path.is_file()
            original_arc_exists_archived = archived_original_arc_path.is_file()

            if not original_arc_exists_live and not original_arc_exists_archived:
                temp_status_callback_for_scan(f"Original ARC '{original_arc_file_path.name}' (or its archive) not found for folder '{edited_folder.name}'. Skipping rebuild.", STATUS_WARN)
                continue

            try:
                if original_arc_exists_live and original_arc_file_path.resolve(strict=True).is_file() and \
                   edited_folder.resolve(strict=True).is_dir() and \
                   original_arc_file_path.resolve(strict=True).is_relative_to(edited_folder.resolve(strict=True)):
                    temp_status_callback_for_scan(f"Skipping '{edited_folder.name}': Its corresponding original ARC '{original_arc_file_path.name}' is located inside it. Move the ARC outside.", STATUS_ERROR)
                    continue
            except Exception: pass


            params_to_use = {"version": None, "platform": None, "bo_char": None,
                             "file_order": None, "entry_has_extended_names": False,
                             "original_file_metadata_map": {}}
            arc_to_get_params_from_path = original_arc_file_path if original_arc_exists_live else archived_original_arc_path
            temp_arc_loader = None
            try:
                temp_status_callback_for_scan(f"Attempting to load '{arc_to_get_params_from_path.name}' to get parameters...", STATUS_DEBUG)
                temp_arc_loader = MTArc()
                # For MTArc.load, pass the status_callback directly (it will handle queue-like or direct)
                temp_arc_loader.load(str(arc_to_get_params_from_path), status_queue_or_callback=temp_status_callback_for_scan)

                if not temp_arc_loader.arc_header:
                    temp_status_callback_for_scan(f"ERROR: Failed to load or parse header of original ARC '{arc_to_get_params_from_path.name}'. Cannot determine parameters for rebuild. Skipping this item.", STATUS_ERROR)
                    if temp_arc_loader: temp_arc_loader.close()
                    continue

                current_file_metadata_map = {}
                if temp_arc_loader.files:
                    for fi_orig in temp_arc_loader.files:
                        norm_path_key = fi_orig['full_filename'].lower().replace('\\','/')
                        current_file_metadata_map[norm_path_key] = {
                            'is_compressed': fi_orig['is_compressed'],
                            'uncompressed_size_raw': fi_orig['uncompressed_size_raw']
                        }

                params_to_use.update({
                    "version": temp_arc_loader.version,
                    "platform": temp_arc_loader.platform,
                    "bo_char": temp_arc_loader.byte_order_char,
                    "file_order": [fi['full_filename'] for fi in temp_arc_loader.files] if temp_arc_loader.files else [],
                    "entry_has_extended_names": temp_arc_loader.entry_has_extended_names,
                    "original_file_metadata_map": current_file_metadata_map
                })
                temp_status_callback_for_scan(f"Read params from '{arc_to_get_params_from_path.name}': v{params_to_use['version']}, P:{params_to_use['platform']}, BO:{params_to_use['bo_char']}, ExtNames:{params_to_use['entry_has_extended_names']}, Files:{len(params_to_use.get('file_order',[]))}", STATUS_DEBUG)

            except ARCCSkippedError as e_arcc_skip_params:
                temp_status_callback_for_scan(f"Info: Cannot use parameters from '{arc_to_get_params_from_path.name}' (skipped as .arcc). Skipping rebuild for '{edited_folder.name}'.", STATUS_INFO)
                if temp_arc_loader: temp_arc_loader.close()
                continue
            except Exception as e_load_params:
                temp_status_callback_for_scan(f"ERROR: Exception while loading original ARC '{arc_to_get_params_from_path.name}' for parameters: {e_load_params}. Skipping rebuild for this item.", STATUS_ERROR)
                traceback.print_exc(file=sys.stderr)
                if temp_arc_loader: temp_arc_loader.close()
                continue
            finally:
                if temp_arc_loader: temp_arc_loader.close()

            tasks_for_submission.append({
                "edited_folder_str": str(edited_folder),
                "original_arc_target_location_str": str(original_arc_file_path),
                "target_arc_filename_str": original_arc_file_path.name,
                "original_arc_params": params_to_use,
                "archived_original_arc_path_str": str(archived_original_arc_path)
            })
    except Exception as e_scan_folders_main:
        status_callback(f"Error during initial scan for folders/ARCs: {e_scan_folders_main}", STATUS_ERROR)
        traceback.print_exc(file=sys.stderr)
        progress_callback(0); return

    if not tasks_for_submission:
        status_callback("No matching *_arc folders and corresponding .arc files (with readable parameters) found to process.", STATUS_WARN)
        progress_callback(100); return

    total_initial_tasks = len(tasks_for_submission)
    status_callback(f"Found {total_initial_tasks} items for in-place rebuild. Preparing to archive originals and rebuild...", STATUS_INFO)

    tasks_ready_for_parallel_rebuild = []
    failed_archive_or_setup_count = 0

    for i, task_info in enumerate(tasks_for_submission):
        original_arc_target_loc_p = pathlib.Path(task_info["original_arc_target_location_str"])
        archived_original_arc_dest_p = pathlib.Path(task_info["archived_original_arc_path_str"])
        original_secured_for_rebuild = False

        if original_arc_target_loc_p.exists() and original_arc_target_loc_p.is_file():
            try:
                archived_original_arc_dest_p.parent.mkdir(parents=True, exist_ok=True)
                final_archive_path_p = archived_original_arc_dest_p
                if final_archive_path_p.exists():
                    timestamp_suffix = datetime.now().strftime("_backup_%Y%m%d%H%M%S%f")
                    final_archive_path_p = final_archive_path_p.with_name(
                        final_archive_path_p.stem + timestamp_suffix + final_archive_path_p.suffix
                    )
                shutil.move(str(original_arc_target_loc_p), str(final_archive_path_p))
                status_callback(f"Archived original '{original_arc_target_loc_p.name}' to '{final_archive_path_p.name}'.", STATUS_DEBUG)
                task_info["actual_archived_path_str"] = str(final_archive_path_p)
                original_secured_for_rebuild = True
            except Exception as e_archive:
                status_callback(f"Failed to archive original '{original_arc_target_loc_p.name}': {e_archive}. Skipping rebuild for this item.", STATUS_ERROR)
                failed_archive_or_setup_count += 1
                continue
        elif archived_original_arc_dest_p.exists() and archived_original_arc_dest_p.is_file():
            status_callback(f"Original '{original_arc_target_loc_p.name}' is already archived at '{archived_original_arc_dest_p.name}'.", STATUS_DEBUG)
            task_info["actual_archived_path_str"] = str(archived_original_arc_dest_p)
            original_secured_for_rebuild = True
        else:
            status_callback(f"CRITICAL: Original ARC '{original_arc_target_loc_p.name}' (or its expected archive) not found. This should not happen if parameters were read. Skipping.", STATUS_ERROR)
            failed_archive_or_setup_count += 1
            continue

        if original_secured_for_rebuild:
            tasks_ready_for_parallel_rebuild.append(task_info)

    if not tasks_ready_for_parallel_rebuild:
        status_callback(f"No tasks remaining after attempting to archive originals. Total initial tasks: {total_initial_tasks}, failed setup: {failed_archive_or_setup_count}.", STATUS_WARN)
        progress_callback(100 if total_initial_tasks > 0 else 0)
        return

    status_callback(f"Starting parallel rebuild for {len(tasks_ready_for_parallel_rebuild)} items...", STATUS_INFO)

    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        # Pass status_callback directly to _list_inject_worker
        future_to_task_info_map = {
            executor.submit(
                _list_inject_worker,
                task_info["edited_folder_str"],
                str(pathlib.Path(task_info["original_arc_target_location_str"]).parent), # output_rebuilt_dir_str
                key1, key2, status_callback, # status_callback_worker is now status_callback
                task_info["target_arc_filename_str"],
                task_info["original_arc_params"]["version"],
                task_info["original_arc_params"]["platform"],
                task_info["original_arc_params"]["bo_char"],
                False, # ARCC_SKIP: Explicitly pass False for target_is_arcc
                task_info["original_arc_params"]["file_order"],
                task_info["original_arc_params"]["entry_has_extended_names"],
                task_info["original_arc_params"]["original_file_metadata_map"]
            ): task_info for task_info in tasks_ready_for_parallel_rebuild
        }

        processed_in_parallel_count = 0
        completed_rebuilds_count = 0
        failed_rebuilds_count = 0
        for future in concurrent.futures.as_completed(future_to_task_info_map):
            task_info_completed = future_to_task_info_map[future]
            original_arc_final_loc_p = pathlib.Path(task_info_completed["original_arc_target_location_str"])
            edited_folder_p = pathlib.Path(task_info_completed["edited_folder_str"])
            actual_archived_original_path_str = task_info_completed.get("actual_archived_path_str")

            # Worker messages are now directly handled by the passed status_callback
            try:
                _, success = future.result()
                if success:
                    completed_rebuilds_count += 1
                    if edited_folder_p.exists() and edited_folder_p.is_dir():
                        archive_dest_edited_folder = original_backup_root / edited_folder_p.relative_to(source_path)
                        archive_dest_edited_folder.parent.mkdir(parents=True, exist_ok=True)
                        try:
                            final_archive_edited_folder_p = archive_dest_edited_folder
                            if final_archive_edited_folder_p.exists():
                                timestamp_suffix_folder = datetime.now().strftime("_processed_%Y%m%d%H%M%S%f")
                                final_archive_edited_folder_p = final_archive_edited_folder_p.with_name(
                                    final_archive_edited_folder_p.name + timestamp_suffix_folder
                                )
                            shutil.move(str(edited_folder_p), str(final_archive_edited_folder_p))
                            status_callback(f"Archived successfully processed folder '{edited_folder_p.name}' to '{final_archive_edited_folder_p.name}'.", STATUS_DEBUG)
                        except Exception as e_archive_folder:
                            status_callback(f"Warning: Failed to archive processed folder '{edited_folder_p.name}': {e_archive_folder}", STATUS_WARN)
                else:
                    failed_rebuilds_count += 1
                    status_callback(f"Rebuild failed for '{original_arc_final_loc_p.name}'. Attempting to restore original ARC.", STATUS_ERROR)
                    if actual_archived_original_path_str and os.path.isfile(actual_archived_original_path_str):
                        try:
                            if original_arc_final_loc_p.exists(): os.remove(str(original_arc_final_loc_p))
                            shutil.move(actual_archived_original_path_str, str(original_arc_final_loc_p))
                            status_callback(f"Restored original ARC '{original_arc_final_loc_p.name}' from backup '{os.path.basename(actual_archived_original_path_str)}'.", STATUS_INFO)
                        except Exception as e_restore:
                            status_callback(f"CRITICAL: Failed to restore original ARC '{original_arc_final_loc_p.name}' from '{actual_archived_original_path_str}': {e_restore}. Manual restoration may be needed.", STATUS_ERROR)
                    else:
                         status_callback(f"Warning: Cannot restore original ARC for '{original_arc_final_loc_p.name}', backup path '{actual_archived_original_path_str}' not found or invalid.", STATUS_WARN)

            except Exception as e_future_rebuild_main:
                failed_rebuilds_count += 1
                status_callback(f"Critical error during result processing for '{original_arc_final_loc_p.name}': {e_future_rebuild_main}", STATUS_ERROR)
                traceback.print_exc(file=sys.stderr)
                if actual_archived_original_path_str and os.path.isfile(actual_archived_original_path_str):
                    try:
                        if original_arc_final_loc_p.exists(): os.remove(str(original_arc_final_loc_p))
                        shutil.move(actual_archived_original_path_str, str(original_arc_final_loc_p))
                        status_callback(f"Attempted restore for '{original_arc_final_loc_p.name}' from '{actual_archived_original_path_str}' due to critical error.", STATUS_WARN)
                    except Exception as e_restore_critical:
                        status_callback(f"CRITICAL: Failed to restore '{original_arc_final_loc_p.name}' from '{actual_archived_original_path_str}' during critical error handling: {e_restore_critical}.", STATUS_ERROR)
                else:
                    status_callback(f"Warning: Cannot restore original for '{original_arc_final_loc_p.name}' (critical error), backup path '{actual_archived_original_path_str}' not found.", STATUS_WARN)

            processed_in_parallel_count +=1
            current_total_processed_for_progress = failed_archive_or_setup_count + processed_in_parallel_count
            progress_callback(current_total_processed_for_progress / total_initial_tasks * 100)


    duration = time.perf_counter() - start_time_overall
    total_failures_overall = failed_archive_or_setup_count + failed_rebuilds_count
    summary_msg = (f"Recursive in-place injection complete. Time: {duration:.2f}s. "
                   f"Successfully Rebuilt: {completed_rebuilds_count}/{len(tasks_ready_for_parallel_rebuild)}. "
                   f"Total Failures (Setup + Rebuild): {total_failures_overall} out of {total_initial_tasks} initial tasks.")
    final_status_level = STATUS_SUCCESS if total_failures_overall == 0 and completed_rebuilds_count > 0 else \
                         (STATUS_WARN if completed_rebuilds_count > 0 else \
                          (STATUS_ERROR if total_initial_tasks > 0 else STATUS_INFO) )
    if total_initial_tasks == 0: final_status_level = STATUS_INFO

    status_callback(summary_msg, final_status_level)


# --- GUI CODE ---
class ArcToolApp:
    def __init__(self, root):
        self.root = root;
        self.root.title("SaladSoftware ARC Tool");
        self.root.configure(bg=BG_COLOR);
        self.root.geometry("1220x900");
        self.default_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE);
        self.bold_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE, weight="bold");
        self.title_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE + 2, weight="bold")
        self.tab_label_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE - 2)
        self.queue = queue.Queue(); self.style = ttk.Style(); self.configure_styles()

        self.main_paned_window = ttk.PanedWindow(root, orient=tk.VERTICAL, style='TPanedwindow'); self.main_paned_window.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        self.top_pane_frame = ttk.Frame(self.main_paned_window, style='TFrame'); self.main_paned_window.add(self.top_pane_frame, weight=3)

        header_frame = ttk.Frame(self.top_pane_frame, style='TFrame');
        header_frame.pack(pady=5, padx=10, fill='x')
        ttk.Label(header_frame, text=f"~ Handburger's SaladSoftware MT Arc Tool ~ Version {VERSION}", style='TLabel', font=self.title_font).pack(side=tk.LEFT, anchor='w')
        self.help_button = ttk.Button(header_frame, text="Help", command=self.show_help, style='TButton'); self.help_button.pack(side=tk.RIGHT, padx=5, pady=5)

        attribution_text = "Uses Kuriimu1 and Kuriimu2 MT Arc Logic (GPL-3.0 License - legal permission to copy, distribute, and modify)"
        ttk.Label(self.top_pane_frame,
                  text=attribution_text,
                  style='TLabel',
                  font=self.tab_label_font).pack(anchor='w', pady=(0, 10), padx=10)

        self.notebook = ttk.Notebook(self.top_pane_frame, style='TNotebook')
        self.list_extract_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)
        self.list_inject_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)
        self.rec_extract_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)
        self.folder_inject_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)
        self.flatten_extract_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)
        self.internal_arc_extract_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)
        self.internal_arc_inject_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)

        self.notebook.add(self.list_extract_frame, text='Extract Arc Files')
        self.notebook.add(self.list_inject_frame, text='Inject Arc Folders')
        self.notebook.add(self.rec_extract_frame, text='Recursive Extract')
        self.notebook.add(self.folder_inject_frame, text='Recursive Inject (In-Place)')
        self.notebook.add(self.flatten_extract_frame, text='Extract All (Flatten)')
        self.notebook.add(self.internal_arc_extract_frame, text='Internal-ARC Extraction')
        self.notebook.add(self.internal_arc_inject_frame, text='Internal-ARC Injection')

        self.notebook.pack(pady=5, padx=10, expand=True, fill='both')

        self.create_list_extract_widgets(); self.create_list_inject_widgets(); self.create_recursive_extract_widgets(); self.create_folder_inject_widgets()
        self.create_flatten_extract_widgets()
        self.create_internal_arc_extract_widgets()
        self.create_internal_arc_inject_widgets()

        self.bottom_pane_frame = ttk.Frame(self.main_paned_window, style='TFrame');
        self.main_paned_window.add(self.bottom_pane_frame, weight=1)

        self.status_frame = ttk.Frame(self.bottom_pane_frame, style='Status.TFrame');
        self.status_frame.pack(pady=(0,0), padx=10, fill='both', expand=True, side=tk.TOP);
        self.status_frame.grid_rowconfigure(0, weight=1);
        self.status_frame.grid_columnconfigure(0, weight=1)

        self.status_text = scrolledtext.ScrolledText(self.status_frame, wrap=tk.WORD, font=self.default_font, bg=WIDGET_BG, fg=TEXT_COLOR, bd=1, relief='sunken', height=10);
        self.status_text.grid(row=0, column=0, sticky='nsew');
        self.status_text.configure(state='disabled')

        self.status_text.tag_config(STATUS_ERROR, foreground=STATUS_ERROR_FG);
        self.status_text.tag_config(STATUS_WARN, foreground=STATUS_WARN_FG);
        self.status_text.tag_config(STATUS_SUCCESS, foreground=STATUS_SUCCESS_FG);
        self.status_text.tag_config(STATUS_INFO, foreground=STATUS_INFO_FG);
        self.status_text.tag_config(STATUS_DEBUG, foreground=STATUS_DEBUG_FG)

        self.progress_var = tk.DoubleVar()
        self.progress_bar = ttk.Progressbar(self.bottom_pane_frame, orient='horizontal', length=100, mode='determinate', variable=self.progress_var, style='TProgressbar');
        self.progress_bar.pack(pady=10, padx=10, fill='x', side=tk.BOTTOM)

        self.current_arc_for_internal_view = None
        self.tree_item_data = {}

        self.current_arc_for_internal_inject_view = None
        self.internal_inject_tree_item_data = {}
        self.files_to_inject_map = {}

        if TkinterDnD:
            self.setup_drag_and_drop()
        else:
            self.add_status_message("tkinterdnd2 library not found. Drag and drop functionality will be disabled.", STATUS_WARN)

        self.check_queue()

    def configure_styles(self):
        self.style.theme_use('clam'); self.style.configure('.',background=BG_COLOR,foreground=TEXT_COLOR,font=self.default_font,fieldbackground=WIDGET_BG,troughcolor=BG_COLOR,borderwidth=1); self.style.map('.',foreground=[('disabled','#aaaaaa')])
        self.style.configure('TFrame',background=BG_COLOR); self.style.configure('Status.TFrame',background=BG_COLOR); self.style.configure('TPanedwindow', background=BG_COLOR)
        self.style.configure('TLabel',background=BG_COLOR,foreground=TEXT_COLOR,padding=5); self.style.configure('Header.TLabel',font=self.bold_font,foreground=TEXT_COLOR)
        self.style.configure('TButton',background=BUTTON_BG,foreground=BUTTON_FG,bordercolor=BUTTON_BORDER,focuscolor=HIGHLIGHT_BG,lightcolor=BUTTON_BG,darkcolor=BUTTON_BG,padding=(10, 6)); self.style.map('TButton',background=[('active',BUTTON_ACTIVE_BG),('pressed',BUTTON_PRESSED_BG)],foreground=[('active',BUTTON_FG),('pressed',BUTTON_FG)])
        self.style.configure('TEntry',fieldbackground=WIDGET_BG,foreground=INPUT_TEXT_COLOR,insertcolor=INPUT_TEXT_COLOR,bordercolor=BUTTON_BORDER); self.style.map('TEntry',selectbackground=[('focus',HIGHLIGHT_BG)],selectforeground=[('focus',HIGHLIGHT_TEXT)])
        listbox_opts = {'background': WIDGET_BG, 'foreground': TEXT_COLOR, 'selectbackground': HIGHLIGHT_BG, 'selectforeground': HIGHLIGHT_TEXT, 'font': self.default_font, 'bd': 1, 'relief': 'sunken', 'highlightthickness': 1, 'highlightbackground': BUTTON_BORDER, 'highlightcolor': HIGHLIGHT_BG}
        for opt, val in listbox_opts.items(): self.root.option_add(f'*Listbox*{opt}', val)
        self.style.configure('TNotebook',background=BG_COLOR,borderwidth=0);
        self.style.configure('TNotebook.Tab',background=HEADER_BG,foreground=HEADER_TEXT,padding=[10,5],font=self.tab_label_font,borderwidth=1);
        self.style.map('TNotebook.Tab',background=[('selected',HEADER_ACTIVE_BG)],foreground=[('selected',HEADER_ACTIVE_TEXT)],expand=[('selected',[1,1,1,1])])
        self.style.configure('TProgressbar',thickness=20,background=STATUS_SUCCESS_FG,troughcolor=WIDGET_BG); self.style.configure('Vertical.TScrollbar', background=BUTTON_BG, troughcolor=WIDGET_BG, bordercolor=BUTTON_BORDER, arrowcolor=TEXT_COLOR);
        self.style.map('Vertical.TScrollbar', background=[('active', BUTTON_ACTIVE_BG)])
        self.style.configure('Treeview', background=WIDGET_BG, fieldbackground=WIDGET_BG, foreground=TEXT_COLOR)
        self.style.map('Treeview', background=[('selected', HIGHLIGHT_BG)], foreground=[('selected', HIGHLIGHT_TEXT)])
        self.style.configure('Treeview.Heading', background=HEADER_BG, foreground=HEADER_TEXT, font=self.bold_font, padding=5)
        self.style.map('Treeview.Heading', background=[('active', HEADER_ACTIVE_BG)])
        self.style.configure('file_replaced', foreground='#FFA500', font=self.bold_font)


    def _create_dir_input(self, parent, label, row, var_name, pady_override=None):
        pady_val = (10,2) if pady_override is None else pady_override
        ttk.Label(parent, text=label, style='Header.TLabel').grid(row=row, column=0, sticky='w', padx=5, pady=pady_val);
        frame=ttk.Frame(parent); frame.grid(row=row+1, column=0, sticky='ew', padx=5, pady=(0,10)); frame.grid_columnconfigure(0, weight=1)
        v=tk.StringVar(); setattr(self, var_name, v); e=ttk.Entry(frame, textvariable=v, width=60); e.grid(row=0, column=0, sticky='ew', padx=(0,10));
        b=ttk.Button(frame, text="Browse...", command=lambda v_arg=v: self._select_directory(v_arg)); b.grid(row=0, column=1); return v

    def _create_file_output_input(self, parent, label, row, var_name, original_arc_filepath_var, pady_override=None):
        pady_val = (10,2) if pady_override is None else pady_override
        ttk.Label(parent, text=label, style='Header.TLabel').grid(row=row, column=0, sticky='w', padx=5, pady=pady_val);
        frame=ttk.Frame(parent); frame.grid(row=row+1, column=0, sticky='ew', padx=5, pady=(0,10)); frame.grid_columnconfigure(0, weight=1)
        v=tk.StringVar(); setattr(self, var_name, v); e=ttk.Entry(frame, textvariable=v, width=60); e.grid(row=0, column=0, sticky='ew', padx=(0,10));
        b=ttk.Button(frame, text="Browse...", command=lambda v_arg=v, orig_fp_var=original_arc_filepath_var: self._select_save_file_path(v_arg, orig_fp_var)); b.grid(row=0, column=1); return v


    def _select_directory(self, string_var):
        directory=filedialog.askdirectory(title="Select Directory");
        if directory: string_var.set(directory)

    def _select_save_file_path(self, string_var_to_set, original_arc_filepath_var):
        original_arc_path = original_arc_filepath_var.get()

        initial_dir = None
        initial_file = None
        if original_arc_path and os.path.isfile(original_arc_path):
            initial_dir = os.path.dirname(original_arc_path)
            initial_file = os.path.basename(original_arc_path)
        else:
            initial_dir = os.getcwd()
            initial_file = "rebuilt_arc.arc"

        filepath = filedialog.asksaveasfilename(
            title="Select Output Rebuilt ARC File",
            defaultextension=".arc",
            initialdir=initial_dir,
            initialfile=initial_file,
            filetypes=[("MT ARC files", "*.arc"), ("All files", "*.*")]
        )
        if filepath:
            string_var_to_set.set(filepath)


    def create_list_extract_widgets(self):
        frame=self.list_extract_frame; frame.grid_columnconfigure(0, weight=1); frame.grid_rowconfigure(1, weight=1); ttk.Label(frame, text="Input ARC Files:", style='Header.TLabel').grid(row=0, column=0, columnspan=3, sticky='w', pady=(10,5))
        lb_frame = ttk.Frame(frame); lb_frame.grid(row=1, column=0, columnspan=2, padx=5, pady=5, sticky='nsew'); lb_frame.grid_rowconfigure(0, weight=1); lb_frame.grid_columnconfigure(0, weight=1)
        self.list_extract_listbox=tk.Listbox(lb_frame, width=80, height=10, selectmode=tk.EXTENDED); self.list_extract_listbox.grid(row=0, column=0, sticky='nsew'); sb=ttk.Scrollbar(lb_frame, orient='vertical', command=self.list_extract_listbox.yview, style='Vertical.TScrollbar'); sb.grid(row=0, column=1, sticky='nsw'); self.list_extract_listbox.config(yscrollcommand=sb.set)
        bf=ttk.Frame(frame); bf.grid(row=2, column=0, columnspan=2, sticky='ew', padx=5, pady=5); ttk.Button(bf, text="Select Files", command=self.select_list_extract_files).pack(side=tk.LEFT, padx=(0,10), pady=5); ttk.Button(bf, text="Clear List", command=lambda: self.list_extract_listbox.delete(0, tk.END)).pack(side=tk.LEFT, padx=(0,10), pady=5)
        ttk.Label(frame, text="Output: Folders named <filename>_arc created next to each input .arc file.", style='TLabel').grid(row=3, column=0, columnspan=3, sticky='w', padx=5, pady=(10,5)); ttk.Button(frame, text="Start Extraction", command=self.start_list_extraction).grid(row=4, column=0, columnspan=3, pady=(10,10))

    def create_list_inject_widgets(self):
        frame=self.list_inject_frame; frame.grid_columnconfigure(0, weight=1); frame.grid_rowconfigure(1, weight=1); ttk.Label(frame, text="Input Source Folders:", style='Header.TLabel').grid(row=0, column=0, columnspan=3, sticky='w', pady=(10,5))
        lb_frame = ttk.Frame(frame); lb_frame.grid(row=1, column=0, columnspan=2, padx=5, pady=5, sticky='nsew'); lb_frame.grid_rowconfigure(0, weight=1); lb_frame.grid_columnconfigure(0, weight=1)
        self.list_inject_listbox=tk.Listbox(lb_frame, width=80, height=10, selectmode=tk.EXTENDED); self.list_inject_listbox.grid(row=0, column=0, sticky='nsew'); sb=ttk.Scrollbar(lb_frame, orient='vertical', command=self.list_inject_listbox.yview, style='Vertical.TScrollbar'); sb.grid(row=0, column=1, sticky='nsw'); self.list_inject_listbox.config(yscrollcommand=sb.set)
        bf=ttk.Frame(frame); bf.grid(row=2, column=0, columnspan=2, sticky='ew', padx=5, pady=5); ttk.Button(bf, text="Add Folder", command=self.select_list_inject_folders).pack(side=tk.LEFT, padx=(0,10), pady=5); ttk.Button(bf, text="Clear List", command=lambda: self.list_inject_listbox.delete(0, tk.END)).pack(side=tk.LEFT, padx=(0,10), pady=5)
        self._create_dir_input(frame, "Output Rebuilt ARC Directory:", 3, "list_inject_output_var"); ttk.Button(frame, text="Start Rebuild", command=self.start_list_injection).grid(row=5, column=0, columnspan=3, pady=(10,10))

    def create_recursive_extract_widgets(self):
        frame=self.rec_extract_frame; frame.grid_columnconfigure(0, weight=1);
        self._create_dir_input(frame, "Source ARC Directory (Recursive):", 0, "rec_extract_source_var", pady_override=(10,5))
        ttk.Label(frame, text="Output: Folders named <filename>_arc created next to each found .arc file.", style='TLabel').grid(row=2, column=0, sticky='w', padx=5, pady=(10,5)); ttk.Button(frame, text="Start Recursive Extraction", command=self.start_recursive_extraction).grid(row=3, column=0, pady=(10,10))

    def create_folder_inject_widgets(self):
        frame=self.folder_inject_frame; frame.grid_columnconfigure(0, weight=1); self._create_dir_input(frame, "Source Directory (contains .arc files and *_arc folders):", 0, "folder_inject_source_dir_var", pady_override=(10,5))
        info_text = ("Rebuilds .arc files found alongside corresponding *_arc folders.\nOriginals moved to 'original_arc_backups' subfolder. New ARCs match original format & file order.");
        ttk.Label(frame, text=info_text, style='TLabel', justify=tk.LEFT).grid(row=2, column=0, sticky='w', padx=5, pady=(10,5))
        ttk.Button(frame, text="Start In-Place Rebuild (Retains Params)", command=self.start_folder_injection).grid(row=3, column=0, pady=(10,10))

    def create_flatten_extract_widgets(self):
        frame = self.flatten_extract_frame; frame.grid_columnconfigure(0, weight=1)
        self._create_dir_input(frame, "Source ARC Directory (Recursive):", 0, "flatten_extract_source_var", pady_override=(10,5))
        self._create_dir_input(frame, "Output Directory (for all flattened files):", 2, "flatten_extract_output_var")
        ttk.Label(frame, text="Extracts all files from all ARCs into a single output directory.\nFilenames prefixed with ARC name (e.g., arc1_image.tex).", style='TLabel', justify=tk.LEFT).grid(row=4, column=0, sticky='w', padx=5, pady=(10,5))
        ttk.Button(frame, text="Start Flattened Extraction", command=self.start_flatten_extraction).grid(row=5, column=0, pady=(10,10))

    def create_internal_arc_extract_widgets(self):
        frame = self.internal_arc_extract_frame
        frame.grid_columnconfigure(0, weight=1)
        frame.grid_rowconfigure(1, weight=1)

        input_arc_frame = ttk.Frame(frame); input_arc_frame.grid(row=0, column=0, sticky='ew', padx=5, pady=(0,2))
        input_arc_frame.grid_columnconfigure(0, weight=1)
        ttk.Label(input_arc_frame, text="Select ARC File to Preview:", style='Header.TLabel').pack(side=tk.LEFT, anchor='w')
        self.internal_arc_filepath_var = tk.StringVar()
        ttk.Entry(input_arc_frame, textvariable=self.internal_arc_filepath_var, width=90).pack(side=tk.LEFT, expand=True, fill='x', padx=10)
        ttk.Button(input_arc_frame, text="Browse ARC...", command=self.select_internal_arc_file).pack(side=tk.LEFT)

        tree_frame = ttk.Frame(frame);
        tree_frame.grid(row=1, column=0, sticky='nsew', pady=(2,0))
        tree_frame.grid_rowconfigure(0, minsize=250,  weight=1);
        tree_frame.grid_columnconfigure(0, weight=1, minsize=200)

        self.internal_arc_tree = ttk.Treeview(tree_frame, columns=("fullpath", "type", "size"), displaycolumns=(), show="tree")
        self.internal_arc_tree.heading("#0", text="Name", anchor='w')
        self.internal_arc_tree.column("#0", width=450, stretch=tk.YES)

        self.internal_arc_tree.column("fullpath", width=0, stretch=tk.NO)
        self.internal_arc_tree.column("type", width=0, stretch=tk.NO)
        self.internal_arc_tree.column("size", width=0, stretch=tk.NO)

        tree_ysb = ttk.Scrollbar(tree_frame, orient='vertical', command=self.internal_arc_tree.yview, style='Vertical.TScrollbar')
        self.internal_arc_tree.configure(yscrollcommand=tree_ysb.set)

        self.internal_arc_tree.grid(row=0, column=0, sticky='nsew')
        tree_ysb.grid(row=0, column=1, sticky='ns')

        self.internal_arc_tree.tag_configure('file_checked_color', foreground='#00f7ff')
        self.internal_arc_tree.tag_configure('folder_checked_color', foreground='#00f7ff')
        self.internal_arc_tree.tag_configure('file_unchecked_color', foreground=TEXT_COLOR)
        self.internal_arc_tree.tag_configure('folder_unchecked_color', foreground='#FFDEAD')
        self.internal_arc_tree.bind("<ButtonRelease-1>", self.on_tree_item_toggle_check)

        output_frame = ttk.Frame(frame);
        output_frame.grid(row=2, column=0, sticky='ews', pady=(2,0))
        self._create_dir_input(output_frame, "Output Directory for Selected Items:", 0, "internal_extract_output_var")
        ttk.Button(frame, text="Extract Selected Items", command=self.start_internal_arc_extraction).grid(row=3, column=0, pady=(10,10), padx=5)

    def create_internal_arc_inject_widgets(self):
        frame = self.internal_arc_inject_frame
        frame.grid_columnconfigure(0, weight=1)
        frame.grid_rowconfigure(1, weight=1)

        input_arc_frame = ttk.Frame(frame); input_arc_frame.grid(row=0, column=0, sticky='ew', padx=5, pady=(0,2))
        input_arc_frame.grid_columnconfigure(0, weight=1)
        ttk.Label(input_arc_frame, text="Select ARC File to Inject Into:", style='Header.TLabel').pack(side=tk.LEFT, anchor='w')
        self.internal_inject_filepath_var = tk.StringVar()
        ttk.Entry(input_arc_frame, textvariable=self.internal_inject_filepath_var, width=90).pack(side=tk.LEFT, expand=True, fill='x', padx=10)
        ttk.Button(input_arc_frame, text="Browse ARC...", command=self.select_internal_inject_arc_file).pack(side=tk.LEFT)

        tree_and_buttons_frame = ttk.Frame(frame)
        tree_and_buttons_frame.grid(row=1, column=0, sticky='nsew', pady=(2,0))
        tree_and_buttons_frame.grid_rowconfigure(0, weight=1)
        tree_and_buttons_frame.grid_columnconfigure(0, weight=1)

        self.internal_inject_tree = ttk.Treeview(tree_and_buttons_frame, columns=("fullpath", "type", "size"), displaycolumns=(), show="tree")
        self.internal_inject_tree.heading("#0", text="Name", anchor='w')
        self.internal_inject_tree.column("#0", width=450, stretch=tk.YES)

        self.internal_inject_tree.column("fullpath", width=0, stretch=tk.NO)
        self.internal_inject_tree.column("type", width=0, stretch=tk.NO)
        self.internal_inject_tree.column("size", width=0, stretch=tk.NO)

        tree_ysb = ttk.Scrollbar(tree_and_buttons_frame, orient='vertical', command=self.internal_inject_tree.yview, style='Vertical.TScrollbar')
        self.internal_inject_tree.configure(yscrollcommand=tree_ysb.set)

        self.internal_inject_tree.grid(row=0, column=0, sticky='nsew')
        tree_ysb.grid(row=0, column=1, sticky='ns')

        self.internal_inject_tree.bind("<<TreeviewSelect>>", self.on_internal_inject_tree_selection_changed)

        buttons_frame = ttk.Frame(tree_and_buttons_frame);
        buttons_frame.grid(row=0, column=2, sticky='n', padx=(10,0))
        self.replace_file_button = ttk.Button(buttons_frame, text="Replace Selected File...", command=self.replace_selected_internal_file, state=tk.DISABLED)
        self.replace_file_button.pack(pady=(5,5), fill='x')
        self.clear_injection_map_button = ttk.Button(buttons_frame, text="Clear Replacements", command=self.clear_internal_inject_map)
        self.clear_injection_map_button.pack(pady=(5,5), fill='x')

        output_frame = ttk.Frame(frame);
        output_frame.grid(row=2, column=0, sticky='ews', pady=(2,0))
        self._create_file_output_input(output_frame, "Output Rebuilt ARC File (New Name/Location):", 0, "internal_inject_output_var", self.internal_inject_filepath_var)

        info_text = "Select an existing ARC, then pick files to replace. Retains original ARC structure and metadata."
        ttk.Label(frame, text=info_text, style='TLabel', justify=tk.LEFT).grid(row=3, column=0, sticky='w', padx=5, pady=(10,5))
        ttk.Button(frame, text="Start Injection", command=self.start_internal_arc_injection).grid(row=4, column=0, pady=(10,10), padx=5)


    def setup_drag_and_drop(self):
        self.list_extract_listbox.drop_target_register(DND_FILES)
        self.list_extract_listbox.dnd_bind('<<Drop>>', self.handle_drop_list_extract)

        self.flatten_extract_frame.drop_target_register(DND_FILES)
        self.flatten_extract_frame.dnd_bind('<<Drop>>', self.handle_drop_flatten_extract)

        self.internal_arc_extract_frame.drop_target_register(DND_FILES)
        self.internal_arc_extract_frame.dnd_bind('<<Drop>>', self.handle_drop_internal_arc_extract)

        self.internal_arc_inject_frame.drop_target_register(DND_FILES)
        self.internal_arc_inject_frame.dnd_bind('<<Drop>>', self.handle_drop_internal_arc_inject)
        self.add_status_message("Drag and drop initialized for relevant tabs.", STATUS_DEBUG)

    def _parse_dropped_files(self, event_data_str):
        try:
            filepaths = self.root.tk.splitlist(event_data_str)
            return [pathlib.Path(fp) for fp in filepaths]
        except Exception as e:
            self.add_status_message(f"Error parsing dropped file list: {e}", STATUS_ERROR)
            return []

    def handle_drop_list_extract(self, event):
        try:
            filepaths = self._parse_dropped_files(event.data)
            current_items = set(self.list_extract_listbox.get(0, tk.END))
            new_files_added_count = 0
            for fp in filepaths:
                if fp.is_file() and fp.suffix.lower() == '.arc':
                    fp_str = str(fp)
                    if fp_str not in current_items:
                        self.list_extract_listbox.insert(tk.END, fp_str)
                        new_files_added_count += 1

            if new_files_added_count > 0:
                self.add_status_message(f"D&D: Added {new_files_added_count} ARC file(s) to 'Extract Arc Files' list.", STATUS_INFO)
            elif not any(fp.suffix.lower() == '.arc' for fp in filepaths):
                 self.add_status_message("D&D: No .arc files found in dropped items for 'Extract Arc Files'.", STATUS_WARN)
            self.notebook.select(self.list_extract_frame)
        except Exception as e:
            self.add_status_message(f"Error during D&D for List Extract: {e}", STATUS_ERROR)
            traceback.print_exc(file=sys.stderr)

    def handle_drop_flatten_extract(self, event):
        try:
            filepaths = self._parse_dropped_files(event.data)
            dropped_arc_file_path = None
            for fp in filepaths:
                if fp.is_file() and fp.suffix.lower() == '.arc':
                    dropped_arc_file_path = str(fp)
                    break

            if not dropped_arc_file_path:
                self.add_status_message("D&D: No .arc file dropped or found for 'Extract All (Flatten)'.", STATUS_WARN)
                return

            output_dir = self.flatten_extract_output_var.get()
            if not output_dir:
                messagebox.showwarning("Output Missing", "Please select an output directory for the flattened files before dropping an ARC.")
                self.add_status_message("D&D Flatten: Output directory not set.", STATUS_ERROR)
                return

            if not pathlib.Path(output_dir).is_dir():
                try:
                    pathlib.Path(output_dir).mkdir(parents=True, exist_ok=True)
                except Exception as e_mkdir:
                    messagebox.showerror("Output Error", f"Cannot create output directory '{output_dir}': {e_mkdir}")
                    self.add_status_message(f"D&D Flatten: Error creating output dir: {e_mkdir}", STATUS_ERROR)
                    return

            self.add_status_message(f"D&D Flatten: Processing '{os.path.basename(dropped_arc_file_path)}' into '{output_dir}'.", STATUS_INFO)
            self._run_task(run_batch_parallel,
                           args_tuple=(_flatten_extract_worker, [dropped_arc_file_path], output_dir))
            self.notebook.select(self.flatten_extract_frame)
        except Exception as e:
            self.add_status_message(f"Error during D&D for Flatten Extract: {e}", STATUS_ERROR)
            traceback.print_exc(file=sys.stderr)

    def handle_drop_internal_arc_extract(self, event):
        try:
            filepaths = self._parse_dropped_files(event.data)
            dropped_arc_file_path = None
            for fp in filepaths:
                if fp.is_file() and fp.suffix.lower() == '.arc':
                    dropped_arc_file_path = str(fp)
                    break

            if not dropped_arc_file_path:
                self.add_status_message("D&D: No .arc file dropped or found for 'Internal-ARC Extraction'.", STATUS_WARN)
                return

            self.internal_arc_filepath_var.set(dropped_arc_file_path)
            self.load_arc_into_treeview(dropped_arc_file_path)
            self.add_status_message(f"D&D: Loaded '{os.path.basename(dropped_arc_file_path)}' for internal preview.", STATUS_INFO)
            self.notebook.select(self.internal_arc_extract_frame)
        except Exception as e:
            self.add_status_message(f"Error during D&D for Internal ARC: {e}", STATUS_ERROR)
            traceback.print_exc(file=sys.stderr)

    def handle_drop_internal_arc_inject(self, event):
        try:
            filepaths = self._parse_dropped_files(event.data)
            dropped_arc_file_path = None
            for fp in filepaths:
                if fp.is_file() and fp.suffix.lower() == '.arc':
                    dropped_arc_file_path = str(fp)
                    break

            if not dropped_arc_file_path:
                self.add_status_message("D&D: No .arc file dropped or found for 'Internal-ARC Injection'.", STATUS_WARN)
                return

            self.internal_inject_filepath_var.set(dropped_arc_file_path)
            self.load_arc_into_inject_treeview(dropped_arc_file_path)
            self.add_status_message(f"D&D: Loaded '{os.path.basename(dropped_arc_file_path)}' for internal injection.", STATUS_INFO)
            self.notebook.select(self.internal_arc_inject_frame)
        except Exception as e:
            self.add_status_message(f"Error during D&D for Internal ARC Injection: {e}", STATUS_ERROR)
            traceback.print_exc(file=sys.stderr)

    def select_list_extract_files(self):
        files=filedialog.askopenfilenames(title="Select ARC Files", filetypes=[("MT ARC","*.arc"),("All Files","*.*")]);
        if files: current_items = set(self.list_extract_listbox.get(0, tk.END)); new_files_added = 0
        for f in files:
            if f not in current_items: self.list_extract_listbox.insert(tk.END, f); new_files_added +=1
        if new_files_added: self.add_status_message(f"Added {new_files_added} file(s) to extraction list.", STATUS_INFO)

    def select_list_inject_folders(self):
        directory = filedialog.askdirectory(title="Select Source Folder to Add to List")
        if directory:
            current_items = set(self.list_inject_listbox.get(0, tk.END))
            if directory not in current_items:
                self.list_inject_listbox.insert(tk.END, directory)
                self.add_status_message(f"Added folder '{os.path.basename(directory)}' to injection list.", STATUS_INFO)
            else:
                self.add_status_message(f"Folder '{os.path.basename(directory)}' is already in the list.", STATUS_WARN)

    def select_internal_arc_file(self):
        filepath = filedialog.askopenfilename(title="Select ARC File", filetypes=[("MT ARC","*.arc"),("All Files","*.*")])
        if filepath:
            self.internal_arc_filepath_var.set(filepath)
            self.load_arc_into_treeview(filepath)

    def select_internal_inject_arc_file(self):
        filepath = filedialog.askopenfilename(title="Select ARC File to Inject Into", filetypes=[("MT ARC","*.arc"),("All Files","*.*")])
        if filepath:
            self.internal_inject_filepath_var.set(filepath)
            self.load_arc_into_inject_treeview(filepath)

    def load_arc_into_treeview(self, filepath):
        self.internal_arc_tree.delete(*self.internal_arc_tree.get_children())
        self.tree_item_data.clear()
        self.current_arc_for_internal_view = MTArc()
        try:
            # Pass self.queue_status for MTArc.load, it will adapt.
            self.current_arc_for_internal_view.load(filepath, status_queue_or_callback=self.queue_status)
            self.add_status_message(f"Loaded ARC '{os.path.basename(filepath)}' with {len(self.current_arc_for_internal_view.files)} entries.", STATUS_INFO)

            folder_iids = {}
            sorted_files = sorted(self.current_arc_for_internal_view.files, key=lambda fi: fi['full_filename'].replace('\\', '/'))

            for file_info in sorted_files:
                full_path = file_info['full_filename'].replace('\\', '/')
                parts = full_path.split('/')
                current_parent_iid_for_insert = ''
                path_accumulator = []

                for i, part_name in enumerate(parts[:-1]):
                    path_accumulator.append(part_name)
                    current_folder_path_str = "/".join(path_accumulator)

                    if current_folder_path_str not in folder_iids:
                        iid = self.internal_arc_tree.insert(
                            current_parent_iid_for_insert,
                            'end',
                            text=f"{CHECK_UNCHECKED} {part_name}",
                            values=(current_folder_path_str, "folder", 0),
                            tags=('folder_unchecked_color',),
                            open=False
                        )
                        folder_iids[current_folder_path_str] = iid
                        self.tree_item_data[iid] = {
                            'path': current_folder_path_str, 'is_folder': True,
                            'checked_state': False, 'file_info': None,
                            'display_name': part_name
                        }
                        current_parent_iid_for_insert = iid
                    else:
                        current_parent_iid_for_insert = folder_iids[current_folder_path_str]

                file_name_only = parts[-1]
                file_iid = self.internal_arc_tree.insert(
                    current_parent_iid_for_insert,
                    'end',
                    text=f"{CHECK_UNCHECKED} {file_name_only}",
                    values=(full_path, "file", file_info.get('calculated_uncompressed_size',0)),
                    tags=('file_unchecked_color',),
                    open=False
                )
                self.tree_item_data[file_iid] = {
                    'path': full_path, 'is_folder': False,
                    'checked_state': False, 'file_info': file_info,
                    'display_name': file_name_only
                }
        except ARCCSkippedError as e:
            # Status already sent by MTArc.load via queue_status
            if self.current_arc_for_internal_view: self.current_arc_for_internal_view.close()
            self.current_arc_for_internal_view = None
            return
        except Exception as e:
            self.add_status_message(f"Error loading ARC for preview: {e}", STATUS_ERROR)
            traceback.print_exc(file=sys.stderr)
            if self.current_arc_for_internal_view: self.current_arc_for_internal_view.close()
            self.current_arc_for_internal_view = None

    def load_arc_into_inject_treeview(self, filepath):
        self.internal_inject_tree.delete(*self.internal_inject_tree.get_children())
        self.internal_inject_tree_item_data.clear()
        self.files_to_inject_map.clear()

        self.current_arc_for_internal_inject_view = MTArc()
        try:
            self.current_arc_for_internal_inject_view.load(filepath, status_queue_or_callback=self.queue_status)
            self.add_status_message(f"Loaded ARC '{os.path.basename(filepath)}' for injection preview with {len(self.current_arc_for_internal_inject_view.files)} entries.", STATUS_INFO)

            folder_iids = {}
            sorted_files = sorted(self.current_arc_for_internal_inject_view.files, key=lambda fi: fi['full_filename'].replace('\\', '/'))

            for file_info in sorted_files:
                full_path = file_info['full_filename'].replace('\\', '/')
                parts = full_path.split('/')
                current_parent_iid_for_insert = ''
                path_accumulator = []

                for i, part_name in enumerate(parts[:-1]):
                    path_accumulator.append(part_name)
                    current_folder_path_str = "/".join(path_accumulator)

                    if current_folder_path_str not in folder_iids:
                        iid = self.internal_inject_tree.insert(
                            current_parent_iid_for_insert,
                            'end',
                            text=part_name,
                            values=(current_folder_path_str, "folder", 0),
                            tags=('folder_unchecked_color',),
                            open=False
                        )
                        folder_iids[current_folder_path_str] = iid
                        self.internal_inject_tree_item_data[iid] = {
                            'path': current_folder_path_str, 'is_folder': True,
                            'file_info': None, 'display_name': part_name
                        }
                        current_parent_iid_for_insert = iid
                    else:
                        current_parent_iid_for_insert = folder_iids[current_folder_path_str]

                file_name_only = parts[-1]
                file_iid = self.internal_inject_tree.insert(
                    current_parent_iid_for_insert,
                    'end',
                    text=file_name_only,
                    values=(full_path, "file", file_info.get('calculated_uncompressed_size',0)),
                    tags=('file_unchecked_color',),
                    open=False
                )
                self.internal_inject_tree_item_data[file_iid] = {
                    'path': full_path, 'is_folder': False,
                    'file_info': file_info, 'display_name': file_name_only
                }
            self.replace_file_button.config(state=tk.DISABLED)
        except ARCCSkippedError as e:
            if self.current_arc_for_internal_inject_view: self.current_arc_for_internal_inject_view.close()
            self.current_arc_for_internal_inject_view = None
            self.replace_file_button.config(state=tk.DISABLED)
            return
        except Exception as e:
            self.add_status_message(f"Error loading ARC for injection: {e}", STATUS_ERROR)
            traceback.print_exc(file=sys.stderr)
            if self.current_arc_for_internal_inject_view: self.current_arc_for_internal_inject_view.close()
            self.current_arc_for_internal_inject_view = None

    def on_internal_inject_tree_selection_changed(self, event):
        selected_items = self.internal_inject_tree.selection()
        if len(selected_items) == 1:
            item_iid = selected_items[0]
            item_data = self.internal_inject_tree_item_data.get(item_iid)
            if item_data and not item_data['is_folder']:
                self.replace_file_button.config(state=tk.NORMAL)
            else:
                self.replace_file_button.config(state=tk.DISABLED)
        else:
            self.replace_file_button.config(state=tk.DISABLED)

    def replace_selected_internal_file(self):
        selected_items = self.internal_inject_tree.selection()
        if not selected_items or len(selected_items) != 1: return

        item_iid = selected_items[0]
        item_data = self.internal_inject_tree_item_data.get(item_iid)

        if not item_data or item_data['is_folder']:
            messagebox.showwarning("Invalid Selection", "Please select a single file (not a folder) to replace.")
            return

        internal_arc_path = item_data['path']
        original_display_name = item_data['display_name']

        new_disk_file_path = filedialog.askopenfilename(
            title=f"Select replacement for '{original_display_name}'",
            filetypes=[("All Files", "*.*")]
        )
        if new_disk_file_path:
            self.files_to_inject_map[internal_arc_path.lower().replace('\\', '/')] = new_disk_file_path

            new_text = f"{original_display_name} (REPLACED by {os.path.basename(new_disk_file_path)})"
            self.internal_inject_tree.item(item_iid, text=new_text, tags=('file_replaced',))
            self.add_status_message(f"Marked '{original_display_name}' for replacement with '{os.path.basename(new_disk_file_path)}'.", STATUS_INFO)

    def clear_internal_inject_map(self):
        if messagebox.askyesno("Clear Replacements", "Are you sure you want to clear all marked file replacements?"):
            self.files_to_inject_map.clear()
            self.add_status_message("All pending file replacements have been cleared.", STATUS_INFO)
            if self.internal_inject_filepath_var.get():
                self.load_arc_into_inject_treeview(self.internal_inject_filepath_var.get())


    def on_tree_item_toggle_check(self, event):
        item_iid = self.internal_arc_tree.identify_row(event.y)
        if not item_iid:
            return

        element_clicked = self.internal_arc_tree.identify_element(event.x, event.y)
        element_str_lower = str(element_clicked).lower()
        if "indicator" in element_str_lower or \
           "expander" in element_str_lower or \
           "arrow" in element_str_lower:
            return

        if item_iid not in self.tree_item_data:
            return

        current_data = self.tree_item_data[item_iid]
        new_state = not current_data['checked_state']
        self._set_tree_item_checked_state(item_iid, new_state, recursive=True, update_parent=True)

    def _set_tree_item_checked_state(self, item_iid, checked: bool, recursive: bool, update_parent: bool):
        if item_iid not in self.tree_item_data:
            return

        current_data = self.tree_item_data[item_iid]

        original_display_name_key = 'display_name'
        if original_display_name_key not in current_data:
            current_text_from_tree = self.internal_arc_tree.item(item_iid, 'text')
            if current_text_from_tree:
                parts = current_text_from_tree.split(" ", 1)
                if len(parts) > 1:
                    current_data[original_display_name_key] = parts[1]
                else:
                    current_data[original_display_name_key] = current_text_from_tree
            else:
                current_data[original_display_name_key] = "ErrorName"

        current_data['checked_state'] = checked
        item_display_name = current_data.get(original_display_name_key, "Unknown")

        checkbox_char = CHECK_CHECKED if checked else CHECK_UNCHECKED
        new_text = f"{checkbox_char} {item_display_name}"
        self.internal_arc_tree.item(item_iid, text=new_text)

        tag_to_apply = ""
        is_folder = current_data['is_folder']

        if checked:
            tag_to_apply = 'folder_checked_color' if is_folder else 'file_checked_color'
        else:
            tag_to_apply = 'folder_unchecked_color' if is_folder else 'file_unchecked_color'

        self.internal_arc_tree.item(item_iid, tags=(tag_to_apply,))

        if recursive and is_folder:
            for child_iid in self.internal_arc_tree.get_children(item_iid):
                self._set_tree_item_checked_state(child_iid, checked, recursive=True, update_parent=False)

        if update_parent:
            parent_iid = self.internal_arc_tree.parent(item_iid)
            if parent_iid:
                self._update_parent_checkbox_state(parent_iid)

    def _update_parent_checkbox_state(self, parent_iid):
        if not parent_iid or parent_iid not in self.tree_item_data:
            return

        children_iids = self.internal_arc_tree.get_children(parent_iid)
        parent_data = self.tree_item_data[parent_iid]
        current_parent_checked_state = parent_data['checked_state']

        if not children_iids:
            return

        all_children_now_fully_checked = True
        any_child_checked = False

        for child_iid in children_iids:
            if child_iid in self.tree_item_data:
                child_data = self.tree_item_data[child_iid]
                if not child_data['checked_state']:
                    all_children_now_fully_checked = False
                if child_data['checked_state']:
                    any_child_checked = True
            else:
                all_children_now_fully_checked = False

        new_parent_checked_state = current_parent_checked_state

        if current_parent_checked_state:
            if not all_children_now_fully_checked:
                new_parent_checked_state = False
        else:
            pass

        if current_parent_checked_state != new_parent_checked_state:
            self._set_tree_item_checked_state(parent_iid, new_parent_checked_state, recursive=False, update_parent=True)

    def _run_task(self, target_func, args_tuple=(), kwargs_dict=None,
                  original_arc_params_list=None,
                  target_is_arcc_list=None,
                  original_file_orders_list=None,
                  original_file_metadata_map_list=None):
        k1, k2 = None, None

        if kwargs_dict is None: kwargs_dict = {}

        kwargs_dict['progress_callback'] = self.update_progress
        kwargs_dict['status_callback'] = self.queue_status # For GUI, this puts onto app.queue
        kwargs_dict['key1'] = k1
        kwargs_dict['key2'] = k2

        if target_func == run_batch_parallel:
            kwargs_dict['original_arc_params_list'] = original_arc_params_list
            kwargs_dict['target_is_arcc_list'] = target_is_arcc_list
            kwargs_dict['original_file_orders_list'] = original_file_orders_list
            kwargs_dict['original_file_metadata_map_list'] = original_file_metadata_map_list

        self.progress_var.set(0)

        task_name_display = target_func.__name__.replace('_', ' ').replace('run batch parallel', '').strip().title()
        if args_tuple and hasattr(args_tuple[0], '__name__'):
            worker_name = args_tuple[0].__name__
            if worker_name == '_list_extract_worker': task_name_display = "List Extraction"
            elif worker_name == '_list_inject_worker': task_name_display = "List Injection"
            elif worker_name == '_flatten_extract_worker': task_name_display = "Flattened Extraction"
        elif target_func == recursive_batch_extract: task_name_display = "Recursive Extraction"
        elif target_func == folder_batch_inject: task_name_display = "Folder In-Place Injection"
        elif target_func == self._perform_internal_arc_extraction_thread: task_name_display = "Internal ARC Extraction"
        elif target_func == self._perform_internal_arc_injection_thread: task_name_display = "Internal ARC Injection"


        self.add_status_message(f"Starting {task_name_display} task...", STATUS_INFO);
        thread = threading.Thread(target=target_func, args=args_tuple, kwargs=kwargs_dict, daemon=True);
        thread.start()

    def start_list_extraction(self):
        items = self.list_extract_listbox.get(0, tk.END);
        if not items: messagebox.showwarning("Input Missing","Please select one or more ARC files for extraction."); return;
        self._run_task(run_batch_parallel, (_list_extract_worker, items, None))

    def start_list_injection(self):
        items_folder_paths_str = self.list_inject_listbox.get(0, tk.END) # Corrected from list_extract_listbox
        output_rebuilt_dir_str = self.list_inject_output_var.get()

        if not items_folder_paths_str:
            messagebox.showwarning("Input Missing", "Please add one or more source folders to rebuild.")
            return
        if not output_rebuilt_dir_str:
            messagebox.showwarning("Output Missing", "Please select an output directory for the rebuilt ARC files.")
            return

        for folder_path_str_val in items_folder_paths_str:
            if not os.path.isdir(folder_path_str_val):
                messagebox.showerror("Input Invalid", f"Source folder not found or is not a directory: {folder_path_str_val}")
                return

        all_original_arc_params_dicts = []
        all_target_is_arcc_flags = []
        all_original_file_orders = []
        all_original_file_metadata_maps = []

        self.add_status_message("Preparing parameters for List Injection...", STATUS_INFO)

        default_params_values = {
            "version": DEFAULT_VERSION,
            "platform": DEFAULT_PLATFORM,
            "bo_char": DEFAULT_BYTE_ORDER_CHAR,
            "file_order": None,
            "entry_has_extended_names": False,
            "original_file_metadata_map": {}
        }

        for folder_path_str_item in items_folder_paths_str:
            folder_path_obj_item = pathlib.Path(folder_path_str_item)
            current_params_for_item = default_params_values.copy()

            if folder_path_obj_item.name.endswith("_arc"):
                arc_basename_item = folder_path_obj_item.name[:-4]
                potential_original_arc_path_item = folder_path_obj_item.parent / (arc_basename_item + ".arc")

                if potential_original_arc_path_item.is_file():
                    self.add_status_message(f"Found potential original ARC '{potential_original_arc_path_item.name}' for folder '{folder_path_obj_item.name}'. Attempting to load parameters...", STATUS_DEBUG)
                    temp_arc_loader_item = MTArc()
                    try:
                        # Pass self.queue_status (which puts on app.queue)
                        temp_arc_loader_item.load(str(potential_original_arc_path_item), status_queue_or_callback=self.queue_status)

                        if temp_arc_loader_item.arc_header:
                            file_meta_map_item = {}
                            if temp_arc_loader_item.files:
                                for fi_orig_item in temp_arc_loader_item.files:
                                    norm_path_key_item = fi_orig_item['full_filename'].lower().replace('\\', '/')
                                    file_meta_map_item[norm_path_key_item] = {
                                        'is_compressed': fi_orig_item['is_compressed'],
                                        'uncompressed_size_raw': fi_orig_item['uncompressed_size_raw']
                                    }

                            current_params_for_item.update({
                                "version": temp_arc_loader_item.version,
                                "platform": temp_arc_loader_item.platform,
                                "bo_char": temp_arc_loader_item.byte_order_char,
                                "file_order": [fi['full_filename'] for fi in temp_arc_loader_item.files] if temp_arc_loader_item.files else [],
                                "entry_has_extended_names": temp_arc_loader_item.entry_has_extended_names,
                                "original_file_metadata_map": file_meta_map_item
                            })
                            self.add_status_message(f"Using parameters from '{potential_original_arc_path_item.name}' for '{folder_path_obj_item.name}'.", STATUS_INFO)
                        else:
                            self.add_status_message(f"Failed to load header from '{potential_original_arc_path_item.name}'. Using default parameters for '{folder_path_obj_item.name}'.", STATUS_WARN)
                    except ARCCSkippedError:
                         self.add_status_message(f"Info: Original ARC '{potential_original_arc_path_item.name}' is an ARCC and was skipped. Using default parameters for '{folder_path_obj_item.name}'.", STATUS_INFO)
                    except Exception as e_load_params_item:
                        self.add_status_message(f"Error loading parameters from '{potential_original_arc_path_item.name}' for '{folder_path_obj_item.name}': {e_load_params_item}. Using defaults.", STATUS_WARN)
                    finally:
                        if temp_arc_loader_item: temp_arc_loader_item.close()
                else:
                    self.add_status_message(f"No original ARC found for '{folder_path_obj_item.name}' (expected '{potential_original_arc_path_item.name}'). Using default parameters.", STATUS_DEBUG)
            else:
                self.add_status_message(f"Folder '{folder_path_obj_item.name}' does not end with '_arc'. Using default parameters.", STATUS_DEBUG)

            param_dict_for_worker_item = {
                "version": current_params_for_item["version"],
                "platform": current_params_for_item["platform"],
                "bo_char": current_params_for_item["bo_char"],
                "entry_has_extended_names": current_params_for_item["entry_has_extended_names"]
            }
            all_original_arc_params_dicts.append(param_dict_for_worker_item)
            all_target_is_arcc_flags.append(False)
            all_original_file_orders.append(current_params_for_item["file_order"])
            all_original_file_metadata_maps.append(current_params_for_item["original_file_metadata_map"])

        self._run_task(run_batch_parallel,
                       args_tuple=(_list_inject_worker, items_folder_paths_str, output_rebuilt_dir_str),
                       original_arc_params_list=all_original_arc_params_dicts,
                       target_is_arcc_list=all_target_is_arcc_flags,
                       original_file_orders_list=all_original_file_orders,
                       original_file_metadata_map_list=all_original_file_metadata_maps)


    def start_recursive_extraction(self):
        src = self.rec_extract_source_var.get();
        if not src: messagebox.showwarning("Input Missing","Please select a source directory containing ARC files."); return
        self._run_task(recursive_batch_extract, (src, None))

    def start_folder_injection(self):
        src_dir = self.folder_inject_source_dir_var.get();
        if not src_dir: messagebox.showwarning("Input Missing","Please select the source directory for in-place rebuild."); return
        self._run_task(folder_batch_inject, (src_dir,))

    def start_flatten_extraction(self):
        src_dir = self.flatten_extract_source_var.get()
        out_dir = self.flatten_extract_output_var.get()
        if not src_dir: messagebox.showwarning("Input Missing", "Please select a source directory for flattened extraction."); return
        if not out_dir: messagebox.showwarning("Output Missing", "Please select an output directory for the flattened files."); return
        self._run_task(recursive_flatten_extract, (src_dir, out_dir))

    def start_internal_arc_extraction(self):
        if not self.current_arc_for_internal_view or not self.current_arc_for_internal_view.files:
            messagebox.showwarning("No ARC Loaded", "Please load an ARC file into the preview first.")
            return

        output_dir = self.internal_extract_output_var.get()
        if not output_dir:
            messagebox.showwarning("Output Missing", "Please select an output directory for the extracted items.")
            return

        if not os.path.isdir(output_dir):
            try:
                pathlib.Path(output_dir).mkdir(parents=True, exist_ok=True)
            except Exception as e:
                messagebox.showerror("Output Error", f"Cannot create output directory '{output_dir}': {e}")
                return

        selected_items_for_extraction = []

        def find_selected_dfs(item_iid, current_output_base_folder_name, current_arc_base_path):
            item_node_data = self.tree_item_data.get(item_iid)
            if not item_node_data: return

            is_explicitly_checked = item_node_data['checked_state']

            if is_explicitly_checked and item_node_data['is_folder']:
                new_output_base_folder_name = pathlib.Path(item_node_data['path']).name
                new_arc_base_path = item_node_data['path']
            else:
                new_output_base_folder_name = current_output_base_folder_name
                new_arc_base_path = current_arc_base_path

            if item_node_data['is_folder']:
                for child_iid in self.internal_arc_tree.get_children(item_iid):
                    find_selected_dfs(child_iid, new_output_base_folder_name, new_arc_base_path)
            else:
                if is_explicitly_checked or new_arc_base_path:
                    file_info = item_node_data['file_info']
                    arc_file_full_path_str = file_info['full_filename'].replace('\\', '/')

                    target_disk_path = None
                    if new_arc_base_path:
                        relative_path_in_arc = pathlib.Path(arc_file_full_path_str).relative_to(pathlib.Path(new_arc_base_path))
                        target_disk_path = pathlib.Path(output_dir) / new_output_base_folder_name / relative_path_in_arc
                    elif is_explicitly_checked:
                         target_disk_path = pathlib.Path(output_dir) / pathlib.Path(arc_file_full_path_str).name

                    if target_disk_path:
                        selected_items_for_extraction.append((file_info, target_disk_path))

        for root_iid in self.internal_arc_tree.get_children(''):
            find_selected_dfs(root_iid, "", "")

        if not selected_items_for_extraction:
            messagebox.showinfo("Nothing Selected", "No files or folders are checked for extraction.")
            return

        final_extraction_list = []
        seen_target_paths = set()
        for fi, tdp in selected_items_for_extraction:
            if str(tdp) not in seen_target_paths:
                final_extraction_list.append((fi, tdp))
                seen_target_paths.add(str(tdp))

        if not final_extraction_list:
            messagebox.showinfo("Nothing to Extract", "No items effectively selected for extraction after processing.")
            return

        self.add_status_message(f"Preparing to extract {len(final_extraction_list)} item(s)...", STATUS_INFO)
        self._run_task(self._perform_internal_arc_extraction_thread,
                       args_tuple=(final_extraction_list, self.internal_arc_filepath_var.get()))


    def _perform_internal_arc_extraction_thread(self, items_to_extract, arc_filepath_str,
                                                progress_callback, status_callback, key1, key2):
        arc_for_extraction = None
        try:
            if not self.current_arc_for_internal_view or self.current_arc_for_internal_view._raw_file_path != arc_filepath_str:
                status_callback(f"Re-opening ARC '{os.path.basename(arc_filepath_str)}' for extraction...", STATUS_DEBUG)
                arc_for_extraction = MTArc()
                # For GUI calls, status_callback is self.queue_status, which uses app.queue
                arc_for_extraction.load(arc_filepath_str, key1=key1, key2=key2, status_queue_or_callback=status_callback)
            else:
                arc_for_extraction = self.current_arc_for_internal_view

            total_items = len(items_to_extract)
            processed_count = 0
            error_count = 0

            for i, (file_info, target_disk_path) in enumerate(items_to_extract):
                try:
                    status_callback(f"Extracting '{file_info['full_filename']}' to '{target_disk_path}'...", STATUS_DEBUG)
                    file_data = arc_for_extraction.extract_file(file_info, arc_filepath_str)

                    target_disk_path.parent.mkdir(parents=True, exist_ok=True)
                    with open(target_disk_path, 'wb') as out_f:
                        out_f.write(file_data)
                    processed_count += 1
                except Exception as e:
                    error_count += 1
                    status_callback(f"Error extracting '{file_info['full_filename']}' to '{target_disk_path}': {e}", STATUS_ERROR)
                    traceback.print_exc(file=sys.stderr)

                progress_callback((i + 1) / total_items * 100)

            final_msg = f"Internal ARC extraction complete. Extracted: {processed_count}, Errors: {error_count}."
            final_level = STATUS_SUCCESS if error_count == 0 and processed_count > 0 else \
                        (STATUS_WARN if processed_count > 0 else STATUS_ERROR)
            status_callback(final_msg, final_level)

        except ARCCSkippedError as e:
            progress_callback(100)
            if arc_for_extraction and arc_for_extraction != self.current_arc_for_internal_view:
                 arc_for_extraction.close()
            return
        except Exception as e_load_extract:
            status_callback(f"Error during extraction setup for '{os.path.basename(arc_filepath_str)}': {e_load_extract}", STATUS_ERROR)
            progress_callback(100)
            if arc_for_extraction and arc_for_extraction != self.current_arc_for_internal_view:
                arc_for_extraction.close()
            return
        finally:
            if arc_for_extraction and arc_for_extraction != self.current_arc_for_internal_view:
                arc_for_extraction.close()

    def start_internal_arc_injection(self):
        if not self.current_arc_for_internal_inject_view or not self.current_arc_for_internal_inject_view.files:
            messagebox.showwarning("No ARC Loaded", "Please load an ARC file into the 'Internal-ARC Injection' preview first.")
            return

        original_arc_path = self.internal_inject_filepath_var.get()
        output_arc_path = self.internal_inject_output_var.get()

        if not output_arc_path:
            messagebox.showwarning("Output Missing", "Please select an output path for the rebuilt ARC file.")
            return

        if not original_arc_path:
            messagebox.showerror("Internal Error", "Original ARC file path is missing. Please reload the ARC.")
            return

        if pathlib.Path(original_arc_path).resolve() == pathlib.Path(output_arc_path).resolve():
            response = messagebox.askyesno(
                "Overwrite Warning",
                f"You are attempting to overwrite the original ARC file '{os.path.basename(original_arc_path)}'.\n\n"
                "This operation will modify the original file in place, which is risky. "
                "It's highly recommended to save to a new file to preserve the original.\n\n"
                "Do you wish to proceed and overwrite the original file?"
            )
            if not response:
                self.add_status_message("Injection cancelled by user to prevent overwrite.", STATUS_INFO)
                return

        if not self.files_to_inject_map:
            response = messagebox.askyesno(
                "No Files to Inject",
                "No files have been marked for replacement. The output ARC will be an identical copy.\n"
                "Do you wish to proceed anyway?"
            )
            if not response:
                self.add_status_message("Injection cancelled as no files were selected for replacement.", STATUS_INFO)
                return

        self.add_status_message(f"Starting internal ARC injection for '{os.path.basename(original_arc_path)}'...", STATUS_INFO)
        self._run_task(self._perform_internal_arc_injection_thread,
                       args_tuple=(original_arc_path, self.files_to_inject_map.copy(), output_arc_path))


    def _perform_internal_arc_injection_thread(self, original_arc_filepath: str, files_to_inject_map: dict, output_arc_path: str,
                                                progress_callback, status_callback, key1, key2):
        arc_loader_for_read = None
        arc_saver_for_write = None

        try:
            status_callback(f"Attempting to load original ARC '{os.path.basename(original_arc_filepath)}'...", STATUS_DEBUG)
            arc_loader_for_read = MTArc()
            arc_loader_for_read.load(original_arc_filepath, key1=key1, key2=key2, status_queue_or_callback=status_callback)

            if not arc_loader_for_read.files:
                status_callback(f"Original ARC '{os.path.basename(original_arc_filepath)}' contains no files. Cannot perform injection.", STATUS_ERROR)
                progress_callback(100); return

            files_to_pack_for_save = []
            total_files = len(arc_loader_for_read.files)
            processed_count = 0
            error_count = 0

            status_callback(f"Preparing {total_files} files for repack...", STATUS_INFO)
            for i, original_fi in enumerate(arc_loader_for_read.files):
                full_filename_norm_lower = original_fi['full_filename'].lower().replace('\\', '/')
                new_fi_for_save = original_fi.copy()

                data_source_description = ""
                if full_filename_norm_lower in files_to_inject_map:
                    disk_file_to_inject = files_to_inject_map[full_filename_norm_lower]
                    try:
                        new_data = pathlib.Path(disk_file_to_inject).read_bytes()
                        new_fi_for_save['data'] = new_data
                        new_fi_for_save['original_is_compressed_hint'] = original_fi['is_compressed']
                        new_fi_for_save['original_uncompressed_size_raw_hint'] = original_fi['uncompressed_size_raw']
                        data_source_description = f"new data from '{os.path.basename(disk_file_to_inject)}'"
                    except Exception as e_read_new:
                        status_callback(f"Error reading new data for '{original_fi['full_filename']}' from '{disk_file_to_inject}': {e_read_new}. Using original data instead.", STATUS_WARN)
                        new_fi_for_save['data'] = arc_loader_for_read.extract_file(original_fi, original_arc_filepath)
                        data_source_description = "original data (new data read failed)"
                else:
                    new_fi_for_save['data'] = arc_loader_for_read.extract_file(original_fi, original_arc_filepath)
                    new_fi_for_save['original_is_compressed_hint'] = original_fi['is_compressed']
                    new_fi_for_save['original_uncompressed_size_raw_hint'] = original_fi['uncompressed_size_raw']
                    data_source_description = "original data"

                files_to_pack_for_save.append(new_fi_for_save)
                processed_count += 1
                status_callback(f"Processed file {i+1}/{total_files}: '{original_fi['full_filename']}' (using {data_source_description}).", STATUS_DEBUG)
                progress_callback(processed_count / total_files * 100)

            if not files_to_pack_for_save:
                status_callback("No files were successfully prepared for packing. Aborting injection.", STATUS_ERROR)
                progress_callback(100); return


            status_callback(f"Starting ARC rebuild to '{os.path.basename(output_arc_path)}'...", STATUS_INFO)
            arc_saver_for_write = MTArc()
            arc_saver_for_write.save(
                output_arc_path,
                files_to_pack_for_save,
                key1=key1, key2=key2,
                target_version=arc_loader_for_read.version,
                target_platform=arc_loader_for_read.platform,
                target_byte_order_char=arc_loader_for_read.byte_order_char,
                target_is_arcc=False,
                target_entry_has_extended_names=arc_loader_for_read.entry_has_extended_names
            )
            status_callback(f"Successfully rebuilt ARC to '{os.path.basename(output_arc_path)}'.", STATUS_SUCCESS)

        except ARCCSkippedError as e:
            progress_callback(100)
            if arc_loader_for_read: arc_loader_for_read.close()
            return
        except Exception as e:
            status_callback(f"Error during internal ARC injection: {e}", STATUS_ERROR)
            traceback.print_exc(file=sys.stderr)
            error_count += 1
        finally:
            if arc_loader_for_read: arc_loader_for_read.close()
            if arc_saver_for_write: arc_saver_for_write.close()
            progress_callback(100)


    def update_progress(self,v):
        try:
            self.queue.put({'type':'progress','value':max(0.0, min(100.0, float(v)))})
        except Exception as e:
            print(f"Error in update_progress: {e}", file=sys.stderr)

    def queue_status(self,m,l=STATUS_INFO):
        try:
            self.queue.put({'type':'status','msg':m,'level':l})
        except Exception as e:
            print(f"Error in queue_status putting message '{m}': {e}", file=sys.stderr)

    def check_queue(self):
        try:
            while True:
                item = self.queue.get_nowait()
                if item.get('type') == 'progress':
                    self.progress_var.set(item.get('value', 0.0))
                elif item.get('type') == 'status':
                    msg_content = item.get('msg', '')
                    msg_level = item.get('level', STATUS_INFO)
                    self.add_status_message(msg_content, msg_level)
        except queue.Empty:
            pass
        except Exception as e_queue_processing:
            error_message = f"Error in check_queue processing item: {e_queue_processing!r}"
            print(error_message, file=sys.stderr)
            traceback.print_exc(file=sys.stderr)
            try:
                self.add_status_message(error_message, STATUS_ERROR)
            except Exception as e_logging_to_gui:
                print(f"CRITICAL: Failed to log queue processing error to GUI status: {e_logging_to_gui!r}", file=sys.stderr)
                traceback.print_exc(file=sys.stderr)
        finally:
            self.root.after(100, self.check_queue)

    def add_status_message(self,m,l=STATUS_INFO):
        try:
            if not isinstance(m, str): m = str(m)
            self.status_text.configure(state='normal'); timestamp = datetime.now().strftime("[%H:%M:%S]")
            self.status_text.insert(tk.END,f"{timestamp} {m}\n",(l,)); self.status_text.configure(state='disabled'); self.status_text.see(tk.END); self.root.update_idletasks()
        except Exception as e:
            print(f"[{datetime.now().strftime('%H:%M:%S')}] Error updating status GUI: {e}\nStatus message ({l}): {m}", file=sys.stderr)
            traceback.print_exc(file=sys.stderr)

    def toggle_pop_out_log(self):
        if hasattr(self, 'log_is_popped_out') and self.log_is_popped_out: # Check if attribute exists
            if hasattr(self, 'log_toplevel_window') and self.log_toplevel_window:
                self.status_text.grid_forget()
                self.status_frame.pack(pady=(0,0), padx=10, fill='both', expand=True, side=tk.TOP, in_=self.bottom_pane_frame)
                self.status_text.grid(row=0, column=0, sticky='nsew', in_=self.status_frame)
                self.log_toplevel_window.destroy()
                self.log_toplevel_window = None
            if hasattr(self, 'pop_log_button'): self.pop_log_button.config(text="↗ Pop Out Log")
            self.log_is_popped_out = False
        else:
            self.log_toplevel_window = tk.Toplevel(self.root)
            self.log_toplevel_window.title("Log Output")
            self.log_toplevel_window.geometry("800x400")
            self.log_toplevel_window.grid_rowconfigure(0, weight=1)
            self.log_toplevel_window.grid_columnconfigure(0, weight=1)
            self.status_text.grid_forget()
            self.status_frame.pack_forget()
            self.status_text.grid(row=0, column=0, sticky='nsew', in_=self.log_toplevel_window)
            if not hasattr(self, 'pop_log_button'): # Create button if it doesn't exist
                 # This part assumes you have a frame where pop_log_button should be.
                 # For example, in your header_frame. This might need adjustment based on your layout.
                 # If it was meant to be created elsewhere, this is a placeholder.
                 self.pop_log_button = ttk.Button(self.top_pane_frame, text="↙ Dock Log", command=self.toggle_pop_out_log, style='TButton')
                 self.pop_log_button.pack(side=tk.RIGHT, padx=(0,5), pady=5) # Example packing
            else:
                 self.pop_log_button.config(text="↙ Dock Log")

            self.log_is_popped_out = True
            self.log_toplevel_window.protocol("WM_DELETE_WINDOW", self.handle_log_toplevel_close)


    def handle_log_toplevel_close(self):
        if hasattr(self, 'log_is_popped_out') and self.log_is_popped_out:
            self.status_text.grid_forget()
            self.status_frame.pack(pady=(0,0), padx=10, fill='both', expand=True, side=tk.TOP, in_=self.bottom_pane_frame)
            self.status_text.grid(row=0, column=0, sticky='nsew', in_=self.status_frame)
            if hasattr(self, 'log_toplevel_window') and self.log_toplevel_window and self.log_toplevel_window.winfo_exists():
                pass # self.log_toplevel_window.destroy() is implicitly called by WM_DELETE_WINDOW
            self.log_toplevel_window = None
            if hasattr(self, 'pop_log_button'): self.pop_log_button.config(text="↗ Pop Out Log")
            self.log_is_popped_out = False

    def show_help(self):
        help_text_content = """
        SaladSoftware MT Framework Arc Tool - Help Section
        buh
        Tab Descriptions:

        1. Extract Arc Files (List):
           - Select one or more .arc files (or drag & drop).
           - Each ARC is extracted into its own subfolder (e.g., 'file.arc' extracts to 'file_arc/').
           - The internal folder structure of each ARC is preserved within its output subfolder.
           - Output folders are created next to their respective input .arc files.

        2. Inject Arc Folders (List):
           - Add one or more source folders to the list. These folders contain files you want to pack into ARCs.
           - Select an output directory where the new .arc files will be saved.
           - Each source folder is rebuilt into a new .arc file ('hotdog' becomes 'hotdog.arc').
           - If a folder is named 'myarc_arc' and 'myarc.arc' exists in the same directory,
           parameters (version, platform, file order, etc.) from 'myarc.arc' will be used for the rebuild.
           - Otherwise, default parameters are used.

        3. Recursive Extract Arcs:
           - Select a root directory.
           - The tool will scan this directory and all its subdirectories for .arc files.
           - Each found .arc file is extracted similarly to 'Extract Arc Files (List)'
           (into its own subfolder, next to the ARC).

        4. Recursive Inject (In-Place):
           - Select a root directory that contains both original .arc files and
           corresponding unpacked/edited folders (typically named 'original_arc_name_arc').
           - The tool matches *_arc folders with their .arc files.
           - Original .arc files are backed up into an 'original_arc_backups' subfolder (created within the selected root directory).
           - The *_arc folders are then rebuilt into .arc files, replacing the originals.
           - This process attempts to use the (version, platform, byte order,
           file order, compression hints) from the original ARC for the rebuild.
           - Processed *_arc folders are also moved to the backup directory.

        5. Extract All (Flatten File Struct):
           - Select a root directory containing .arc files (scanned recursively) using "Browse" and "Start".
           - OR Drag & Drop a single .arc file onto this tab.
           - Select a single output directory.
           - All files from all found ARCs (recursive) or the single dropped ARC are extracted directly into this single output directory.
           - The original folder structure *within* the ARCs is discarded (flattened).
           - To prevent name collisions, extracted filenames are prefixed with the name of their source ARC
           (e.g., 'arc1_image.tex', 'arc2_sound.wav').

        6. Internal-ARC Extraction:
           - Select a single .arc file to load (or drag & drop) and preview its internal file/folder structure in a tree view.
           - Check the boxes next to individual files or folders within the tree that you wish to extract.
             - Checking a folder will effectively check all its contents.
           - Select an output directory.
           - Click "Extract Selected Items".
             - If a file is checked, it's saved to: `output_dir/filename.ext`
             - If a folder (e.g., 'textures/player') is checked, its contents are saved to:
             `output_dir/player/content_file.ext`.

        7. Internal-ARC Injection:
           - Select a single .arc file to load (or drag & drop) and preview its internal file/folder structure.
           - Select a file in the tree and click "Replace Selected File..." to choose a new file from your disk.
             - The tree will visually indicate which files are marked for replacement.
           - Select an output path for the *newly rebuilt* ARC file. This will be a copy, not an in-place modification by default.
           - Click "Start Injection".
           - The tool will rebuild the ARC:
             - Files marked for replacement will use the new data.
             - All other files will be copied from the original ARC.
             - The original file order, format (version, platform, byte order) will be retained.

        Note: This tool does not process encrypted .arcc files. Any .arcc files encountered will be skipped.
        """
        help_win = tk.Toplevel(self.root)
        help_win.title("Help - SaladSoftware ARC Tool")
        help_win.configure(bg=BG_COLOR)
        help_win.geometry("1200x900")

        help_win.grid_rowconfigure(0, weight=1)
        help_win.grid_columnconfigure(0, weight=1)

        content_frame = ttk.Frame(help_win, style='TFrame', padding=10)
        content_frame.grid(row=0, column=0, sticky='nsew')
        content_frame.grid_rowconfigure(0, weight=1)
        content_frame.grid_columnconfigure(0, weight=1)

        help_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE-1)
        help_text_widget = scrolledtext.ScrolledText(
            content_frame,
            wrap=tk.WORD,
            font=help_font,
            bg=WIDGET_BG,
            fg=TEXT_COLOR,
            bd=1,
            relief='sunken',
            padx=5,
            pady=5
        )
        help_text_widget.grid(row=0, column=0, sticky='nsew', pady=(0,10))

        dedented_help_text = textwrap.dedent(help_text_content.strip())
        help_text_widget.insert(tk.END, dedented_help_text)
        help_text_widget.configure(state='disabled')

        def _close_help():
            help_win.grab_release()
            help_win.destroy()

        ok_button = ttk.Button(content_frame, text="OK", command=_close_help, style='TButton')
        ok_button.grid(row=1, column=0, pady=(5,0))

        help_win.transient(self.root)
        help_win.grab_set()
        help_win.protocol("WM_DELETE_WINDOW", _close_help)
        help_win.focus_set()
        ok_button.focus_set()

# --- CLI Support ---
def cli_status_callback(message, level=STATUS_INFO):
    timestamp = datetime.now().strftime("[%H:%M:%S]")
    print(f"{timestamp} [{level.upper()}] {message}", file=sys.stderr if level in [STATUS_ERROR, STATUS_WARN] else sys.stdout)

def cli_progress_callback(value):
    sys.stdout.write(f"\rProgress: {int(value):3}%")
    sys.stdout.flush()
    if value >= 100:
        sys.stdout.write("\n") # Newline after completion
        sys.stdout.flush()

class CliStatusQueueAdapter:
    """ Adapts the status_queue.put interface to a direct callback for MTArc.load """
    def __init__(self, callback):
        self.callback = callback
    def put(self, item):
        if item and isinstance(item, dict) and item.get('type') == 'status':
            self.callback(item.get('msg',''), item.get('level', STATUS_INFO))
        # Progress items from MTArc.load are ignored by this adapter, CLI progress is handled by run_batch_parallel

def handle_cli_extract(args):
    cli_status_callback(f"Starting List Extraction for: {', '.join(args.arc_files)}", STATUS_INFO)
    run_batch_parallel(_list_extract_worker, args.arc_files, None,
                       cli_progress_callback, cli_status_callback, args.key1, args.key2)

def handle_cli_inject(args):
    cli_status_callback(f"Starting List Injection for folders: {', '.join(args.folders)}", STATUS_INFO)
    if not args.output_dir:
        cli_status_callback("Error: --output-dir is required for inject command.", STATUS_ERROR)
        return

    all_params, all_orders, all_meta_maps, all_is_arcc = [], [], [], [] # target_is_arcc is always False

    default_params = {
        "version": DEFAULT_VERSION, "platform": DEFAULT_PLATFORM, "bo_char": DEFAULT_BYTE_ORDER_CHAR,
        "entry_has_extended_names": False
    }

    for folder_path_str in args.folders:
        folder_p = pathlib.Path(folder_path_str)
        params_for_item = default_params.copy()
        file_order_for_item = None
        meta_map_for_item = {}

        if folder_p.name.endswith("_arc"):
            arc_basename = folder_p.name[:-4]
            potential_orig_arc = folder_p.parent / (arc_basename + ".arc")
            if potential_orig_arc.is_file():
                cli_status_callback(f"Found potential original ARC '{potential_orig_arc.name}' for '{folder_p.name}'. Loading parameters...", STATUS_DEBUG)
                temp_arc = MTArc()
                try:
                    # Use adapter for MTArc.load's status_queue
                    temp_arc.load(str(potential_orig_arc), key1=args.key1, key2=args.key2, status_queue_or_callback=CliStatusQueueAdapter(cli_status_callback))
                    if temp_arc.arc_header:
                        params_for_item = {
                            "version": temp_arc.version, "platform": temp_arc.platform,
                            "bo_char": temp_arc.byte_order_char, "entry_has_extended_names": temp_arc.entry_has_extended_names
                        }
                        file_order_for_item = [fi['full_filename'] for fi in temp_arc.files]
                        for fi_orig in temp_arc.files:
                            norm_key = fi_orig['full_filename'].lower().replace('\\','/')
                            meta_map_for_item[norm_key] = {
                                'is_compressed': fi_orig['is_compressed'],
                                'uncompressed_size_raw': fi_orig['uncompressed_size_raw']
                            }
                        cli_status_callback(f"Using parameters from '{potential_orig_arc.name}'.", STATUS_INFO)
                    else:
                         cli_status_callback(f"Failed to load header from '{potential_orig_arc.name}', using defaults for '{folder_p.name}'.", STATUS_WARN)
                except ARCCSkippedError:
                    cli_status_callback(f"Original ARC '{potential_orig_arc.name}' is ARCC, using defaults for '{folder_p.name}'.", STATUS_INFO)
                except Exception as e:
                    cli_status_callback(f"Error loading original ARC '{potential_orig_arc.name}': {e}. Using defaults.", STATUS_WARN)
                finally:
                    if temp_arc: temp_arc.close()
            else:
                 cli_status_callback(f"No original ARC found for '{folder_p.name}', using defaults.", STATUS_DEBUG)
        else:
            cli_status_callback(f"Folder '{folder_p.name}' doesn't end with '_arc', using defaults.", STATUS_DEBUG)

        all_params.append(params_for_item)
        all_orders.append(file_order_for_item)
        all_meta_maps.append(meta_map_for_item)
        all_is_arcc.append(False) # ARCC rebuild not supported

    run_batch_parallel(_list_inject_worker, args.folders, args.output_dir,
                       cli_progress_callback, cli_status_callback, args.key1, args.key2,
                       original_arc_params_list=all_params,
                       target_is_arcc_list=all_is_arcc,
                       original_file_orders_list=all_orders,
                       original_file_metadata_map_list=all_meta_maps)

def handle_cli_extract_recursive(args):
    cli_status_callback(f"Starting Recursive Extraction from: {args.source_dir}", STATUS_INFO)
    recursive_batch_extract(args.source_dir, None, cli_progress_callback, cli_status_callback, args.key1, args.key2)

def handle_cli_inject_recursive(args):
    cli_status_callback(f"Starting Recursive In-Place Injection in: {args.source_dir}", STATUS_INFO)
    folder_batch_inject(args.source_dir, cli_progress_callback, cli_status_callback, args.key1, args.key2)

def handle_cli_extract_flat(args):
    cli_status_callback(f"Starting Flattened Extraction from '{args.source_path}' to '{args.output_dir}'", STATUS_INFO)
    source_p = pathlib.Path(args.source_path)
    if not args.output_dir:
        cli_status_callback("Error: --output-dir is required for extract-flat command.", STATUS_ERROR)
        return

    if source_p.is_file() and source_p.suffix.lower() == '.arc':
        run_batch_parallel(_flatten_extract_worker, [str(source_p)], args.output_dir,
                           cli_progress_callback, cli_status_callback, args.key1, args.key2)
    elif source_p.is_dir():
        recursive_flatten_extract(str(source_p), args.output_dir,
                                  cli_progress_callback, cli_status_callback, args.key1, args.key2)
    else:
        cli_status_callback(f"Error: Source path '{args.source_path}' is not a valid ARC file or directory.", STATUS_ERROR)

def handle_cli_extract_internal(args):
    cli_status_callback(f"Starting Internal ARC Extraction from '{args.arc_file}' to '{args.output_dir}'", STATUS_INFO)
    if not args.output_dir:
        cli_status_callback("Error: --output-dir is required.", STATUS_ERROR)
        return
    if not args.items:
        cli_status_callback("Error: --items must specify at least one internal path to extract.", STATUS_ERROR)
        return

    arc = MTArc()
    items_to_extract_data = []
    try:
        arc.load(args.arc_file, key1=args.key1, key2=args.key2, status_queue_or_callback=CliStatusQueueAdapter(cli_status_callback))
        if not arc.files:
            cli_status_callback(f"ARC '{args.arc_file}' is empty or failed to load.", STATUS_WARN)
            return

        output_dir_p = pathlib.Path(args.output_dir)
        output_dir_p.mkdir(parents=True, exist_ok=True)

        arc_files_map = {fi['full_filename'].replace('\\', '/'): fi for fi in arc.files}

        for internal_path_raw in args.items:
            internal_path = internal_path_raw.replace('\\', '/')
            if internal_path in arc_files_map:
                file_info = arc_files_map[internal_path]
                target_disk_path = output_dir_p / internal_path # Preserve full structure
                items_to_extract_data.append((file_info, target_disk_path))
            else:
                cli_status_callback(f"Warning: Internal item '{internal_path}' not found in ARC '{args.arc_file}'.", STATUS_WARN)

        if not items_to_extract_data:
            cli_status_callback("No valid items found to extract from the ARC.", STATUS_INFO)
            return

        # Create a dummy app or adapt _perform_internal_arc_extraction_thread if it relies on app state
        # For now, let's call a simplified version or adapt the existing one.
        # The GUI version of _perform_internal_arc_extraction_thread uses self.current_arc_for_internal_view
        # We can pass the loaded `arc` object.
        # We'll call it directly in the main thread for CLI simplicity here, or adapt for threading if preferred.
        # Adapting _perform_internal_arc_extraction_thread to be callable without 'self'
        
        # Simplified direct extraction loop for CLI:
        total_items = len(items_to_extract_data)
        processed_count = 0
        error_count = 0
        for i, (file_info, target_disk_path) in enumerate(items_to_extract_data):
            try:
                cli_status_callback(f"Extracting '{file_info['full_filename']}' to '{target_disk_path}'...", STATUS_DEBUG)
                file_data = arc.extract_file(file_info, args.arc_file)
                target_disk_path.parent.mkdir(parents=True, exist_ok=True)
                with open(target_disk_path, 'wb') as out_f:
                    out_f.write(file_data)
                processed_count += 1
            except Exception as e:
                error_count += 1
                cli_status_callback(f"Error extracting '{file_info['full_filename']}' to '{target_disk_path}': {e}", STATUS_ERROR)
            cli_progress_callback((i + 1) / total_items * 100)
        
        final_msg = f"Internal ARC extraction complete. Extracted: {processed_count}, Errors: {error_count}."
        final_level = STATUS_SUCCESS if error_count == 0 and processed_count > 0 else (STATUS_WARN if processed_count > 0 else STATUS_ERROR)
        cli_status_callback(final_msg, final_level)

    except ARCCSkippedError:
        pass # message already handled by MTArc.load
    except Exception as e:
        cli_status_callback(f"Error during internal ARC extraction: {e}", STATUS_ERROR)
        traceback.print_exc(file=sys.stderr)
    finally:
        if arc: arc.close()

def handle_cli_inject_internal(args):
    cli_status_callback(f"Starting Internal ARC Injection from '{args.arc_file}' to '{args.output_arc}'", STATUS_INFO)
    if not args.output_arc:
        cli_status_callback("Error: --output-arc is required.", STATUS_ERROR)
        return

    files_to_inject_map_cli = {}
    if args.replace:
        for rep_arg in args.replace:
            parts = rep_arg.split('=', 1)
            if len(parts) == 2:
                internal_path = parts[0].strip().replace('\\', '/')
                disk_file_path = parts[1].strip()
                if not os.path.isfile(disk_file_path):
                    cli_status_callback(f"Error: Replacement disk file not found: '{disk_file_path}' for internal '{internal_path}'", STATUS_ERROR)
                    return
                files_to_inject_map_cli[internal_path.lower()] = disk_file_path
            else:
                cli_status_callback(f"Error: Invalid format for --replace argument: '{rep_arg}'. Expected 'internal/path=disk/path'.", STATUS_ERROR)
                return

    if not files_to_inject_map_cli and not args.force_repack:
        cli_status_callback("No files specified for replacement via --replace. Use --force-repack to repack without changes.", STATUS_INFO)
        return

    # Simplified direct injection for CLI:
    arc_loader = MTArc()
    arc_saver = MTArc()
    try:
        cli_status_callback(f"Loading original ARC '{args.arc_file}'...", STATUS_DEBUG)
        arc_loader.load(args.arc_file, key1=args.key1, key2=args.key2, status_queue_or_callback=CliStatusQueueAdapter(cli_status_callback))
        if not arc_loader.files:
            cli_status_callback(f"Original ARC '{args.arc_file}' is empty or failed to load.", STATUS_ERROR)
            return

        files_to_pack = []
        total_arc_files = len(arc_loader.files)
        cli_status_callback(f"Preparing {total_arc_files} files for repack...", STATUS_INFO)

        for i, original_fi in enumerate(arc_loader.files):
            new_fi = original_fi.copy()
            internal_path_norm = original_fi['full_filename'].lower().replace('\\', '/')
            
            if internal_path_norm in files_to_inject_map_cli:
                disk_path = files_to_inject_map_cli[internal_path_norm]
                cli_status_callback(f"Replacing '{original_fi['full_filename']}' with data from '{disk_path}'...", STATUS_DEBUG)
                try:
                    new_data = pathlib.Path(disk_path).read_bytes()
                    new_fi['data'] = new_data
                except Exception as e:
                    cli_status_callback(f"Error reading replacement file '{disk_path}': {e}. Using original data.", STATUS_WARN)
                    new_fi['data'] = arc_loader.extract_file(original_fi, args.arc_file) # Fallback
            else:
                new_fi['data'] = arc_loader.extract_file(original_fi, args.arc_file)
            
            new_fi['original_is_compressed_hint'] = original_fi['is_compressed']
            new_fi['original_uncompressed_size_raw_hint'] = original_fi['uncompressed_size_raw']
            files_to_pack.append(new_fi)
            cli_progress_callback((i + 1) / total_arc_files * 100)
        
        cli_status_callback(f"Saving rebuilt ARC to '{args.output_arc}'...", STATUS_INFO)
        arc_saver.save(
            args.output_arc, files_to_pack,
            key1=args.key1, key2=args.key2,
            target_version=arc_loader.version,
            target_platform=arc_loader.platform,
            target_byte_order_char=arc_loader.byte_order_char,
            target_is_arcc=False, # ARCC not supported for rebuild
            target_entry_has_extended_names=arc_loader.entry_has_extended_names
        )
        cli_status_callback(f"Successfully rebuilt ARC to '{args.output_arc}'.", STATUS_SUCCESS)

    except ARCCSkippedError:
        pass
    except Exception as e:
        cli_status_callback(f"Error during internal ARC injection: {e}", STATUS_ERROR)
        traceback.print_exc(file=sys.stderr)
    finally:
        if arc_loader: arc_loader.close()
        if arc_saver: arc_saver.close()

# --- MAIN EXECUTION ---
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=f"Handburger's SaladSoftware MT Arc Tool - Version {VERSION}", formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('--version', action='version', version=f'%(prog)s {VERSION}')
    subparsers = parser.add_subparsers(dest="command", title="Commands",
                                       help="Run a command with -h for more details (e.g., %(prog)s extract -h)")

    key_args = [
        (['-k1', '--key1'], {'type': str, 'default': None, 'help': 'Blowfish Key Part 1 (currently unused).'}),
        (['-k2', '--key2'], {'type': str, 'default': None, 'help': 'Blowfish Key Part 2 (currently unused).'})
    ]

    # Extract command
    p_extract = subparsers.add_parser('extract', help='Extract one or more ARC files. Output is <filename>_arc next to each input.')
    p_extract.add_argument('arc_files', metavar='ARC_FILE', type=str, nargs='+', help='Path(s) to ARC file(s) to extract.')
    for pargs, pkwargs in key_args: p_extract.add_argument(*pargs, **pkwargs)
    p_extract.set_defaults(func=handle_cli_extract)

    # Inject command
    p_inject = subparsers.add_parser('inject', help='Rebuild ARC files from source folders.')
    p_inject.add_argument('folders', metavar='FOLDER', type=str, nargs='+', help='Path(s) to source folder(s) to rebuild into ARCs.')
    p_inject.add_argument('--output-dir', '-o', type=str, required=True, help='Directory to save rebuilt ARC files.')
    for pargs, pkwargs in key_args: p_inject.add_argument(*pargs, **pkwargs)
    p_inject.set_defaults(func=handle_cli_inject)

    # Extract-recursive command
    p_extract_rec = subparsers.add_parser('extract-recursive', help='Recursively find and extract ARC files in a directory.')
    p_extract_rec.add_argument('source_dir', metavar='SOURCE_DIR', type=str, help='Root directory to scan for ARC files.')
    for pargs, pkwargs in key_args: p_extract_rec.add_argument(*pargs, **pkwargs)
    p_extract_rec.set_defaults(func=handle_cli_extract_recursive)

    # Inject-recursive command
    p_inject_rec = subparsers.add_parser('inject-recursive', help='Recursively find and rebuild ARC files in-place from matching *_arc folders.')
    p_inject_rec.add_argument('source_dir', metavar='SOURCE_DIR', type=str, help='Root directory with ARCs and *_arc folders.')
    for pargs, pkwargs in key_args: p_inject_rec.add_argument(*pargs, **pkwargs)
    p_inject_rec.set_defaults(func=handle_cli_inject_recursive)

    # Extract-flat command
    p_extract_flat = subparsers.add_parser('extract-flat', help='Extract all files from ARC(s) into a single flat output directory.')
    p_extract_flat.add_argument('source_path', metavar='SOURCE_PATH', type=str, help='Path to a single ARC file or a root directory to scan recursively.')
    p_extract_flat.add_argument('--output-dir', '-o', type=str, required=True, help='Directory to save all extracted files (flattened).')
    for pargs, pkwargs in key_args: p_extract_flat.add_argument(*pargs, **pkwargs)
    p_extract_flat.set_defaults(func=handle_cli_extract_flat)

    # Extract-internal command
    p_extract_int = subparsers.add_parser('extract-internal', help='Extract specific items from an ARC, preserving structure.')
    p_extract_int.add_argument('arc_file', metavar='ARC_FILE', type=str, help='Path to the source ARC file.')
    p_extract_int.add_argument('--items', metavar='INTERNAL_PATH', type=str, nargs='+', required=True, help='Full internal path(s) of items to extract (e.g., "path/to/file.tex").')
    p_extract_int.add_argument('--output-dir', '-o', type=str, required=True, help='Directory to save extracted items.')
    for pargs, pkwargs in key_args: p_extract_int.add_argument(*pargs, **pkwargs)
    p_extract_int.set_defaults(func=handle_cli_extract_internal)

    # Inject-internal command
    p_inject_int = subparsers.add_parser('inject-internal', help='Rebuild an ARC, replacing specific internal files with disk files.')
    p_inject_int.add_argument('arc_file', metavar='ARC_FILE', type=str, help='Path to the source ARC file.')
    p_inject_int.add_argument('--replace', metavar='INTERNAL=DISK', action='append', help='Specify a replacement: "internal/path=path/to/diskfile". Can be used multiple times.')
    p_inject_int.add_argument('--output-arc', '-o', type=str, required=True, help='Path to save the newly rebuilt ARC file.')
    p_inject_int.add_argument('--force-repack', action='store_true', help='Force repacking even if no files are replaced (useful for testing or format conversion if other params change).')
    for pargs, pkwargs in key_args: p_inject_int.add_argument(*pargs, **pkwargs)
    p_inject_int.set_defaults(func=handle_cli_inject_internal)

    args = parser.parse_args()

    # --- Common Setup (Crypto check, Extension map loading) ---
    try:
        _ = Blowfish.new(b"12345678", Blowfish.MODE_ECB) # Basic check
    except ImportError:
        msg = "Required 'pycryptodome' library not found. Please install it (e.g., pip install pycryptodome)."
        if not args.command: # GUI mode
            try:
                temp_root_crypto = tk.Tk(); temp_root_crypto.withdraw()
                messagebox.showerror("Dependency Missing", msg)
                temp_root_crypto.destroy()
            except tk.TclError: print(f"ERROR: {msg}", file=sys.stderr)
        else: # CLI mode
            print(f"ERROR: {msg}", file=sys.stderr)
        sys.exit(1)
    except Exception as e_crypto_test:
        msg = f"Error initializing 'pycryptodome': {e_crypto_test}. It might be installed incorrectly."
        if not args.command: # GUI mode
            try:
                temp_root_crypto = tk.Tk(); temp_root_crypto.withdraw()
                messagebox.showerror("Dependency Error", msg)
                temp_root_crypto.destroy()
            except tk.TclError: print(f"ERROR: {msg}", file=sys.stderr)
        else: # CLI mode
            print(f"ERROR: {msg}", file=sys.stderr)
        sys.exit(1)

    primary_ext_map_path = resource_path(EXTENSION_MAP_FILE)
    game_specific_ext_map_path = resource_path(GAME_SPECIFIC_HASH_FILE)

    if not os.path.exists(primary_ext_map_path):
        warning_msg_ext = (f"Primary extension map file '{EXTENSION_MAP_FILE}' not found.\n"
                           "Extracted files might have generic hexadecimal extensions.")
        if not args.command: # GUI mode
             try:
                temp_root_warn = tk.Tk(); temp_root_warn.withdraw();
                messagebox.showwarning("Extension Map Missing", warning_msg_ext)
                temp_root_warn.destroy()
             except tk.TclError: print(f"WARNING: {warning_msg_ext}", file=sys.stderr) # Fallback if Tk fails early
        else: # CLI mode
            print(f"WARNING: {warning_msg_ext}", file=sys.stderr)

    load_extension_map(primary_ext_map_path, game_specific_ext_map_path)
    # --- End Common Setup ---

    if hasattr(args, 'func'):
        args.func(args) # Execute CLI command handler
    else: # No command given, or invalid command, default to GUI
        if TkinterDnD:
            root = TkinterDnD.Tk()
        else:
            try:
                root = tk.Tk()
                messagebox.showwarning("Dependency Missing",
                                     "Required 'tkinterdnd2' library not found for drag & drop.\n"
                                     "Please install it (e.g., pip install tkinterdnd2).\n"
                                     "The application will run without drag & drop support.")
            except tk.TclError:
                 print("ERROR: tkinterdnd2 library not found AND Tkinter is not available for dialog.\n"
                       "Please install it (e.g., pip install tkinterdnd2).\n"
                       "Drag & drop will be disabled.", file=sys.stderr)
                 sys.exit(1) # Critical for GUI if Tk itself fails

        app = ArcToolApp(root)
        root.mainloop()