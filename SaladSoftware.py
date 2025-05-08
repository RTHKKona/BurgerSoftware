# Handburger's MT Framework ARC Decryptor/Extractor
# This script is a Python port of the original C# code from IcySon55's Kuriimu project.
# It is designed to process and extract files from MT Framework ARC archives.
# The script includes various utility functions, a GUI for user interaction, and support for Blowfish encryption/decryption.

# --- IMPORTS ---
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext, simpledialog
import tkinter.font as tkFont
import os
import sys
import struct
import zlib
import io
import threading
import queue
import pathlib # For easier path manipulation and recursive glob
import concurrent.futures # For parallel processing
import traceback # For detailed error info
import time # For timing operations
from collections import namedtuple
from Crypto.Cipher import Blowfish
# from Crypto.Util.Padding import pad, unpad # Using manual null padding
# from Crypto.Random import get_random_bytes # Not currently needed
from datetime import datetime # For timestamps
import shutil # For moving files/folders


# --- CONSTANTS ---
# --- Color Scheme ---
BG_COLOR='#2b2b2b';TEXT_COLOR='#ffebcd';WIDGET_BG='#3c3f41';INPUT_TEXT_COLOR='#f0f0f0'
BUTTON_BG='#4c4c4c';BUTTON_FG=TEXT_COLOR;BUTTON_ACTIVE_BG='#5c5c5c';BUTTON_PRESSED_BG='#636363'
BUTTON_BORDER='#1e1e1e';HEADER_BG='#4a4a4a';HEADER_TEXT=TEXT_COLOR;HEADER_ACTIVE_BG=WIDGET_BG
HEADER_ACTIVE_TEXT='#ffffff';HIGHLIGHT_BG='#52596b';HIGHLIGHT_TEXT='#ffffff'
STATUS_ERROR_FG='#ff6b6b';STATUS_WARN_FG='#ffb366';STATUS_SUCCESS_FG='#86e3a0'
STATUS_INFO_FG=TEXT_COLOR;STATUS_DEBUG_FG='#999999'
# --- Font ---
FONT_FAMILY="JetBrains Mono";FONT_SIZE=10;FONT_SETTINGS=(FONT_FAMILY,FONT_SIZE)
# --- Platform Enum ---
class Platform: UNKNOWN=0; PC=1; CTR=2; PS3=3; Switch=4
# --- ARC Constants ---
DEFAULT_VERSION=7;DEFAULT_BYTE_ORDER_CHAR='<';DEFAULT_PLATFORM=Platform.Switch # Default to Switch for rebuilds
# --- Structs ---
def format_struct(e, p): return e + p
FMT_HEADER_COMMON="4sHH"; SIZE_HEADER_COMMON=8; FMT_HEADER_PC_EXTRA="I"; SIZE_HEADER_PC_EXTRA=4
FMT_ENTRY="64sIiii"; SIZE_ENTRY=80; FMT_ENTRY_SWITCH="64sIiiii"; SIZE_ENTRY_SWITCH=84
FMT_HFS_HEADER="4shhiI"; SIZE_HFS_HEADER=16; FMT_HFS_FOOTER="QQ"; SIZE_HFS_FOOTER=16
# --- Zlib/Align/Magic ---
ZLIB_COMPRESSION_LEVEL = 9; ALIGNMENT_SWITCH = 0x8000; ALIGNMENT_PC_DEFAULT = 0x100
MAGIC_ARC_LE=b'ARC\x00'; MAGIC_ARCC_LE=b'ARCC'; MAGIC_ARC_BE=b'\x00CRA'; MAGIC_HFS_LE=b'HFS\x00'; MAGIC_HFS_BE=b'\x00SFH'
# --- Status Levels ---
STATUS_INFO="info"; STATUS_SUCCESS="success"; STATUS_WARN="warn"; STATUS_ERROR="error"; STATUS_DEBUG="debug"
# --- Parallel Processing ---
MAX_WORKERS = os.cpu_count() * 2 if os.cpu_count() else 4
MAX_WORKERS = max(4, MAX_WORKERS if MAX_WORKERS is not None else 4)
MAX_WORKERS = min(MAX_WORKERS, 32)

# --- Extension Map (Will be populated from file) ---
EXTENSION_MAP = {}
REV_EXTENSION_MAP = {}
EXTENSION_MAP_FILE = "unique_extensions.txt" # Default to user-provided file


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
        "is_compressed":False,"calculated_uncompressed_size":None, # Calculated size can be None if original size is invalid
    }

def load_extension_map(filepath: str):
    """
    Loads the extension map from a text file (like unique_extensions.txt).
    Each line is either an 8-char hex hash or a plaintext extension string (without dot).
    """
    global EXTENSION_MAP, REV_EXTENSION_MAP
    EXTENSION_MAP = {}
    REV_EXTENSION_MAP = {}

    if not os.path.isfile(filepath):
        print(f"Warning: Extension map file not found at '{filepath}'. Using empty map.", file=sys.stderr)
        return

    potential_hashes_from_file = set()
    potential_extension_strings = []

    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            for line_num, line in enumerate(f, 1):
                line = line.strip()
                if not line or line.startswith('#') or line.startswith('//'):
                    continue

                is_potential_hash = False
                if len(line) == 8:
                    try:
                        hash_val = int(line, 16) # Check if it's a valid hex
                        # No explicit range check needed due to Python's arbitrary int size,
                        # but struct.pack would fail later for out-of-range ULONG.
                        # For now, accept any 8-char hex as a potential hash.
                        potential_hashes_from_file.add(hash_val)
                        is_potential_hash = True
                    except ValueError:
                        pass # Not a valid 8-char hex, treat as potential extension string

                if not is_potential_hash:
                    # Treat as a plaintext extension string (e.g., "tex", "arc", "w00d")
                    # Basic validation: common extension characters
                    # Allow alphanum, underscore. Add more if needed, but keep it simple.
                    if line and all(c.isalnum() or c == '_' for c in line):
                         potential_extension_strings.append(line)
                    else:
                        # Check if it's a multi-part extension like "main.dfa" but without the leading dot
                        # This case is less likely for unique_extensions.txt format
                        # For now, we assume simple extension strings if not hashes
                        print(f"Warning: Line {line_num} in {filepath}: Skipping unusual string '{line}' (neither 8-char hex nor simple extension).", file=sys.stderr)
        
        # Process plaintext extension strings first
        for ext_str_no_dot in potential_extension_strings:
            actual_ext_with_dot = "." + ext_str_no_dot # e.g., ".tex"
            hash_for_ext = calculate_arc_hash(ext_str_no_dot) # e.g., calculate_arc_hash("tex")

            # If this hash is already mapped, prefer the existing one if different, or just ensure consistency.
            # For simplicity, new entries will overwrite, assuming the list is curated.
            EXTENSION_MAP[hash_for_ext] = actual_ext_with_dot
            REV_EXTENSION_MAP[actual_ext_with_dot.lower()] = hash_for_ext
            
            # If this calculated hash was also listed explicitly as a hex hash,
            # it means it's "explained" by a plaintext string.
            if hash_for_ext in potential_hashes_from_file:
                potential_hashes_from_file.remove(hash_for_ext)

        # Any hashes remaining in potential_hashes_from_file are those listed as hex
        # but for which no plaintext extension string in the file calculated to that hash.
        # These will be handled by get_full_filename's fallback (e.g. ".1234ABCD").
        # No explicit add to EXTENSION_MAP for these is strictly needed for functionality,
        # as get_full_filename handles hashes not in EXTENSION_MAP by formatting them.

        num_mapped = len(EXTENSION_MAP)
        num_unexplained_hashes = len(potential_hashes_from_file)
        print(f"Loaded {num_mapped} extension mappings from {filepath}. "
              f"({num_unexplained_hashes} additional 8-char hex strings were found but not mapped to a plaintext extension in the file).")

    except Exception as e:
        print(f"Error loading extension map from {filepath}: {e}", file=sys.stderr)
        traceback.print_exc() # More detail for debugging map loading
        EXTENSION_MAP = {} 
        REV_EXTENSION_MAP = {}


def get_full_filename(file_info):
    """Constructs the full filename (preserving separators) from base name and extension hash, using loaded map."""
    try:
        name = "decode_error" # Default if decoding fails
        filename_bytes = file_info.get("filename_base", b'')
        if not filename_bytes: name = ""
        else:
            # Try decoding with common encodings until successful or exhausted
            for encoding in ['ascii','latin-1','utf-8','shift-jis']: # Try common encodings
                 try:
                      decoded_name = filename_bytes.split(b'\x00',1)[0].decode(encoding)
                      if decoded_name: # Ensure not empty
                           # Important: Keep original separators (\ and /)
                           name = decoded_name
                           break # Success
                 except UnicodeDecodeError: continue
                 except Exception: continue # Catch other potential errors
    except Exception: name = "decode_error_unknown" # Catch any unexpected errors during name decoding

    # Look up extension hash in the loaded EXTENSION_MAP. Provide default if hash not found.
    hash_val = file_info.get("ext_hash", 0)
    ext = EXTENSION_MAP.get(hash_val, f".{hash_val:08X}") # Use hash if not found in map

    # Return the potentially path-containing name + extension
    return name + ext

def get_calculated_uncompressed_size(file_info):
    """Calculates the effective uncompressed size based on platform logic. Returns None if raw size is invalid."""
    p=file_info.get("platform", Platform.UNKNOWN); # Defensive get
    u=file_info.get("uncompressed_size_raw") # Defensive get

    if u is None: return None # Cannot calculate if raw size is None

    # Cast raw size to int before bitwise ops if it might be other type
    try: u = int(u)
    except (ValueError, TypeError):
         print(f"Warning: Raw uncompressed size is not an integer ({u}). Cannot calculate.", file=sys.stderr)
         return None # Cannot calculate if raw size is not a number

    if u < 0:
         # Negative raw size indicates potential corruption or unusual format
         print(f"Warning: Negative raw uncompressed size ({u}). Cannot calculate meaningful size.", file=sys.stderr)
         return None

    # Use PC logic for UNKNOWN to match default platform guess.
    if p == Platform.UNKNOWN: p = DEFAULT_PLATFORM

    # Strictly follow C# logic based on Platform enum
    if p == Platform.CTR: return u & 0x00FFFFFF
    elif p == Platform.Switch: return u
    elif p == Platform.PS3 or p == Platform.PC: return u >> 3
    # For any other unexpected Platform value, fallback?
    print(f"Warning: Unknown platform {p} for size calculation. Returning raw value.", file=sys.stderr)
    return u # Fallback to raw value for unknown platforms


def calculate_arc_hash(s:str)->int:
    """Calculates the MT Framework ARC extension hash (ported from C#)."""
    if not isinstance(s, str):
        print(f"Warning: Input to calculate_arc_hash is not a string ({type(s).__name__}). Treating as empty.", file=sys.stderr)
        return 0
    if not s: return 0 # Handle empty input string
    try:b=s.encode('ascii')
    except UnicodeEncodeError:
        # Log warning for non-ASCII, use utf-8 ignore as fallback
        print(f"Warning: Non-ASCII characters in hash input '{s}'. Using UTF-8 ignore.", file=sys.stderr)
        b=s.encode('utf-8',errors='ignore')
    h=0xFFFFFFFF;poly=0xEDB88320 # CRC32 polynomial
    for bv in b:
        for i in range(8):
            # Bitwise operations matching C# logic
            bit = (bv >> i) & 1 # Get bit
            xor_val = poly if (bit ^ (h & 1)) else 0
            h = (h >> 1) ^ xor_val
    return h&0xFFFFFFFF # Mask to ensure 32-bit unsigned

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

# calculate_padding is internal

def compress_kontract_zlib(data, level=ZLIB_COMPRESSION_LEVEL):
    """Compresses data using standard Deflate with Kontract's 0x78 0xDA header and Adler32 footer."""
    if not isinstance(data, bytes):
         raise TypeError("Input to compress_kontract_zlib must be bytes.")
    if not data: return b'' # Handle empty data

    try:
        # Use wbits=-zlib.MAX_WBITS for raw deflate stream (no zlib header/checksum)
        # level should be -1 to 9 (default is 6). Kontract uses Optimal (usually 9).
        # Ensure level is within range
        actual_level = max(-1, min(9, level))
        compressed_core=zlib.compress(data,level=actual_level,wbits=-zlib.MAX_WBITS)
        checksum=zlib.adler32(data)&0xFFFFFFFF # Ensure unsigned 32-bit
        header=b'\x78\xda';footer=checksum.to_bytes(4,byteorder='big'); return header+compressed_core+footer
    except Exception as e:
         # Catch zlib errors or other issues
         raise RuntimeError(f"Kontract Zlib compression failed: {e}") from e


def decompress_kontract_zlib(compressed_data):
    """Decompresses data assuming Kontract's Zlib header (0x78) and trailer (4 bytes) format."""
    if not isinstance(compressed_data, bytes):
         raise TypeError("Input to decompress_kontract_zlib must be bytes.")
    if len(compressed_data) < 6: # Need at least 2 byte header + 4 byte footer
         # Data is too short to potentially be Kontract Zlib, treat as uncompressed
         print(f"Warning: Data size ({len(compressed_data)}) is less than Kontract Zlib minimum (6 bytes). Skipping decompression.", file=sys.stderr)
         return compressed_data # Return data as is

    # Check header (Kontract checks 0x78 implicitly/explicitly)
    # If the header is missing or wrong, it's likely not Kontract Zlib
    if not compressed_data.startswith(b'\x78'):
         print(f"Warning: Data does not start with expected Kontract Zlib header (0x78). Skipping decompression.", file=sys.stderr)
         return compressed_data # Return data as is

    # Extract core data (skip 2-byte header, 4-byte footer)
    core_data=compressed_data[2:-4]
    # Handle empty core data explicitly (header+footer only, implies empty uncompressed)
    if not core_data: return b''

    try:
        # Use wbits=-zlib.MAX_WBITS for raw deflate decompression
        return zlib.decompress(core_data,wbits=-zlib.MAX_WBITS)
    except zlib.error as e:
        # Fallback to standard zlib decompression if raw deflate fails
        print(f"Warning: Raw deflate decompression failed ({e}), trying standard zlib...",file=sys.stderr)
        try: return zlib.decompress(compressed_data) # Standard zlib expects header/checksum
        except zlib.error as e2:
             # Both methods failed, decompression truly failed
             raise RuntimeError(f"Standard zlib decompression also failed: {e2}. Data may be corrupt or not zlib.") from e2
    except Exception as e:
         # Catch any other unexpected error during decompression
         raise RuntimeError(f"Unexpected decompression error: {e}") from e


# --- MT Framework Blowfish Crypto Wrapper (using pycryptodome) ---
class MTBlowfishCrypto:
    """Wraps pycryptodome Blowfish to mimic Kontract.Encryption.BlowFish with MTMethod."""
    def __init__(self, key: bytes):
        # Validate key length
        if not isinstance(key, bytes) or len(key) < 1 or len(key) > 56:
             raise ValueError(f"Invalid Blowfish key ({type(key).__name__}, {len(key) if isinstance(key, (bytes, bytearray)) else 'N/A'} bytes). Must be bytes 1-56 bytes.")
        self.key = key
        self.mt_method = True # Hardcoded based on MTFramework.cs usage

    def _swap_block_endian(self, block_64bit: bytes) -> bytes:
        """Swaps the two 4-byte halves of an 8-byte block (LLLLRRRR -> RRRRLLLL)."""
        if not isinstance(block_64bit, bytes) or len(block_64bit) != 8:
            # This should ideally not happen if handling full blocks
            raise ValueError(f"Attempted to swap endian on non-8-byte block (type {type(block_64bit).__name__}, size {len(block_64bit) if isinstance(block_64bit, (bytes, bytearray)) else 'N/A'}).")
        return block_64bit[4:] + block_64bit[:4]

    # Note: _pad_data is handled internally by encrypt_ecb now to simplify caller logic

    def encrypt_ecb(self, data: bytes) -> bytes:
        """Encrypts data in ECB mode, applying MTMethod byte swapping and null padding."""
        if not isinstance(data, bytes):
             raise TypeError("Input to encrypt_ecb must be bytes.")
        if not data: return b'' # Handle empty data

        # Blowfish ECB requires data length to be a multiple of 8 bytes (block size)
        block_size = 8
        original_len = len(data)
        pad_len = (block_size - (original_len % block_size)) % block_size
        padded_data = data + (b'\x00' * pad_len) # Apply null padding

        # This should be impossible with correct padding logic, but defensive check
        if len(padded_data) % block_size != 0:
             raise RuntimeError("Internal error: Padded data length is not a multiple of 8.")

        try:
            cipher = Blowfish.new(self.key, Blowfish.MODE_ECB)
            encrypted_data = bytearray()

            # Process in 8-byte blocks
            for i in range(0, len(padded_data), block_size):
                block = padded_data[i:i+block_size]
                if self.mt_method:
                    block = self._swap_block_endian(block) # Swap before encrypting
                # pycryptodome's encrypt expects 8 bytes
                encrypted_block = cipher.encrypt(block)
                if self.mt_method:
                    encrypted_block = self._swap_block_endian(encrypted_block) # Swap after encrypting
                encrypted_data.extend(encrypted_block)

            # The size of the encrypted data is the size of the padded input data
            return bytes(encrypted_data)

        except Exception as e:
            # Catch potential errors during encryption (e.g. bad key state, library issues)
            raise RuntimeError(f"Blowfish encryption failed: {e}") from e


    def decrypt_ecb(self, data: bytes) -> bytes:
        """Decrypts data in ECB mode, applying MTMethod byte swapping."""
        if not isinstance(data, bytes):
             raise TypeError("Input to decrypt_ecb must be bytes.")
        if not data: return b'' # Handle empty data

        # We can only decrypt full 8-byte blocks. If input is not a multiple of 8, process only full blocks.
        block_size = 8
        processed_len = len(data) - (len(data) % block_size)

        if processed_len <= 0 and len(data) > 0:
             # Data exists but is less than block size, cannot decrypt
             print(f"Warning: Data chunk size ({len(data)} bytes) is less than Blowfish block size ({block_size} bytes). Cannot decrypt, returning raw data.", file=sys.stderr)
             return data # Cannot decrypt, return as is
        if processed_len <= 0: # Input data was empty or less than block size
             return data # Return empty data

        try:
            cipher = Blowfish.new(self.key, Blowfish.MODE_ECB)
            decrypted_padded_data = bytearray()

            # Process in 8-byte blocks up to processed_len
            for i in range(0, processed_len, block_size):
                block = data[i:i+block_size]
                if self.mt_method:
                    block = self._swap_block_endian(block) # Swap before decrypting
                # pycryptodome's decrypt expects 8 bytes
                decrypted_block = cipher.decrypt(block)
                if self.mt_method:
                    decrypted_block = self._swap_block_endian(decrypted_block) # Swap after decrypting
                decrypted_padded_data.extend(decrypted_block)

            # Note: Unpadding/truncation to original size is handled by the caller (MTArc.extract_file)
            # The decrypted_padded_data will have a length that is a multiple of 8 (or 0).
            return bytes(decrypted_padded_data)

        except Exception as e:
             # Catch potential errors during decryption (e.g. bad key, corrupt data, library issues)
             # Log failure but return the raw (undecrypted) data
             print(f"Warning: Blowfish decryption failed: {e}. Returning raw data.", file=sys.stderr)
             return data # Keep the raw data if decryption fails


# --- Main ARC Class ---
class MTArc:
    def __init__(self):
        # Initialize all instance variables explicitly for clarity
        self.hfs_header = None; self.hfs_footer = None; self.arc_header = None
        self.files = []; self.byte_order_char = DEFAULT_BYTE_ORDER_CHAR; self.platform = DEFAULT_PLATFORM
        self.header_length = 0; self.entry_struct_fmt = format_struct(DEFAULT_BYTE_ORDER_CHAR, FMT_ENTRY)
        self.entry_struct_size = SIZE_ENTRY; self.hfs_header_length = 0; self.is_encrypted = False
        self.crypto = None; self._raw_file_path = None; self._decrypted_entries_bytes = None
        self._data_offset = 0; self._file_size = None # Added _file_size


    def _derive_mtf_key(self, key1: str, key2: str) -> bytes:
         """ Derives Blowfish key using the MTFramework method (ported from C#). """
         if not isinstance(key1, str) or not isinstance(key2, str): raise TypeError("Keys not str")
         if len(key1) != len(key2): raise ValueError("Keys unequal len")
         if not key1: return b''
         key1_rev = key1[::-1]; key_bytes = bytearray()
         try:
             for i in range(len(key1_rev)): val = (ord(key1_rev[i]) ^ ord(key2[i])) | (i << 6); key_bytes.append(val & 0xFF)
             return bytes(key_bytes)
         except Exception as e: raise RuntimeError(f"Key derive fail:{e}") from e


    def _setup_encryption(self, key1=None, key2=None):
        """Sets up the crypto object if valid keys are provided."""
        k1p=key1 is not None and key1!="";k2p=key2 is not None and key2!=""
        if k1p!=k2p: raise ValueError("Both keys required or none");
        if k1p and k2p:
            try: 
                dk=self._derive_mtf_key(key1,key2) 
                self.crypto=MTBlowfishCrypto(dk)
                self.is_encrypted=True
            except Exception as e: print(f"ERR:Encrypt init fail:{e}",file=sys.stderr);self.is_encrypted=False;self.crypto=None;raise
        else: self.is_encrypted=False;self.crypto=None


    def load(self, filepath, key1=None, key2=None, status_queue=None): # Allow status_queue for more detailed warnings
        """Loads ARC data from a file, parsing headers, entries, and setting up for extraction."""
        self.files = []; self._raw_file_path = None; self._decrypted_entries_bytes = None; self._data_offset = 0; self._file_size = None

        def _q_status(msg, level): # Helper to send to queue if available
            if status_queue: status_queue.put({'type':'status','msg':msg,'level':level})
            else: print(f"{level.upper()}: {msg}", file=sys.stderr)

        try:
            self._setup_encryption(key1, key2);
            if not os.path.isfile(filepath): raise FileNotFoundError(f"Not found:{filepath}");
            if not os.access(filepath,os.R_OK): raise PermissionError(f"Read denied:{filepath}");
            self._raw_file_path=filepath;
            try: self._file_size=os.path.getsize(filepath) # Store file size
            except Exception as e: raise IOError(f"Size get fail:{filepath}:{e}") from e
            if self._file_size < 4: raise IOError(f"Too small({self._file_size}b)");

            with open(filepath,'rb')as f_raw:
                mb=f_raw.read(4);f_raw.seek(0);self.byte_order_char='>'if mb==MAGIC_ARC_BE or mb==MAGIC_HFS_BE else'<';self.platform=Platform.PS3 if self.byte_order_char=='>'else Platform.PC
                ishfs=mb==MAGIC_HFS_LE or mb==MAGIC_HFS_BE
                if ishfs:
                    hfsfmt=format_struct(self.byte_order_char,FMT_HFS_HEADER);
                    if self._file_size<SIZE_HFS_HEADER: raise IOError("Short HFS hdr")
                    hfb=f_raw.read(SIZE_HFS_HEADER);
                    if len(hfb)<SIZE_HFS_HEADER: raise IOError(f"Incomplete HFS hdr read({len(hfb)}/{SIZE_HFS_HEADER})")
                    try:self.hfs_header=HFSHeader(*struct.unpack(hfsfmt,hfb))
                    except Exception as e:raise IOError(f"Parse HFS hdr fail:{e}")from e
                    self.hfs_header_length=0x20000 if self.hfs_header.type==0 else 0x10;epah=f_raw.tell()+self.hfs_header_length
                    if epah>self._file_size:raise IOError(f"Short HFS data({self.hfs_header_length}b)");f_raw.seek(self.hfs_header_length,io.SEEK_CUR)
                else:self.hfs_header=None;self.hfs_header_length=0
                rah=self._file_size-f_raw.tell()
                if rah<SIZE_HEADER_COMMON:raise IOError(f"Short ARC hdr({SIZE_HEADER_COMMON}b exp,{rah}b rem)");
                hcf=format_struct(self.byte_order_char,FMT_HEADER_COMMON);hb=f_raw.read(SIZE_HEADER_COMMON)
                if len(hb)<SIZE_HEADER_COMMON:raise IOError(f"Incomplete ARC hdr read({len(hb)}/{SIZE_HEADER_COMMON})")
                try:self.arc_header=ARCHeader(*struct.unpack(hcf,hb))
                except Exception as e:raise IOError(f"Parse ARC hdr fail:{e}")from e
                eam=MAGIC_ARC_BE if self.byte_order_char=='>'else MAGIC_ARC_LE;eam2=MAGIC_ARCC_LE if self.byte_order_char=='<'else b'';
                if self.arc_header.magic not in[eam,eam2]and not ishfs:_q_status(f"W:Unusual ARC magic:{self.arc_header.magic!r}",STATUS_WARN)
                self.header_length=SIZE_HEADER_COMMON;v=self.arc_header.version
                if self.byte_order_char=='>':self.platform=Platform.PS3
                elif v==9:self.platform=Platform.Switch;self.entry_struct_fmt=format_struct('<',FMT_ENTRY_SWITCH);self.entry_struct_size=SIZE_ENTRY_SWITCH
                elif v==7:self.platform=Platform.PC;self.entry_struct_fmt=format_struct('<',FMT_ENTRY);self.entry_struct_size=SIZE_ENTRY
                else:self.platform=Platform.PC;self.entry_struct_fmt=format_struct('<',FMT_ENTRY);self.entry_struct_size=SIZE_ENTRY
                if self.byte_order_char=='<'and v not in[7,9]:
                    if f_raw.tell()+SIZE_HEADER_PC_EXTRA<=self._file_size:f_raw.read(SIZE_HEADER_PC_EXTRA);self.header_length+=SIZE_HEADER_PC_EXTRA
                    else:_q_status(f"W:Exp pad v{v} LE, file short.",STATUS_WARN)
                mre=1000000;ec=self.arc_header.entry_count
                if ec is None or not isinstance(ec,int)or ec<0 or ec>mre:raise ValueError(f"Invalid entries({ec}).Corrupt?");
                emsu=ec*self.entry_struct_size;rahs=self._file_size-f_raw.tell();etp=ec
                if rahs<emsu:
                    _q_status(f"W:File short metadata({emsu}b exp,{rahs}b rem).Partial read.",STATUS_WARN);
                    mbrr=rahs-(rahs%self.entry_struct_size);etp=mbrr//self.entry_struct_size if self.entry_struct_size>0 else 0
                    if etp==0 and ec>0:raise IOError("File too short for 1 entry.")
                    _q_status(f"W:Will read {etp} entries.",STATUS_WARN)
                else:mbrr=emsu
                mbr=f_raw.read(mbrr);
                if len(mbr)!=mbrr:raise IOError(f"Incomplete metadata read({len(mbr)}/{mbrr})");
                mbd=mbr
                if self.is_encrypted and self.crypto:
                    try:mbd=self.crypto.decrypt_ecb(mbr)
                    except Exception as e:_q_status(f"W:Meta decrypt fail:{e}.Parsing raw.",STATUS_WARN);mbd=mbr
                self._decrypted_entries_bytes=mbd;bap=len(self._decrypted_entries_bytes);netp=bap//self.entry_struct_size if self.entry_struct_size>0 else 0
                if netp<etp:_q_status(f"W:Only {netp} entries fit decrypted meta.Hdr said {ec}.",STATUS_WARN)
                for i in range(netp):
                    eso=i*self.entry_struct_size;eeo=eso+self.entry_struct_size
                    if bap<eeo:_q_status(f"W:Meta block short parse.Cannot parse e{i+1}+.",STATUS_WARN);break
                    ed=self._decrypted_entries_bytes[eso:eeo];fi=create_file_info();fi["platform"]=self.platform
                    try:
                        up=struct.unpack(self.entry_struct_fmt,ed)
                        if self.platform==Platform.Switch:fi.update(zip(["filename_base","ext_hash","compressed_size","uncompressed_size_raw","unknown1","offset"],up))
                        else:fi.update(zip(["filename_base","ext_hash","compressed_size","uncompressed_size_raw","offset"],up));fi["unknown1"]=None
                        csz=fi.get("compressed_size");calcsz=get_calculated_uncompressed_size(fi);fi["is_compressed"]=True if(self.platform==Platform.Switch and csz is not None and csz>0)or(csz is not None and calcsz is not None and csz>0 and csz!=calcsz)else False
                        fi["full_filename"]=get_full_filename(fi);fi["calculated_uncompressed_size"]=calcsz
                        if csz is None or not isinstance(csz,int)or csz<0:_q_status(f"W:File'{fi['full_filename']}'e{i+1} invalid comp size({csz}).Skip.",STATUS_WARN);continue
                        if calcsz is not None and calcsz<0:_q_status(f"W:File'{fi['full_filename']}'e{i+1} neg uncomp size({calcsz}).",STATUS_WARN)
                        offset_val=fi.get("offset");
                        if offset_val is None or not isinstance(offset_val,int)or offset_val<0:_q_status(f"W:File'{fi['full_filename']}'e{i+1} invalid offset({offset_val}).Skip.",STATUS_WARN);continue
                        data_end_potential=offset_val+csz;arc_section_size=self._file_size-self.hfs_header_length
                        if data_end_potential>arc_section_size:_q_status(f"W:File'{fi['full_filename']}'e{i+1} data end({data_end_potential})>ARC end({arc_section_size}).Read partial?",STATUS_WARN)
                        self.files.append(fi)
                    except Exception as e:_q_status(f"Err parse entry{i+1}data:{e}.Skip.",STATUS_WARN)
                if len(self.files)<ec:_q_status(f"W:Parsed {len(self.files)}/{ec} entries due to issues.",STATUS_WARN)
                self._data_offset=0
                if self.files:self._data_offset=self.files[0].get("offset",0)
                dsap=self.hfs_header_length+self._data_offset;capmb=f_raw.tell()
                if dsap<capmb and len(self.files)>0:_q_status(f"W:Data offset({self._data_offset},abs{dsap})in meta(ends near{capmb}).",STATUS_WARN)
                if dsap>self._file_size:_q_status(f"W:Data offset({self._data_offset},abs{dsap})>file end({self._file_size}).Extract fail.",STATUS_WARN)
        except (FileNotFoundError,PermissionError,IOError,ValueError,RuntimeError)as e:raise e
        except Exception as e:raise IOError(f"Load fail {os.path.basename(filepath)}:{e}")from e

    def extract_file(self, file_info, input_arc_path):
        if not self._raw_file_path or self._raw_file_path!=input_arc_path or self._file_size is None:raise RuntimeError(f"MTArc state invalid for '{file_info.get('full_filename','?')}'.Load fail for {os.path.basename(input_arc_path)}?")
        try:offset=int(file_info.get("offset",0));hfs_len=int(self.hfs_header_length);d_off=offset+hfs_len
        except Exception as e:raise ValueError(f"Invalid offset/HFS len '{file_info.get('full_filename','?')}':{e}")from e
        rs=file_info.get("compressed_size");raw=b''
        if rs is None or not isinstance(rs,int)or rs<0:print(f"W:Skip extract '{file_info.get('full_filename','?')}'invalid comp size({rs}).",file=sys.stderr);return b''
        if rs==0:return b''
        fs=self._file_size;
        try:
            with open(self._raw_file_path,'rb')as f:
                if fs>=0 and(d_off<0 or d_off>fs):print(f"W:Offset {d_off} for '{file_info.get('full_filename','?')}' out bounds({fs}).Skip.",file=sys.stderr);return b''
                ars=rs
                if fs>=0 and d_off+rs>fs:print(f"W:Read size {rs} from {d_off} for '{file_info.get('full_filename','?')}' > file end({fs}).Reading til EOF.",file=sys.stderr);ars=fs-d_off;ars=max(0,ars)
                if ars>0:f.seek(d_off);raw=f.read(ars)
            if len(raw)!=ars:print(f"W:Read size mismatch '{file_info.get('full_filename','?')}':Exp {ars},got {len(raw)}.",file=sys.stderr)
        except Exception as e:raise IOError(f"Read fail raw data '{file_info.get('full_filename','?')}'off{d_off}size{rs}:{e}")from e
        dec=raw
        if self.is_encrypted:
            if not self.crypto:print(f"ERR:Encrypt flag but no crypto '{file_info.get('full_filename','?')}'.",file=sys.stderr)
            else:
                try:dec=self.crypto.decrypt_ecb(raw)
                except Exception as e:print(f"W:Blowfish decrypt fail '{file_info.get('full_filename','?')}:{e}'.Raw data.",file=sys.stderr);dec=raw
        fin=dec
        if file_info.get("is_compressed"):
            if not dec:fin=b''
            else:
                try:fin=decompress_kontract_zlib(dec)
                except Exception as e:print(f"W:Zlib decomp fail '{file_info.get('full_filename','?')}':{e}.Pre-decomp data.",file=sys.stderr);fin=dec
        else:fin=dec
        expsz=file_info.get("calculated_uncompressed_size");actsz=len(fin)
        if expsz is None or not isinstance(expsz,int)or expsz<0:print(f"W:Invalid exp uncomp size({expsz})'{file_info.get('full_filename','?')}'.No truncate.",file=sys.stderr)
        elif actsz>expsz:fin=fin[:expsz] # Truncate excess
        # elif actsz<expsz: print(f"W:Final size {actsz} < exp {expsz} '{file_info.get('full_filename','?')}'.Incomplete?",file=sys.stderr) # Warning removed
        return fin

    def save(self, output_path, input_file_infos, key1=None, key2=None):
        if not input_file_infos:raise ValueError("No files");
        if not isinstance(input_file_infos,list):raise TypeError("input_file_infos not list");
        try:
            self._setup_encryption(key1,key2); 
            self.platform=Platform.Switch;self.byte_order_char='<';v=9;self.entry_struct_fmt=format_struct('<',FMT_ENTRY_SWITCH);self.entry_struct_size=SIZE_ENTRY_SWITCH;self.header_length=SIZE_HEADER_COMMON;
            initial_ec=len(input_file_infos);ds=io.BytesIO();updated_file_infos=[];
            temp_md_size=initial_ec*self.entry_struct_size;temp_md_end=self.header_length+temp_md_size;al=ALIGNMENT_SWITCH;temp_data_start=(temp_md_end+al-1)&~(al-1);
            cdo=temp_data_start
            for idx,fi in enumerate(input_file_infos):
                if not isinstance(fi,dict):print(f"W:Skip invalid item {idx} (not dict).",file=sys.stderr);continue
                od=fi.get("data");fn=fi.get("full_filename","unknown file")
                if od is None:print(f"W:No data key '{fn}'.Empty.",file=sys.stderr);od=b''
                elif not isinstance(od,bytes):print(f"W:Data not bytes '{fn}'({type(od).__name__}).Empty.",file=sys.stderr);od=b''
                us=len(od);cd=b'';dtw=b''
                if us>0:
                    try:cd=compress_kontract_zlib(od)
                    except Exception as e:print(f"ERR:Zlib compress fail '{fn}':{e}.Store raw.",file=sys.stderr);cd=od
                dtw=cd
                if self.is_encrypted:
                    if not self.crypto:raise RuntimeError("Encrypt but no crypto");
                    try:dtw=self.crypto.encrypt_ecb(dtw)
                    except Exception as e:print(f"ERR:Blowfish encrypt data fail '{fn}':{e}.Store plain.",file=sys.stderr);dtw=cd
                fi_to_save=fi.copy();fi_to_save["offset"]=cdo;fi_to_save["compressed_size"]=len(dtw);fi_to_save["uncompressed_size_raw"]=us;fi_to_save["unknown1"]=fi_to_save.get("unknown1",0);
                try:ds.write(dtw)
                except Exception as e:raise IOError(f"Write temp stream fail '{fn}':{e}")from e
                cdo+=len(dtw);updated_file_infos.append(fi_to_save)
            try:
                output_p=pathlib.Path(output_path);output_p.parent.mkdir(parents=True,exist_ok=True)
                with open(output_p,'wb')as f:
                    f.write(b'\x00'*self.header_length);mdb_plain=bytearray();packed_entry_count=0
                    for fi in updated_file_infos:
                        packed_name_bytes = fi.get("filename_base") 
                        fn_display = fi.get("full_filename","?") 

                        if not isinstance(packed_name_bytes, bytes) or len(packed_name_bytes) != 64:
                            print(f"W: filename_base for '{fn_display}' not pre-formatted or missing. Re-deriving from full_filename.", file=sys.stderr)
                            base_name_for_arc_str = os.path.splitext(fn_display)[0]
                            try: 
                                fnb_enc = base_name_for_arc_str.encode('ascii')
                            except UnicodeEncodeError: 
                                fnb_enc = base_name_for_arc_str.encode('utf-8', errors='ignore')
                            packed_name_bytes = fnb_enc[:64].ljust(64, b'\x00')
                        
                        ev=(packed_name_bytes, 
                            fi.get("ext_hash",0),
                            fi.get("compressed_size",0),
                            fi.get("uncompressed_size_raw",0),
                            fi.get("unknown1",0),
                            fi.get("offset",0))
                        
                        if ev[2]is None or not isinstance(ev[2],int)or ev[2]<0 or ev[5]is None or not isinstance(ev[5],int)or ev[5]<0:print(f"W:Skip pack entry '{fn_display}':Invalid size({ev[2]})or offset({ev[5]}).",file=sys.stderr);continue
                        try:packed_entry=struct.pack(self.entry_struct_fmt,*ev);mdb_plain.extend(packed_entry);packed_entry_count+=1
                        except Exception as e:print(f"ERR:Pack entry fail '{fn_display}':{e}.Skip.",file=sys.stderr)
                    mdr=bytes(mdb_plain);mtw=mdr;
                    if self.is_encrypted:
                        if not self.crypto:raise RuntimeError("Encrypt but no crypto");
                        try:mtw=self.crypto.encrypt_ecb(mdr)
                        except Exception as e:print(f"ERR:Blowfish encrypt meta fail:{e}.Store plain.",file=sys.stderr);mtw=mdr
                    f.write(mtw);
                    meta_end_actual=self.header_length+len(mtw);data_start_actual=(meta_end_actual+al-1)&~(al-1);
                    pad=data_start_actual-f.tell();
                    if pad<0:raise RuntimeError(f"Internal ERR:Data start({data_start_actual})<meta end({f.tell()})");
                    if pad>0:f.write(b'\x00'*pad)
                    if f.tell()!=data_start_actual:raise RuntimeError(f"Internal ERR:Stream pos({f.tell()})!=data start({data_start_actual})")
                    f.write(ds.getvalue());f.seek(0)
                    f.write(struct.pack(format_struct(self.byte_order_char,FMT_HEADER_COMMON),MAGIC_ARC_LE,v,packed_entry_count)) # Use final count
            except Exception as e:
                print(f"ERR:Write output fail {output_path}:{e}",file=sys.stderr);
                if os.path.exists(output_path):
                    try:os.remove(output_path)
                    except Exception as ce:print(f"W:Cleanup fail {output_path}:{ce}",file=sys.stderr)
                raise RuntimeError(f"Save fail {os.path.basename(output_path)}:{e}")from e
        except Exception as e:raise RuntimeError(f"Save prepare fail:{e}")from e
    def close(self):pass


# --- BATCH OPERATIONS (Workers and Orchestrators) ---

# Worker for single file/folder based extraction
# _list_extract_worker(arc_path_str, output_base_dir_str, key1, key2, status_queue)
def _list_extract_worker(arc_path_str: str, output_base_dir_str: str | None, key1: str | None, key2: str | None, status_queue: queue.Queue):
    """
    Worker to extract a single ARC file.
    Output folder will be created in the same directory as arc_path_str, named <arc_stem>_arc.
    output_base_dir_str is ignored by this worker.
    """
    arc_path = pathlib.Path(arc_path_str)
    # output_base_dir_str is ignored; output is relative to arc_path.
    arc = None 

    try:
        arc_filename = arc_path.name
        arc_basename = arc_path.stem
        # MODIFIED: Output folder is next to the source ARC file
        output_folder = arc_path.parent / f"{arc_basename}_arc"


        status_queue.put({'type': 'status', 'msg': f"Loading {arc_filename}...", 'level': STATUS_DEBUG})

        arc = MTArc()
        arc.load(str(arc_path), key1=key1, key2=key2, status_queue=status_queue)

        try: output_folder.mkdir(parents=True, exist_ok=True)
        except Exception as e:
             raise IOError(f"Failed to create output folder {output_folder}: {e}") from e
        if not os.access(output_folder, os.W_OK):
            raise PermissionError(f"Write permission denied for output folder: {output_folder}")


        platform_name = Platform(arc.platform).name if isinstance(arc.platform, Platform) else f"Platform {arc.platform}"
        status_queue.put({'type': 'status', 'msg': f" Extracting {len(arc.files)} files from {platform_name} ARC {arc_filename} to ./{output_folder.relative_to(arc_path.parent)}...", 'level': STATUS_INFO})


        processed_count = 0
        error_count = 0
        for file_info in arc.files:
            if not isinstance(file_info, dict) or "full_filename" not in file_info or "offset" not in file_info or "compressed_size" not in file_info:
                 status_queue.put({'type':'status','msg':f"  Skipping invalid file info in {arc_filename}: {file_info!r}",'level':STATUS_WARN})
                 error_count += 1 
                 continue 

            try:
                file_data = arc.extract_file(file_info, str(arc_path)) 

                relative_file_path_str = file_info.get("full_filename", "") 
                safe_components = []
                for component in pathlib.Path(relative_file_path_str).parts:
                    safe_comp = component.replace(':', '_').replace('\x00', '').replace('..', '__')
                    safe_comp = safe_comp.replace('<', '_').replace('>', '_').replace('"', '_').replace('|', '_').replace('?', '_').replace('*', '_').replace('/', '_').replace('\\', '_')
                    if safe_comp:
                         safe_components.append(safe_comp)

                if not safe_components:
                     status_queue.put({'type':'status','msg':f"  Skipping entry with invalid/empty derived filename in {arc_filename}",'level':STATUS_WARN})
                     error_count += 1
                     continue

                output_file_path = output_folder.joinpath(*safe_components)
                output_file_path.parent.mkdir(parents=True, exist_ok=True)

                with open(output_file_path, 'wb') as out_f: out_f.write(file_data)
                processed_count += 1

            except OSError as e: 
                 status_queue.put({'type': 'status', 'msg': f"  OS Error writing '{file_info.get('full_filename','?')}' from {arc_filename}: {e}", 'level': STATUS_ERROR})
                 status_queue.put({'type':'status','msg':f"  Trace: {traceback.format_exc()}",'level':STATUS_DEBUG}) 
                 error_count += 1
            except Exception as e:
                status_queue.put({'type': 'status', 'msg': f"  Error extracting '{file_info.get('full_filename','?')}' from {arc_filename}: {e}", 'level': STATUS_ERROR})
                status_queue.put({'type':'status','msg':f"  Trace: {traceback.format_exc()}",'level':STATUS_DEBUG}) 
                error_count += 1

        if processed_count > 0 and error_count == 0:
            status_queue.put({'type': 'status', 'msg': f"Finished extracting {arc_filename} ({processed_count} files)", 'level': STATUS_SUCCESS})
            return arc_filename, True 
        elif processed_count > 0 and error_count > 0:
            status_queue.put({'type': 'status', 'msg': f"Finished extracting {arc_filename} with errors ({processed_count} successful, {error_count} failed)", 'level': STATUS_WARN})
            return arc_filename, False 
        elif error_count > 0:
             status_queue.put({'type': 'status', 'msg': f"Failed to extract any files from {arc_filename} ({error_count} errors)", 'level': STATUS_ERROR})
             return arc_filename, False 
        else: 
             status_queue.put({'type': 'status', 'msg': f"No files found in {arc_filename}.", 'level': STATUS_INFO})
             return arc_filename, True 


    except (FileNotFoundError, PermissionError, IOError, ValueError, RuntimeError) as e:
         status_queue.put({'type':'status','msg':f"Failed loading/processing ARC {arc_path.name}: {e}",'level':STATUS_ERROR}); return arc_path.name,False
    except Exception as e:
        status_queue.put({'type': 'status', 'msg': f"An unexpected error occurred processing ARC {arc_path.name}: {e}", 'level': STATUS_ERROR})
        status_queue.put({'type':'status','msg':f"Trace: {traceback.format_exc()}",'level':STATUS_DEBUG}) 
        return arc_path.name, False 

    finally:
        if arc: arc.close()


# Worker for single folder based injection
# _list_inject_worker(source_folder_str, output_rebuilt_dir_str, key1, key2, status_queue, target_arc_filename_override=None)
# Also used for Folder Inject Dir
def _list_inject_worker(source_folder_str: str, output_rebuilt_dir_str: str | None, 
                        key1: str | None, key2: str | None, status_queue: queue.Queue,
                        target_arc_filename_override: str | None = None):
    """Worker to rebuild a single ARC from a source folder (scans recursively)."""
    source_folder_path = pathlib.Path(source_folder_str)
    
    if not output_rebuilt_dir_str:
        status_queue.put({'type':'status','msg':f"Output directory for rebuild not provided for {source_folder_path.name}.", 'level':STATUS_ERROR})
        return source_folder_path.name, False 
    output_rebuilt_dir = pathlib.Path(output_rebuilt_dir_str)
    arc = None 

    try:
        folder_name_raw = source_folder_path.name 
        arc_base_name = folder_name_raw
        if folder_name_raw.endswith("_arc"):
            arc_base_name = folder_name_raw[:-4]

        if target_arc_filename_override:
            output_arc_path = output_rebuilt_dir / target_arc_filename_override
        else:
            output_arc_path = output_rebuilt_dir / f"{arc_base_name}.arc"


        status_queue.put({'type': 'status', 'msg': f"Processing folder {folder_name_raw} for rebuild as {output_arc_path.name}...", 'level': STATUS_DEBUG})

        files_to_pack = []
        has_files_in_folder = False 
        error_reading_files = False 

        try:
            if not source_folder_path.is_dir():
                 raise FileNotFoundError(f"Source folder not found: {source_folder_path.name}")
            if not os.access(source_folder_path, os.R_OK):
                 raise PermissionError(f"Read permission denied for folder: {source_folder_path.name}")

            for root_str, _, files_in_dir in os.walk(source_folder_path):
                root_path = pathlib.Path(root_str)
                for filename_leaf in files_in_dir:
                    has_files_in_folder = True 
                    file_path_obj = root_path / filename_leaf
                    
                    if not os.access(str(file_path_obj), os.R_OK):
                        status_queue.put({'type':'status','msg':f"  Permission denied reading file {file_path_obj.relative_to(source_folder_path)} in {folder_name_raw}. Skipping.",'level':STATUS_ERROR})
                        error_reading_files = True
                        continue
                    
                    try:
                        with open(file_path_obj, 'rb') as f: data = f.read()
                        
                        fi = create_file_info()
                        
                        relative_arc_path = file_path_obj.relative_to(source_folder_path)
                        arc_internal_filename = relative_arc_path.as_posix() # Use forward slashes

                        fi["full_filename"] = arc_internal_filename 

                        base_for_arc, ext_for_arc_with_dot = os.path.splitext(arc_internal_filename) # ext_for_arc_with_dot e.g. ".tex" or ".ABCD1234"
                        
                        try:
                            fnb_encoded_str = base_for_arc.encode('ascii')
                        except UnicodeEncodeError:
                            fnb_encoded_str = base_for_arc.encode('utf-8', errors='ignore')
                        
                        fi["filename_base"] = fnb_encoded_str[:64].ljust(64,b'\x00')

                        # --- Determine ext_hash ---
                        assigned_hash = None
                        # 1. Try REV_EXTENSION_MAP (for friendly extensions like .tex -> hash)
                        if ext_for_arc_with_dot.lower() in REV_EXTENSION_MAP:
                            assigned_hash = REV_EXTENSION_MAP[ext_for_arc_with_dot.lower()]
                        else:
                            # 2. Check if the extension string (without dot) is an 8-char hex hash
                            potential_hash_str_from_ext = ext_for_arc_with_dot[1:] # Remove leading dot
                            if len(potential_hash_str_from_ext) == 8:
                                try:
                                    assigned_hash = int(potential_hash_str_from_ext, 16)
                                except ValueError:
                                    pass # Not a valid hex string, will fall through

                            if assigned_hash is None:
                                # 3. Fallback: calculate hash of the extension string itself (e.g. "foo" for ".foo", or "ABCD1234" if it wasn't valid hex)
                                # For calculate_arc_hash, we pass the string without the dot.
                                assigned_hash = calculate_arc_hash(potential_hash_str_from_ext)
                        
                        fi["ext_hash"] = assigned_hash
                        # --- End ext_hash determination ---
                        
                        fi["data"] = data
                        fi["platform"] = Platform.Switch 
                        fi["unknown1"] = 0 

                        if len(data) > 0x7FFFFFFF: 
                             status_queue.put({'type':'status','msg':f"  Warning: File {arc_internal_filename} is very large ({len(data)} bytes), may exceed max size supported by ARC entry metadata.",'level':STATUS_WARN})
                        files_to_pack.append(fi)

                    except Exception as e:
                        status_queue.put({'type':'status','msg':f"  Error processing file {file_path_obj.relative_to(source_folder_path)} from {folder_name_raw}:{e}",'level':STATUS_ERROR})
                        status_queue.put({'type':'status','msg':f"  Trace: {traceback.format_exc()}",'level':STATUS_DEBUG})
                        error_reading_files = True

        except (FileNotFoundError, PermissionError) as e:
             status_queue.put({'type':'status','msg':f"Error accessing input folder {folder_name_raw}: {e}",'level':STATUS_ERROR}); return folder_name_raw,False
        except Exception as e: 
            status_queue.put({'type':'status','msg':f"An unexpected error occurred scanning folder {folder_name_raw}: {e}",'level':STATUS_ERROR});
            status_queue.put({'type':'status','msg':f"Trace: {traceback.format_exc()}",'level':STATUS_DEBUG});
            return folder_name_raw,False 

        if not has_files_in_folder: 
            status_queue.put({'type':'status','msg':f"Skipping empty folder (no files found): {folder_name_raw}",'level':STATUS_WARN}); return folder_name_raw,False # Return source folder name for consistency
        if not files_to_pack and has_files_in_folder : 
            status_queue.put({'type':'status','msg':f"Skipping folder {folder_name_raw} as no files were successfully processed for packing.",'level':STATUS_ERROR}); return folder_name_raw,False
        
        if error_reading_files and files_to_pack: 
             status_queue.put({'type': 'status', 'msg': f"Warning: Some files in {folder_name_raw} had read errors and were skipped.", 'level': STATUS_WARN})
        elif error_reading_files and not files_to_pack: 
             status_queue.put({'type': 'status', 'msg': f"All files in {folder_name_raw} had read errors. Skipping rebuild.", 'level': STATUS_ERROR})
             return folder_name_raw, False


        try: files_to_pack.sort(key=lambda fi_sort: fi_sort.get("full_filename", "")) 
        except Exception as e:
             print(f"Warning: Failed to sort files for folder {folder_name_raw}: {e}", file=sys.stderr)
             status_queue.put({'type':'status','msg':f"Warning: Failed to sort files for {folder_name_raw}.",'level':STATUS_WARN})

        status_queue.put({'type':'status','msg':f" Rebuilding {output_arc_path.name} ({len(files_to_pack)} files){' (Encrypted)' if key1 and key2 else ''}...",'level':STATUS_INFO})
        arc = MTArc(); 

        try: output_rebuilt_dir.mkdir(parents=True, exist_ok=True)
        except Exception as e:
             raise IOError(f"Failed to create output directory {output_rebuilt_dir}: {e}") from e

        if output_arc_path.exists():
            if not os.access(output_arc_path, os.W_OK):
                 raise PermissionError(f"Write permission denied for existing output file: {output_arc_path.name}")
        elif not output_arc_path.parent.exists(): 
            raise IOError(f"Output parent directory does not exist: {output_arc_path.parent}")
        elif not os.access(output_arc_path.parent, os.W_OK):
             raise PermissionError(f"Write permission denied for output directory: {output_rebuilt_dir.name}")
        
        try:
            if output_arc_path.resolve().is_relative_to(source_folder_path.resolve()):
                status_queue.put({'type':'status','msg':f"Error: Output ARC path '{output_arc_path.name}' would be inside the input folder '{folder_name_raw}'. Aborting save.",'level':STATUS_ERROR})
                return folder_name_raw, False
        except ValueError: pass 
        except Exception as e: 
             status_queue.put({'type':'status','msg':f"Error checking output path safety for {folder_name_raw}: {e}",'level':STATUS_WARN})
             

        arc.save(str(output_arc_path), files_to_pack, key1=key1, key2=key2) 

        status_queue.put({'type':'status','msg':f"Successfully rebuilt {output_arc_path.name}",'level':STATUS_SUCCESS})
        return folder_name_raw, True 

    except (FileNotFoundError, PermissionError, IOError, ValueError, RuntimeError) as e:
         status_queue.put({'type':'status','msg':f"Failed processing folder {source_folder_path.name}: {e}",'level':STATUS_ERROR});
         status_queue.put({'type':'status','msg':f"Trace: {traceback.format_exc()}",'level':STATUS_DEBUG}) 
         return source_folder_path.name,False
    except Exception as e:
        status_queue.put({'type': 'status', 'msg': f"An unexpected error occurred processing folder {source_folder_path.name}: {e}", 'level': STATUS_ERROR})
        status_queue.put({'type':'status','msg':f"Trace: {traceback.format_exc()}",'level':STATUS_DEBUG}) 
        return source_folder_path.name, False 
    finally:
        if arc: arc.close()


# Orchestrator for single file/folder lists
def run_batch_parallel(worker_func, item_list, output_dir: str | None, progress_callback, status_callback, key1, key2, max_workers=None):
    """Runs a batch of tasks (items) in parallel using a worker function."""
    if not item_list:
        status_callback("No items selected for batch.", STATUS_WARN); progress_callback(100); return

    output_path_obj = None # Initialize
    # For _list_extract_worker, output_dir is ignored by the worker itself.
    # For other workers (like _list_inject_worker), output_dir is mandatory.
    if worker_func != _list_extract_worker:
        if not output_dir:
             status_callback(f"Output directory path is empty (required for {worker_func.__name__}).", STATUS_ERROR); progress_callback(0); return
        output_path_obj = pathlib.Path(output_dir)
        try:
            if output_path_obj.exists(): 
                if not output_path_obj.is_dir(): raise NotADirectoryError(f"Output path exists but is not a directory: {output_dir}")
                if not os.access(output_path_obj, os.W_OK): raise PermissionError(f"Write permission denied for output directory: {output_dir}")
            else: output_path_obj.mkdir(parents=True, exist_ok=True) 
        except Exception as e:
             status_callback(f"Output directory error: {e}", STATUS_ERROR); progress_callback(0); return
    # else: for _list_extract_worker, output_dir is handled differently (ignored by worker)


    total_tasks = len(item_list)
    status_callback(f"Starting parallel batch processing for {total_tasks} items...", STATUS_INFO)
    start_time = time.perf_counter() 
    completed_tasks = 0 

    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor: 
        status_queue = queue.Queue() 
        # Pass output_dir directly (it will be None for _list_extract_worker if called correctly from GUI)
        # Note: _list_inject_worker's target_arc_filename_override will be default None here.
        futures = [executor.submit(worker_func, str(item), output_dir, key1, key2, status_queue) for item in item_list]


        for future in concurrent.futures.as_completed(futures):
            while not status_queue.empty():
                try: msg = status_queue.get_nowait(); status_callback(msg['msg'], msg['level'])
                except queue.Empty: break

            try:
                item_name, success = future.result()
            except Exception as e:
                status_callback(f"Critical error from worker thread processing result: {e}", STATUS_ERROR)
                status_callback(f"Trace: {traceback.format_exc()}", STATUS_DEBUG)

            completed_tasks += 1
            progress_callback(completed_tasks / total_tasks * 100)

    end_time = time.perf_counter() 
    duration = end_time - start_time

    while not status_queue.empty():
        try: msg = status_queue.get_nowait(); status_callback(msg['msg'], msg['level'])
        except queue.Empty: break

    status_callback(f"Batch operation complete. Time taken: {duration:.2f} seconds.", STATUS_SUCCESS)


# --- Recursive Extract Worker and Orchestrator ---
# (_list_extract_worker is used as the worker for recursive extract)

def recursive_batch_extract(source_root_dir: str, output_base_dir: str | None, progress_callback: callable, status_callback: callable, key1: str | None, key2: str | None, max_workers=None):
    """
    Finds all .arc files recursively and extracts them in parallel.
    output_base_dir is ignored as extraction occurs next to source ARC files.
    """
    status_callback("Scanning for ARC files...", STATUS_INFO)
    source_path = pathlib.Path(source_root_dir)
    # output_base_dir is ignored by the worker _list_extract_worker in this context.

    if not source_root_dir: status_callback("Input Missing: Please select source directory.", STATUS_ERROR); progress_callback(0); return
    
    if not source_path.is_dir():
         status_callback("Source directory not found or is not a directory.", STATUS_ERROR); progress_callback(0); return
    if not os.access(source_path, os.R_OK): 
        status_callback(f"Read permission denied for source directory: {source_root_dir}", STATUS_ERROR); progress_callback(0); return

    try: arc_files = list(source_path.rglob('*.arc')) 
    except Exception as e:
         status_callback(f"Error scanning source directory for ARC files: {e}", STATUS_ERROR); progress_callback(0); return


    if not arc_files:
        status_callback("No *.arc files found in the source directory.", STATUS_WARN); progress_callback(100); return

    total_files = len(arc_files)
    status_callback(f"Found {total_files} ARC files. Starting parallel extraction...", STATUS_INFO)
    start_time = time.perf_counter() 
    completed_tasks = 0 

    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor: 
        status_queue = queue.Queue() 
        # Pass None for output_base_dir_str, as _list_extract_worker will ignore it
        futures = [executor.submit(_list_extract_worker, str(arc_file), None, key1, key2, status_queue) for arc_file in arc_files]

        for future in concurrent.futures.as_completed(futures):
            while not status_queue.empty():
                try: msg = status_queue.get_nowait(); status_callback(msg['msg'], msg['level'])
                except queue.Empty: break
            try:
                arc_name, success = future.result()
            except Exception as e:
                status_callback(f"Critical error from worker thread processing result: {e}", STATUS_ERROR)
                status_callback(f"Trace: {traceback.format_exc()}", STATUS_DEBUG)

            completed_tasks += 1
            progress_callback(completed_tasks / total_files * 100)
    
    end_time = time.perf_counter() 
    duration = end_time - start_time

    while not status_queue.empty():
        try: msg = status_queue.get_nowait(); status_callback(msg['msg'], msg['level'])
        except queue.Empty: break

    status_callback(f"Recursive batch extraction complete. Time taken: {duration:.2f} seconds.", STATUS_SUCCESS)


# --- Folder Inject Worker and Orchestrator (Recursive In-Place) ---
def folder_batch_inject(source_dir_str: str, progress_callback: callable, status_callback: callable, 
                        key1: str | None, key2: str | None, max_workers=None):
    """
    Recursively finds edited content folders (*_arc) and matching original .arc files
    in the source_dir_str. Rebuilds ARCs in-place, moving originals and edited
    folders to an 'original' subdirectory.
    """
    status_callback("Scanning for edited content folders and matching ARCs for in-place rebuild...", STATUS_INFO)
    
    if not source_dir_str:
        status_callback("Input Missing: Please select the source directory.", STATUS_ERROR)
        progress_callback(0); return

    source_path = pathlib.Path(source_dir_str)
    if not source_path.is_dir():
        status_callback(f"Source directory not found or is not a directory: {source_dir_str}", STATUS_ERROR)
        progress_callback(0); return
    if not os.access(source_path, os.R_OK) or not os.access(source_path, os.W_OK):
        status_callback(f"Read/Write permission denied for source directory: {source_dir_str}", STATUS_ERROR)
        progress_callback(0); return

    original_backup_root = source_path / "original"
    try:
        original_backup_root.mkdir(parents=True, exist_ok=True)
    except Exception as e:
        status_callback(f"Failed to create archive directory '{original_backup_root}': {e}", STATUS_ERROR)
        progress_callback(0); return
    
    tasks_for_submission = [] 
    
    scan_status_queue = queue.Queue()
    def temp_status(msg, level): scan_status_queue.put({'type':'status','msg':msg,'level':level})

    try:
        for edited_folder in source_path.rglob('*_arc'):
            if not edited_folder.is_dir():
                continue

            try:
                if original_backup_root.resolve() in edited_folder.resolve().parents or \
                   original_backup_root.resolve() == edited_folder.resolve():
                    temp_status(f"Skipping already archived or child folder: {edited_folder.relative_to(source_path)}", STATUS_DEBUG)
                    continue
            except Exception: 
                if str(original_backup_root) in str(edited_folder):
                     temp_status(f"Skipping (path string match) potentially archived folder: {edited_folder.relative_to(source_path)}", STATUS_DEBUG)
                     continue


            arc_basename = edited_folder.name[:-4] 
            original_arc_file = edited_folder.parent / (arc_basename + ".arc")

            if not original_arc_file.is_file() and not (original_backup_root / original_arc_file.relative_to(source_path)).is_file():
                temp_status(f"Original ARC '{original_arc_file.name}' not found (and not archived) for edited folder '{edited_folder.name}'. Skipping.", STATUS_WARN)
                continue
            
            try:
                if original_arc_file.is_file() and original_arc_file.resolve().is_relative_to(edited_folder.resolve()):
                    temp_status(f"Skipping '{edited_folder.name}': Original ARC '{original_arc_file.name}' appears to be inside it.", STATUS_ERROR)
                    continue
            except ValueError: pass 
            except Exception as e: temp_status(f"Path check error for {original_arc_file.name}: {e}", STATUS_WARN)


            tasks_for_submission.append({
                "edited_folder": str(edited_folder),
                "original_arc_location": str(original_arc_file), 
                "target_arc_filename": original_arc_file.name 
            })
    except Exception as e:
        status_callback(f"Error scanning source directory for tasks: {e}", STATUS_ERROR)
        status_callback(f"Trace: {traceback.format_exc()}", STATUS_DEBUG)
        progress_callback(0); return
    finally:
        while not scan_status_queue.empty():
            try: msg = scan_status_queue.get_nowait(); status_callback(msg['msg'], msg['level'])
            except queue.Empty: break


    if not tasks_for_submission:
        status_callback("No matching edited folders and original ARCs found to process.", STATUS_WARN)
        progress_callback(100); return

    total_tasks = len(tasks_for_submission)
    status_callback(f"Found {total_tasks} items for in-place rebuild. Starting parallel processing...", STATUS_INFO)
    start_time = time.perf_counter()
    completed_tasks = 0
    
    futures_map = {} 

    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        worker_status_queue = queue.Queue()

        for task_info in tasks_for_submission:
            original_arc_final_loc_p = pathlib.Path(task_info["original_arc_location"]) 
            edited_folder_p = pathlib.Path(task_info["edited_folder"])
            target_arc_filename = task_info["target_arc_filename"] 

            archive_dest_original_arc = original_backup_root / original_arc_final_loc_p.relative_to(source_path)
            
            original_secured = False
            if original_arc_final_loc_p.exists() and original_arc_final_loc_p.is_file():
                try:
                    archive_dest_original_arc.parent.mkdir(parents=True, exist_ok=True)
                    shutil.move(str(original_arc_final_loc_p), str(archive_dest_original_arc))
                    status_callback(f"Archived original {original_arc_final_loc_p.name} to "
                                    f"./{archive_dest_original_arc.relative_to(source_path.parent)}", STATUS_DEBUG)
                    original_secured = True
                except Exception as e:
                    status_callback(f"Failed to archive original {original_arc_final_loc_p.name}: {e}. Skipping rebuild.", STATUS_ERROR)
                    completed_tasks +=1 
                    progress_callback(completed_tasks / total_tasks * 100)
                    continue 
            elif archive_dest_original_arc.exists() and archive_dest_original_arc.is_file(): 
                 status_callback(f"Original {original_arc_final_loc_p.name} already in archive. Proceeding with rebuild.", STATUS_DEBUG)
                 original_secured = True
            else: 
                status_callback(f"Original ARC {original_arc_final_loc_p.name} not found for securing. Skipping.", STATUS_ERROR)
                completed_tasks +=1
                progress_callback(completed_tasks / total_tasks * 100)
                continue

            if not original_secured: 
                status_callback(f"Critical: Original {original_arc_final_loc_p.name} could not be secured. Skipping.", STATUS_ERROR)
                completed_tasks +=1
                progress_callback(completed_tasks / total_tasks * 100)
                continue

            future = executor.submit(_list_inject_worker,
                                     str(edited_folder_p),               
                                     str(original_arc_final_loc_p.parent), 
                                     key1, key2, worker_status_queue,
                                     target_arc_filename)                
            futures_map[future] = {"original_arc_final_path": str(original_arc_final_loc_p), 
                                   "edited_folder_path": str(edited_folder_p)}

        for future in concurrent.futures.as_completed(futures_map):
            while not worker_status_queue.empty():
                try: msg = worker_status_queue.get_nowait(); status_callback(msg['msg'], msg['level'])
                except queue.Empty: break

            task_details = futures_map[future]
            original_arc_final_path_str = task_details["original_arc_final_path"]
            edited_folder_path_str = task_details["edited_folder_path"]
            
            original_arc_final_loc = pathlib.Path(original_arc_final_path_str) 
            edited_folder_to_archive = pathlib.Path(edited_folder_path_str)

            try:
                _, success = future.result() 
                if success:
                    status_callback(f"Successfully rebuilt {original_arc_final_loc.name}.", STATUS_INFO)
                    archive_dest_edited_folder = original_backup_root / edited_folder_to_archive.relative_to(source_path)
                    archive_dest_edited_folder.parent.mkdir(parents=True, exist_ok=True)

                    if edited_folder_to_archive.exists() and edited_folder_to_archive.is_dir():
                        try:
                            if archive_dest_edited_folder.exists(): 
                                if archive_dest_edited_folder.is_file() or \
                                   not archive_dest_edited_folder.is_dir() or \
                                   any(archive_dest_edited_folder.iterdir()): 
                                    timestamp = datetime.now().strftime("%Y%m%d%H%M%S")
                                    archive_name_ts = f"{archive_dest_edited_folder.name}_{timestamp}"
                                    archive_dest_edited_folder = archive_dest_edited_folder.parent / archive_name_ts
                                    status_callback(f"Archive destination for {edited_folder_to_archive.name} busy/non-empty. Archiving as {archive_name_ts}", STATUS_WARN)
                                else: 
                                    shutil.rmtree(str(archive_dest_edited_folder))
                            
                            shutil.move(str(edited_folder_to_archive), str(archive_dest_edited_folder))
                            status_callback(f"Archived edited folder {edited_folder_to_archive.name} to "
                                            f"./{archive_dest_edited_folder.relative_to(source_path.parent)}", STATUS_DEBUG)
                        except Exception as e:
                            status_callback(f"Failed to archive edited folder {edited_folder_to_archive.name} post-rebuild: {e}", STATUS_ERROR)
                            status_callback(f"Trace: {traceback.format_exc()}", STATUS_DEBUG)
                    elif not edited_folder_to_archive.exists():
                        status_callback(f"Edited folder {edited_folder_to_archive.name} not found for archiving (unexpected).", STATUS_WARN)
                else: 
                    status_callback(f"Rebuild failed for {original_arc_final_loc.name}. Attempting to restore original.", STATUS_ERROR)
                    archived_original_path = original_backup_root / original_arc_final_loc.relative_to(source_path)
                    if archived_original_path.exists() and archived_original_path.is_file():
                        try:
                            if original_arc_final_loc.exists(): 
                                if original_arc_final_loc.is_dir(): shutil.rmtree(str(original_arc_final_loc))
                                else: os.remove(str(original_arc_final_loc))
                            shutil.move(str(archived_original_path), str(original_arc_final_loc))
                            status_callback(f"Restored original {original_arc_final_loc.name} from archive.", STATUS_INFO)
                        except Exception as e:
                            status_callback(f"Failed to restore {original_arc_final_loc.name} from archive {archived_original_path}: {e}", STATUS_ERROR)
                    else:
                        status_callback(f"Original {original_arc_final_loc.name} not found in archive for restoration.", STATUS_WARN)
            
            except Exception as e:
                status_callback(f"Critical error processing result for {original_arc_final_loc.name if 'original_arc_final_loc' in locals() else 'an item'}: {e}", STATUS_ERROR)
                status_callback(f"Trace: {traceback.format_exc()}", STATUS_DEBUG)
                archived_original_path_on_error = original_backup_root / pathlib.Path(original_arc_final_path_str).relative_to(source_path)
                current_final_loc_on_error = pathlib.Path(original_arc_final_path_str)
                if archived_original_path_on_error.exists() and archived_original_path_on_error.is_file():
                    if not current_final_loc_on_error.exists() or not current_final_loc_on_error.samefile(archived_original_path_on_error):
                        try:
                            if current_final_loc_on_error.exists(): 
                                if current_final_loc_on_error.is_dir(): shutil.rmtree(str(current_final_loc_on_error))
                                else: os.remove(str(current_final_loc_on_error))
                            shutil.move(str(archived_original_path_on_error), original_arc_final_path_str)
                            status_callback(f"Attempted to restore original {current_final_loc_on_error.name} due to processing error.", STATUS_WARN)
                        except Exception as e_restore:
                            status_callback(f"Failed to restore {current_final_loc_on_error.name} during error handling: {e_restore}", STATUS_ERROR)


            completed_tasks += 1
            progress_callback(completed_tasks / total_tasks * 100)

    end_time = time.perf_counter()
    duration = end_time - start_time

    while not worker_status_queue.empty(): 
        try: msg = worker_status_queue.get_nowait(); status_callback(msg['msg'], msg['level'])
        except queue.Empty: break
    status_callback(f"Recursive in-place injection (rebuild) complete. Time taken: {duration:.2f} seconds.", STATUS_SUCCESS)


# --- GUI CODE ---
class ArcToolApp:
    def __init__(self, root):
        self.root = root
        self.root.title("SaladSoftware ARC Tool")
        self.root.configure(bg=BG_COLOR)
        self.root.geometry("1400x900") # Initial size

        self.default_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE)
        self.bold_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE, weight="bold")
        self.title_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE + 2, weight="bold")

        self.queue = queue.Queue()
        self.style = ttk.Style()
        self.configure_styles()

        # Main PanedWindow for resizable sections
        self.main_paned_window = ttk.PanedWindow(root, orient=tk.VERTICAL, style='TPanedwindow')
        self.main_paned_window.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # --- Top part (Tabs and controls) ---
        self.top_pane_frame = ttk.Frame(self.main_paned_window, style='TFrame')
        self.main_paned_window.add(self.top_pane_frame, weight=3) # Notebook gets more initial space

        key_frame = ttk.Frame(self.top_pane_frame, style='TFrame')
        key_frame.pack(pady=5, padx=10, fill='x')
        ttk.Label(key_frame, text="~ Handburger's SaladSoftware MT Framework Arc Tool ~", style='TLabel', font=self.title_font, justify='center').grid(row=0, column=0, columnspan=4, sticky='w', pady=(0,5))
        ttk.Label(key_frame, text="Based on Kuriimu/Karameru C# Code by IcySon55", style='TLabel').grid(row=1, column=0, columnspan=4, sticky='w', pady=(0,10))
        
        self.notebook = ttk.Notebook(self.top_pane_frame, style='TNotebook')
        self.list_extract_frame = ttk.Frame(self.notebook, style='TFrame')
        self.list_inject_frame = ttk.Frame(self.notebook, style='TFrame')
        self.rec_extract_frame = ttk.Frame(self.notebook, style='TFrame')
        self.folder_inject_frame = ttk.Frame(self.notebook, style='TFrame') # Recursive In-Place Inject

        self.notebook.add(self.list_extract_frame, text='Extract Arc Files (List)')
        self.notebook.add(self.list_inject_frame, text='Inject Arc Folders (List)')
        self.notebook.add(self.rec_extract_frame, text='Recursive Extract Arcs')
        self.notebook.add(self.folder_inject_frame, text='Recursive Inject (In-Place)')
        self.notebook.pack(pady=5, padx=10, expand=True, fill='both')

        self.create_list_extract_widgets()
        self.create_list_inject_widgets()
        self.create_recursive_extract_widgets()
        self.create_folder_inject_widgets() # For recursive in-place inject

        # --- Bottom part (Status and Progress) ---
        self.bottom_pane_frame = ttk.Frame(self.main_paned_window, style='TFrame')
        self.main_paned_window.add(self.bottom_pane_frame, weight=1) # Status gets less initial space

        self.progress_var = tk.DoubleVar()
        self.progress_bar = ttk.Progressbar(self.bottom_pane_frame, orient='horizontal', length=100, mode='determinate', variable=self.progress_var, style='TProgressbar')
        self.progress_bar.pack(pady=(0, 5), padx=10, fill='x', side=tk.BOTTOM) # Progress bar at bottom of bottom_pane_frame

        self.status_frame = ttk.Frame(self.bottom_pane_frame, style='Status.TFrame')
        self.status_frame.pack(pady=(5, 0), padx=10, fill='both', expand=True, side=tk.BOTTOM) # Fill remaining space
        self.status_frame.grid_rowconfigure(0, weight=1)
        self.status_frame.grid_columnconfigure(0, weight=1)
        
        self.status_text = scrolledtext.ScrolledText(self.status_frame, wrap=tk.WORD, font=self.default_font, bg=WIDGET_BG, fg=TEXT_COLOR, bd=1, relief='sunken', height=8)
        self.status_text.grid(row=0, column=0, sticky='nsew')
        self.status_text.configure(state='disabled')
        self.status_text.tag_config(STATUS_ERROR, foreground=STATUS_ERROR_FG)
        self.status_text.tag_config(STATUS_WARN, foreground=STATUS_WARN_FG)
        self.status_text.tag_config(STATUS_SUCCESS, foreground=STATUS_SUCCESS_FG)
        self.status_text.tag_config(STATUS_INFO, foreground=STATUS_INFO_FG)
        self.status_text.tag_config(STATUS_DEBUG, foreground=STATUS_DEBUG_FG)

        self.check_queue()

    def configure_styles(self):
        self.style.theme_use('clam')
        self.style.configure('.',background=BG_COLOR,foreground=TEXT_COLOR,font=self.default_font,fieldbackground=WIDGET_BG,troughcolor=BG_COLOR,borderwidth=1)
        self.style.map('.',foreground=[('disabled','#aaaaaa')])
        self.style.configure('TFrame',background=BG_COLOR)
        self.style.configure('Status.TFrame',background=BG_COLOR) # Used for status_frame parent
        self.style.configure('TPanedwindow', background=BG_COLOR)
        self.style.configure('TLabel',background=BG_COLOR,foreground=TEXT_COLOR,padding=5)
        self.style.configure('Header.TLabel',font=self.bold_font,foreground=TEXT_COLOR)
        self.style.configure('TButton',background=BUTTON_BG,foreground=BUTTON_FG,bordercolor=BUTTON_BORDER,focuscolor=HIGHLIGHT_BG,lightcolor=BUTTON_BG,darkcolor=BUTTON_BG,padding=6)
        self.style.map('TButton',background=[('active',BUTTON_ACTIVE_BG),('pressed',BUTTON_PRESSED_BG)],foreground=[('active',BUTTON_FG),('pressed',BUTTON_FG)])
        self.style.configure('TEntry',fieldbackground=WIDGET_BG,foreground=INPUT_TEXT_COLOR,insertcolor=INPUT_TEXT_COLOR,bordercolor=BUTTON_BORDER)
        self.style.map('TEntry',selectbackground=[('focus',HIGHLIGHT_BG)],selectforeground=[('focus',HIGHLIGHT_TEXT)])
        self.root.option_add('*Listbox*background',WIDGET_BG)
        self.root.option_add('*Listbox*foreground',TEXT_COLOR)
        self.root.option_add('*Listbox*selectBackground',HIGHLIGHT_BG)
        self.root.option_add('*Listbox*selectForeground',HIGHLIGHT_TEXT)
        self.root.option_add('*Listbox*font',self.default_font)
        self.root.option_add('*Listbox*bd',1)
        self.root.option_add('*Listbox*relief','sunken')
        self.style.configure('TNotebook',background=BG_COLOR,borderwidth=0)
        self.style.configure('TNotebook.Tab',background=HEADER_BG,foreground=HEADER_TEXT,padding=[10,5],font=self.default_font,borderwidth=1)
        self.style.map('TNotebook.Tab',background=[('selected',HEADER_ACTIVE_BG)],foreground=[('selected',HEADER_ACTIVE_TEXT)],expand=[('selected',[1,1,1,1])])
        self.style.configure('TProgressbar',thickness=20,background=STATUS_SUCCESS_FG,troughcolor=WIDGET_BG)


    def _create_dir_input(self, parent, label, row, var_name):
        ttk.Label(parent, text=label, style='Header.TLabel').grid(row=row, column=0, sticky='w', padx=5, pady=(10,2))
        frame=ttk.Frame(parent); frame.grid(row=row+1, column=0, sticky='ew', padx=5, pady=(0,5)); frame.grid_columnconfigure(0, weight=1)
        v=tk.StringVar(); setattr(self, var_name, v); 
        e=ttk.Entry(frame, textvariable=v, width=60); e.grid(row=0, column=0, sticky='ew')
        b=ttk.Button(frame, text="Browse...", command=lambda v_arg=v: self._select_directory(v_arg)); b.grid(row=0, column=1, padx=(5,0)) # Renamed lambda v to v_arg
        return v 

    def _select_directory(self, string_var):
        directory=filedialog.askdirectory(title="Select Directory")
        if directory: string_var.set(directory)


    def create_list_extract_widgets(self):
        frame=self.list_extract_frame; frame.grid_columnconfigure(0, weight=1); frame.grid_rowconfigure(1, weight=1) 
        ttk.Label(frame, text="Input ARC Files:", style='Header.TLabel').grid(row=0, column=0, columnspan=3, sticky='w', pady=(10,5))
        self.list_extract_listbox=tk.Listbox(frame, width=80, height=10, selectmode=tk.EXTENDED); self.list_extract_listbox.grid(row=1, column=0, columnspan=2, padx=5, pady=5, sticky='nsew')
        sb=ttk.Scrollbar(frame, orient='vertical', command=self.list_extract_listbox.yview); sb.grid(row=1, column=2, sticky='nsw', pady=5); self.list_extract_listbox.config(yscrollcommand=sb.set)
        bf=ttk.Frame(frame); bf.grid(row=2, column=0, columnspan=2, sticky='ew') 
        ttk.Button(bf, text="Select Files", command=self.select_list_extract_files).pack(side=tk.LEFT, padx=5, pady=5)
        ttk.Button(bf, text="Clear List", command=lambda: self.list_extract_listbox.delete(0, tk.END)).pack(side=tk.RIGHT, padx=5, pady=5)
        
        ttk.Label(frame, text="Output: Folders named <filename>_arc will be created next to each input .arc file.", style='TLabel').grid(row=3, column=0, columnspan=3, sticky='w', padx=5, pady=(10,5))
        
        ttk.Button(frame, text="Start Extraction", command=self.start_list_extraction).grid(row=4, column=0, columnspan=3, pady=(20,10)) 

    def create_list_inject_widgets(self):
        frame=self.list_inject_frame; frame.grid_columnconfigure(0, weight=1); frame.grid_rowconfigure(1, weight=1) 
        ttk.Label(frame, text="Input Source Folders:", style='Header.TLabel').grid(row=0, column=0, columnspan=3, sticky='w', pady=(10,5))
        self.list_inject_listbox=tk.Listbox(frame, width=80, height=10, selectmode=tk.EXTENDED); self.list_inject_listbox.grid(row=1, column=0, columnspan=2, padx=5, pady=5, sticky='nsew')
        sb=ttk.Scrollbar(frame, orient='vertical', command=self.list_inject_listbox.yview); sb.grid(row=1, column=2, sticky='nsw', pady=5); self.list_inject_listbox.config(yscrollcommand=sb.set)
        bf=ttk.Frame(frame); bf.grid(row=2, column=0, columnspan=2, sticky='ew') 
        ttk.Button(bf, text="Add Folder(s)", command=self.select_list_inject_folders).pack(side=tk.LEFT, padx=5, pady=5)
        ttk.Button(bf, text="Clear List", command=lambda: self.list_inject_listbox.delete(0, tk.END)).pack(side=tk.RIGHT, padx=5, pady=5)
        self._create_dir_input(frame, "Output Rebuilt ARC Directory:", 3, "list_inject_output_var")
        ttk.Button(frame, text="Start Rebuild", command=self.start_list_injection).grid(row=5, column=0, columnspan=3, pady=(20,10))

    def create_recursive_extract_widgets(self):
        frame=self.rec_extract_frame; frame.grid_columnconfigure(0, weight=1); 
        self._create_dir_input(frame, "Source ARC Directory (Recursive):", 0, "rec_extract_source_var")
        
        ttk.Label(frame, text="Output: Folders named <filename>_arc will be created next to each found .arc file.", style='TLabel').grid(row=2, column=0, sticky='w', padx=5, pady=(10,5))
        
        ttk.Button(frame, text="Start Recursive Extraction", command=self.start_recursive_extraction).grid(row=3, column=0, pady=(20,10))

    def create_folder_inject_widgets(self): # Renamed to reflect "Recursive Inject (In-Place)"
        frame=self.folder_inject_frame; frame.grid_columnconfigure(0, weight=1); 
        self._create_dir_input(frame, "Source Directory (contains .arc files and _arc folders):", 0, "folder_inject_source_dir_var")
        
        info_text = ("Rebuilds .arc files found alongside corresponding _arc folders.\n"
                     "Original .arc files and _arc folders will be moved into an 'original' subfolder \n"
                     "at the root of the Source Directory, preserving their relative paths.\n"
                     "The new rebuilt .arc files will replace the originals.")
        ttk.Label(frame, text=info_text, style='TLabel', justify=tk.LEFT).grid(row=2, column=0, sticky='w', padx=5, pady=(10,5))

        ttk.Button(frame, text="Start In-Place Rebuild", command=self.start_folder_injection).grid(row=3, column=0, pady=(20,10))


    def select_list_extract_files(self):
        files=filedialog.askopenfilenames(title="Select ARC Files", filetypes=[("MT ARC","*.arc"),("All Files","*.*")])
        if files:
            current_items = set(self.list_extract_listbox.get(0, tk.END))
            for f in files:
                if f not in current_items:
                    self.list_extract_listbox.insert(tk.END, f)

    def select_list_inject_folders(self):
        # Allow selecting multiple folders if system dialog supports it (Windows does with a workaround)
        # For simplicity, sticking to one-by-one for now unless askdirectory has a multi option
        directory=filedialog.askdirectory(title="Select Source Folder(s) to Add to List")
        if directory:
            current_items = set(self.list_inject_listbox.get(0, tk.END))
            if directory not in current_items:
                 self.list_inject_listbox.insert(tk.END, directory)


    def _run_task(self, target_func, args_tuple):
        k1, k2 = None, None # For now, keys are not taken from GUI. Could be added later.
        
        # Adapt arguments for different functions
        # The core functions now expect (..., progress_callback, status_callback, key1, key2)
        # For folder_batch_inject, output_dir is implicit in source_dir
        if target_func == folder_batch_inject:
            # folder_batch_inject(source_dir, progress_callback, status_callback, key1, key2, max_workers=None)
            # args_tuple = (source_dir_str,)
            full_args = args_tuple + (self.update_progress, self.queue_status, k1, k2)
        else:
            # Most other functions: (..., item_list_or_src_dir, output_dir_or_None, progress_callback, status_callback, key1, key2)
            # args_tuple = (worker_func_or_src_dir, items_or_output_dir, output_dir_or_None_if_3rd_arg)
            full_args = args_tuple + (self.update_progress, self.queue_status, k1, k2)

        self.progress_var.set(0)
        task_name = target_func.__name__.replace('_batch', '').replace('_list', ' List').replace('_recursive', ' Recursive').replace('_folder', ' Folder').replace('_', ' ').strip().title()
        self.add_status_message(f"Starting {task_name} task...", STATUS_INFO)
        
        thread = threading.Thread(target=target_func, args=full_args, daemon=True) 
        thread.start()


    def start_list_extraction(self):
        items = self.list_extract_listbox.get(0, tk.END)
        if not items: messagebox.showwarning("Input Missing","Please select one or more ARC files to extract."); return
        # _list_extract_worker output_dir is None (output next to source)
        self._run_task(run_batch_parallel, (_list_extract_worker, items, None))


    def start_list_injection(self):
        items = self.list_inject_listbox.get(0, tk.END)
        out_dir = self.list_inject_output_var.get() 
        if not items: messagebox.showwarning("Input Missing","Please add one or more source folders to inject."); return
        if not out_dir: messagebox.showwarning("Output Missing","Please select an output directory."); return
        for folder_path_str in items:
            if not os.path.isdir(folder_path_str): 
                messagebox.showerror("Input Invalid",f"Source folder not found: {folder_path_str}"); return
        self._run_task(run_batch_parallel, (_list_inject_worker, items, out_dir))


    def start_recursive_extraction(self):
        src = self.rec_extract_source_var.get()
        if not src: messagebox.showwarning("Input Missing","Please select the source directory containing ARC files."); return
        # recursive_batch_extract's output_base_dir is None (output next to source via _list_extract_worker)
        self._run_task(recursive_batch_extract, (src, None))


    def start_folder_injection(self): # This is for the "Recursive Inject (In-Place)" tab
        src_dir = self.folder_inject_source_dir_var.get()
        if not src_dir: messagebox.showwarning("Input Missing","Please select the source directory."); return
        
        # folder_batch_inject(source_dir_str, progress_callback, status_callback, key1, key2, max_workers=None)
        # The _run_task will append progress_callback, status_callback, k1, k2
        self._run_task(folder_batch_inject, (src_dir,))


    def update_progress(self,v):
        self.queue.put({'type':'progress','value':max(0.0, min(100.0, float(v)))}) 

    def queue_status(self,m,l=STATUS_INFO):
        self.queue.put({'type':'status','msg':m,'level':l})

    def check_queue(self):
        try:
            while True:
                m=self.queue.get_nowait()
                t=m.get('type')
                if t=='progress':
                    self.progress_var.set(m.get('value',0.0))
                elif t=='status':
                    self.add_status_message(m.get('msg',''),m.get('level',STATUS_INFO))
        except queue.Empty:
            pass
        except Exception as e:
            print(f"Critical error processing queue: {e}", file=sys.stderr)
            print(f"Trace: {traceback.format_exc()}", file=sys.stderr)
            try: self.add_status_message(f"Critical GUI queue error: {e}", STATUS_ERROR)
            except Exception: pass 
        finally:
            self.root.after(100,self.check_queue) 

    def add_status_message(self,m,l=STATUS_INFO):
        try:
            self.status_text.configure(state='normal') 
            timestamp = datetime.now().strftime("[%H:%M:%S]")
            self.status_text.insert(tk.END,f"{timestamp} {m}\n",l) 
            self.status_text.configure(state='disabled') 
            self.status_text.see(tk.END) 
        except Exception as e:
            print(f"Error updating status GUI: {e}", file=sys.stderr)
            print(f"Status message: {m}", file=sys.stderr)


# --- MAIN EXECUTION ---
if __name__ == "__main__":
    try: from Crypto.Cipher import Blowfish
    except ImportError:
        # Attempt to show Tkinter messagebox even if main GUI hasn't started
        temp_root = tk.Tk()
        temp_root.withdraw() # Hide the root window
        messagebox.showerror("Dependency Missing","Required library 'pycryptodome' not found.\nPlease install it using:\npip install pycryptodome")
        temp_root.destroy()
        sys.exit(1) 

    script_dir = os.path.dirname(os.path.abspath(__file__))
    # Use the EXTENSION_MAP_FILE constant which is now "unique_extensions.txt"
    extension_map_file_path = os.path.join(script_dir, EXTENSION_MAP_FILE)
    
    # Ensure unique_extensions.txt exists or prompt user
    if not os.path.exists(extension_map_file_path):
        temp_root_warn = tk.Tk()
        temp_root_warn.withdraw()
        messagebox.showwarning("Extension Map Missing", 
                               f"The extension map file '{EXTENSION_MAP_FILE}' was not found in the script directory:\n'{script_dir}'\n"
                               "Please ensure it exists. Extensions may not be resolved correctly.")
        temp_root_warn.destroy()
        # Proceed with empty map if file is missing, load_extension_map will print a warning.
    
    load_extension_map(extension_map_file_path)
    # No need for a separate messagebox if EXTENSION_MAP is empty after load,
    # as load_extension_map already prints warnings/errors.

    root = tk.Tk()
    app = ArcToolApp(root)
    root.mainloop()