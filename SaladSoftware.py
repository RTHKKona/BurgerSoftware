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
from collections import namedtuple
from Crypto.Cipher import Blowfish
# from Crypto.Util.Padding import pad, unpad # Using manual null padding
# from Crypto.Random import get_random_bytes # Not currently needed
from datetime import datetime # For timestamps


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
DEFAULT_VERSION=7;DEFAULT_BYTE_ORDER_CHAR='<';DEFAULT_PLATFORM=Platform.Switch
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

# --- Extension Map (Will be populated from file) ---
EXTENSION_MAP = {}
REV_EXTENSION_MAP = {}
EXTENSION_MAP_FILE = "extension_index_line.txt" # Name of the file to load


# --- ARC UTILITIES & MTArc Class ---

def create_file_info():
    """Creates a dictionary to hold file metadata and data."""
    return {
        "filename_base":b'',"ext_hash":0,"compressed_size":0,"uncompressed_size_raw":0,
        "offset":0,"unknown1":None,"platform":Platform.UNKNOWN,"data":None,"full_filename":"",
        "is_compressed":False,"calculated_uncompressed_size":None, # Calculated size can be None if original size is invalid
    }

def load_extension_map(filepath: str):
    """Loads the extension map from a text file."""
    global EXTENSION_MAP, REV_EXTENSION_MAP
    EXTENSION_MAP = {}
    REV_EXTENSION_MAP = {}

    if not os.path.isfile(filepath):
        print(f"Warning: Extension map file not found at '{filepath}'. Using empty map.", file=sys.stderr)
        return

    try:
        with open(filepath, 'r', encoding='utf-8') as f: # Use utf-8 encoding for safety
            for line_num, line in enumerate(f, 1):
                line = line.strip()
                if not line or line.startswith('#') or line.startswith('//'): continue # Skip empty lines and comments

                try:
                    parts = line.split(',', 1) # Split only on the first comma
                    if len(parts) == 2:
                        hex_hash_str = parts[0].strip()
                        extension_str = parts[1].strip()

                        # Parse hex hash
                        hash_value = int(hex_hash_str, 16)

                        # Validate extension string format (starts with dot)
                        if extension_str.startswith('.'):
                             # Add to maps
                             EXTENSION_MAP[hash_value] = extension_str
                             # Store lowercase extension in reverse map
                             REV_EXTENSION_MAP[extension_str.lower()] = hash_value
                        else:
                            print(f"Warning: Line {line_num} in {filepath}: Invalid extension format '{extension_str}'. Skipping.", file=sys.stderr)

                    else:
                        print(f"Warning: Line {line_num} in {filepath}: Invalid format (expected 'hash, .ext'). Skipping.", file=sys.stderr)

                except ValueError:
                    print(f"Warning: Line {line_num} in {filepath}: Invalid hex hash value ('{hex_hash_str}'). Skipping.", file=sys.stderr)
                except Exception as e:
                    print(f"Warning: Unexpected error processing line {line_num} in {filepath}: {e}. Skipping.", file=sys.stderr)

        print(f"Loaded {len(EXTENSION_MAP)} extension mappings from {filepath}.")

    except Exception as e:
        print(f"Error loading extension map from {filepath}: {e}", file=sys.stderr)
        EXTENSION_MAP = {} # Ensure maps are empty on error
        REV_EXTENSION_MAP = {}


def get_full_filename(file_info):
    """Constructs the full filename (preserving separators) from base name and extension hash, using loaded map."""
    try:
        name = "decode_error" # Default if decoding fails
        filename_bytes = file_info.get("filename_base", b'')
        if not filename_bytes: name = ""
        else:
            # Try decoding with common encodings until successful or exhausted
            for encoding in ['ascii','latin-1','utf-8']: # Try common encodings
                 try:
                      decoded_name = filename_bytes.split(b'\x00',1)[0].decode(encoding)
                      if decoded_name: # Ensure not empty
                           # Important: Keep original separators (\ and /)
                           name = decoded_name
                           break # Success
                 except UnicodeDecodeError: continue
                 except Exception: continue # Catch other potential errors
    except Exception: name = "decode_error_unknown" # Catch any unexpected errors during name decoding

    # Look up extension hash in the loaded EXTENSION_MAP.
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


    #def _setup_encryption(self, key1=None, key2=None):
    #    """Sets up the crypto object if valid keys are provided."""
    #    k1p=key1 is not None and key1!="";k2p=key2 is not None and key2!=""
    #    if k1p!=k2p: raise ValueError("Both keys required or none");
    #    if k1p and k2p:
    #        try: dk=self._dk(k1,k2);self.crypto=MTBlowfishCrypto(dk);self.is_encrypted=True
    #        except Exception as e: print(f"ERR:Encrypt init fail:{e}",file=sys.stderr);self.is_encrypted=False;self.crypto=None;raise
    #    else: self.is_encrypted=False;self.crypto=None


    def load(self, filepath, key1=None, key2=None):
        """Loads ARC data from a file, parsing headers, entries, and setting up for extraction."""
        self.files = []; self._raw_file_path = None; self._decrypted_entries_bytes = None; self._data_offset = 0; self._file_size = None

        try:
            self._setup_encryption(key1, key2);
            if not os.path.isfile(filepath): raise FileNotFoundError(f"Not found:{filepath}");
            if not os.access(filepath,os.R_OK): raise PermissionError(f"Read denied:{filepath}");
            self._raw_file_path=filepath;
            try: self._file_size=os.path.getsize(filepath) # Store file size
            except Exception as e: raise IOError(f"Size get fail:{filepath}:{e}") from e
            if self._file_size < 4: raise IOError(f"Too small({self._file_size}b)");

            with open(filepath,'rb') as f_raw:
                mb=f_raw.read(4);f_raw.seek(0);self.byte_order_char='>'if mb==MAGIC_ARC_BE or mb==MAGIC_HFS_BE else'<';self.platform=Platform.PS3 if self.byte_order_char=='>'else Platform.PC
                ishfs=mb==MAGIC_HFS_LE or mb==MAGIC_HFS_BE
                if ishfs:
                    hfs_header_fmt=format_struct(self.byte_order_char,FMT_HFS_HEADER)
                    if self._file_size<SIZE_HFS_HEADER: raise IOError("Short HFS hdr")
                    hfb=f_raw.read(SIZE_HFS_HEADER);
                    if len(hfb)<SIZE_HFS_HEADER: raise IOError(f"Incomplete HFS hdr read({len(hfb)}/{SIZE_HFS_HEADER})")
                    try: self.hfs_header=namedtuple("HFSHeader",["magic","version","type","file_size","padding"])(*struct.unpack(hfs_header_fmt,hfb))
                    except Exception as e: raise IOError(f"Parse HFS hdr fail:{e}")from e
                    self.hfs_header_length=0x20000 if self.hfs_header.type==0 else 0x10; epah=f_raw.tell()+self.hfs_header_length
                    if epah>self._file_size: raise IOError(f"Short HFS data({self.hfs_header_length}b)"); f_raw.seek(self.hfs_header_length,io.SEEK_CUR)
                else: self.hfs_header=None;self.hfs_header_length=0
                rah=self._file_size-f_raw.tell()
                if rah<SIZE_HEADER_COMMON: raise IOError(f"Short ARC hdr({SIZE_HEADER_COMMON}b exp,{rah}b rem)");
                hcf=format_struct(self.byte_order_char,FMT_HEADER_COMMON);hb=f_raw.read(SIZE_HEADER_COMMON)
                if len(hb)<SIZE_HEADER_COMMON: raise IOError(f"Incomplete ARC hdr read({len(hb)}/{SIZE_HEADER_COMMON})")
                try: self.arc_header=namedtuple("ARCHeader",["magic","version","entry_count"])(*struct.unpack(hcf,hb))
                except Exception as e: raise IOError(f"Parse ARC hdr fail:{e}")from e
                eam=MAGIC_ARC_BE if self.byte_order_char=='>'else MAGIC_ARC_LE; eam2=MAGIC_ARCC_LE if self.byte_order_char=='<'else b'';
                if self.arc_header.magic not in[eam,eam2]: print(f"W:Unusual ARC magic:{self.arc_header.magic!r}",file=sys.stderr)
                self.header_length=SIZE_HEADER_COMMON;v=self.arc_header.version
                if self.byte_order_char=='>':self.platform=Platform.PS3
                elif v==9:self.platform=Platform.Switch;self.entry_struct_fmt=format_struct('<',FMT_ENTRY_SWITCH);self.entry_struct_size=SIZE_ENTRY_SWITCH
                elif v==7:self.platform=Platform.PC;self.entry_struct_fmt=format_struct('<',FMT_ENTRY);self.entry_struct_size=SIZE_ENTRY
                else:self.platform=Platform.PC;self.entry_struct_fmt=format_struct('<',FMT_ENTRY);self.entry_struct_size=SIZE_ENTRY
                if self.byte_order_char=='<'and v not in[7,9]:
                    if f_raw.tell()+SIZE_HEADER_PC_EXTRA<=self._file_size:f_raw.read(SIZE_HEADER_PC_EXTRA);self.header_length+=SIZE_HEADER_PC_EXTRA
                    else:print(f"W:Exp pad v{v} LE, file short.",file=sys.stderr)
                mre=1000000;ec=self.arc_header.entry_count
                if ec is None or not isinstance(ec,int)or ec<0 or ec>mre: raise ValueError(f"Invalid entries({ec}).Corrupt?");
                emsu=ec*self.entry_struct_size;rahs=self._file_size-f_raw.tell()
                etp=ec #EntriesToProcess
                if rahs<emsu:
                    print(f"W:File short metadata({emsu}b exp,{rahs}b rem).Partial read.",file=sys.stderr);
                    mbrr=rahs-(rahs%self.entry_struct_size);etp=mbrr//self.entry_struct_size if self.entry_struct_size>0 else 0
                    if etp==0 and ec>0:raise IOError("File too short for 1 entry.")
                    print(f"W:Will read {etp} entries.",file=sys.stderr)
                else:mbrr=emsu
                mbr=f_raw.read(mbrr);
                if len(mbr)!=mbrr:raise IOError(f"Incomplete metadata read({len(mbr)}/{mbrr})");
                mbd=mbr
                if self.is_encrypted and self.crypto:
                    try:mbd=self.crypto.decrypt_ecb(mbr)
                    except Exception as e:print(f"W:Meta decrypt fail:{e}.Parsing raw.",file=sys.stderr);mbd=mbr
                self._decrypted_entries_bytes=mbd;bap=len(self._decrypted_entries_bytes);netp=bap//self.entry_struct_size if self.entry_struct_size>0 else 0 #NumEntriesToParse
                if netp<etp:print(f"W:Only {netp} entries fit decrypted meta.Hdr said {ec}.",file=sys.stderr)
                for i in range(netp):
                    eso=i*self.entry_struct_size;eeo=eso+self.entry_struct_size
                    if bap<eeo:print(f"W:Meta block short parse.Cannot parse e{i+1}+.",file=sys.stderr);break
                    ed=self._decrypted_entries_bytes[eso:eeo];fi=create_file_info();fi["platform"]=self.platform
                    try:
                        up=struct.unpack(self.entry_struct_fmt,ed)
                        if self.platform==Platform.Switch:fi.update(zip(["filename_base","ext_hash","compressed_size","uncompressed_size_raw","unknown1","offset"],up))
                        else:fi.update(zip(["filename_base","ext_hash","compressed_size","uncompressed_size_raw","offset"],up));fi["unknown1"]=None
                        csz=fi.get("compressed_size");calcsz=get_calculated_uncompressed_size(fi);fi["is_compressed"]=True if(self.platform==Platform.Switch and csz is not None and csz>0)or(csz is not None and calcsz is not None and csz>0 and csz!=calcsz)else False
                        fi["full_filename"]=get_full_filename(fi);fi["calculated_uncompressed_size"]=calcsz
                        if csz is None or not isinstance(csz,int)or csz<0:print(f"W:File'{fi['full_filename']}'e{i+1} invalid comp size({csz}).Skip.",file=sys.stderr);continue
                        if calcsz is not None and calcsz<0:print(f"W:File'{fi['full_filename']}'e{i+1} neg uncomp size({calcsz}).",file=sys.stderr)
                        offset_val=fi.get("offset");
                        if offset_val is None or not isinstance(offset_val,int)or offset_val<0:print(f"W:File'{fi['full_filename']}'e{i+1} invalid offset({offset_val}).Skip.",file=sys.stderr);continue
                        data_end_potential=offset_val+csz;arc_section_size=self._file_size-self.hfs_header_length
                        if data_end_potential>arc_section_size:print(f"W:File'{fi['full_filename']}'e{i+1} data end({data_end_potential})>ARC end({arc_section_size}).Read partial?",file=sys.stderr)
                        self.files.append(fi)
                    except Exception as e:print(f"Err parse entry{i+1}data:{e}.Skip.",file=sys.stderr);
                    status_queue.put({'type':'status','msg':f"Err parse entry{i+1}:{e}.Skip.",'level':STATUS_WARN}) if 'status_queue' in locals() else None
                if len(self.files)<ec:print(f"W:Parsed {len(self.files)}/{ec} entries.",file=sys.stderr);
                status_queue.put({'type':'status','msg':f"W:Parsed{len(self.files)}/{ec} entries due to issues.",'level':STATUS_WARN}) if 'status_queue' in locals() else None
                self._data_offset=0
                if self.files:self._data_offset=self.files[0].get("offset",0)
                dsap=self.hfs_header_length+self._data_offset;capmb=f_raw.tell() #CurrentPosAfterMetadataBlock
                if dsap<capmb and len(self.files)>0:print(f"W:Data offset({self._data_offset},abs{dsap})in meta(ends near{capmb}).",file=sys.stderr);status_queue.put({'type':'status','msg':f"W:Data offset({self._data_offset})in meta.Extract fail?",'level':STATUS_WARN}) if 'status_queue' in locals() else None
                if dsap>self._file_size:print(f"W:Data offset({self._data_offset},abs{dsap})>file end({self._file_size}).Extract fail.",file=sys.stderr);status_queue.put({'type':'status','msg':"W:Data offset>file end.Extract fail?",'level':STATUS_WARN}) if 'status_queue' in locals() else None
        except (FileNotFoundError, PermissionError, IOError, ValueError, RuntimeError) as e: raise e
        except Exception as e: raise IOError(f"Load fail {os.path.basename(filepath)}:{e}")from e

    def extract_file(self, file_info, input_arc_path):
        """Reads, decrypts, and decompresses file data for a single file_info."""
        if not self._raw_file_path or self._raw_file_path != input_arc_path or self._file_size is None:
             raise RuntimeError(f"MTArc object state invalid for extraction of '{file_info.get('full_filename', '?')}'. Did load() complete successfully for {os.path.basename(input_arc_path)}?")
        try:offset=int(file_info.get("offset",0));hfs_len=int(self.hfs_header_length);d_off=offset+hfs_len
        except Exception as e:raise ValueError(f"Invalid offset/HFS length '{file_info.get('full_filename','?')}':{e}")from e
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
        # *** REMOVED WARNING for actual_size < expected_size ***
        #elif actsz<expsz: print(f"W:Final size {actsz} < exp {expsz} '{file_info.get('full_filename','?')}'.Incomplete?",file=sys.stderr)
        return fin

    def save(self, output_path, input_file_infos, key1=None, key2=None):
        """Builds an ARC file (forced as Switch v9), handling encryption."""
        if not input_file_infos: raise ValueError("No files provided for saving.")
        if not isinstance(input_file_infos, list): raise TypeError("input_file_infos must be a list.")
        try:
            self._se(k1, k2); # Setup crypto
            self.platform=Platform.Switch; self.byte_order_char='<'; v=9; self.entry_struct_fmt=format_struct('<',FMT_ENTRY_SWITCH); self.entry_struct_size=SIZE_ENTRY_SWITCH; self.header_length=SIZE_HEADER_COMMON;
            initial_ec=len(input_file_infos) # Initial EntryCount
            ds=io.BytesIO(); updated_file_infos=[];
            temp_md_size=initial_ec*self.entry_struct_size; temp_md_end=self.header_length+temp_md_size; al=ALIGNMENT_SWITCH; temp_data_start=(temp_md_end+al-1)&~(al-1);
            cdo=temp_data_start # Current data offset absolute
            for idx, fi in enumerate(input_file_infos):
                if not isinstance(fi,dict): print(f"W:Skip invalid item {idx} (not dict).",file=sys.stderr);continue
                od=fi.get("data"); fn=fi.get("full_filename","unknown file")
                if od is None: print(f"W:No data key '{fn}'.Empty.",file=sys.stderr);od=b''
                elif not isinstance(od,bytes): print(f"W:Data not bytes '{fn}'({type(od).__name__}).Empty.",file=sys.stderr);od=b''
                us=len(od); cd=b''; dtw=b'' # UncompressedSize, CompressedData, DataToWrite
                if us>0:
                    try: cd=compress_kontract_zlib(od)
                    except Exception as e: print(f"ERR:Zlib compress fail '{fn}':{e}.Store raw.",file=sys.stderr);cd=od
                dtw=cd
                if self.is_encrypted:
                    if not self.crypto: raise RuntimeError("Encrypt but no crypto");
                    try: dtw=self.crypto.encrypt_ecb(dtw)
                    except Exception as e: print(f"ERR:Blowfish encrypt data fail '{fn}':{e}.Store plain.",file=sys.stderr);dtw=cd
                fi_to_save=fi.copy(); fi_to_save["offset"]=cdo; fi_to_save["compressed_size"]=len(dtw); fi_to_save["uncompressed_size_raw"]=us; fi_to_save["unknown1"]=fi_to_save.get("unknown1",0);
                try: ds.write(dtw)
                except Exception as e: raise IOError(f"Write temp stream fail '{fn}':{e}")from e
                cdo+=len(dtw); updated_file_infos.append(fi_to_save)
            try:
                output_p=pathlib.Path(output_path); output_p.parent.mkdir(parents=True,exist_ok=True)
                with open(output_p, 'wb') as f:
                    f.write(b'\x00'*self.header_length) # Placeholder header
                    mdb_plain=bytearray(); packed_entry_count=0
                    for fi in updated_file_infos:
                        fnb=fi.get("filename_base");fn=fi.get("full_filename","?")
                        if not fnb: bn=os.path.splitext(fn)[0]; 
                        try:fnb=bn.encode('ascii')
                        except UnicodeEncodeError:fnb=bn.encode('utf-8',errors='ignore')
                        filename_bytes=fnb
                        pn=filename_bytes[:64].ljust(64,b'\x00')
                        ev=(pn,fi.get("ext_hash",0),fi.get("compressed_size",0),fi.get("uncompressed_size_raw",0),fi.get("unknown1",0),fi.get("offset",0))
                        if ev[2]is None or not isinstance(ev[2],int)or ev[2]<0 or ev[5]is None or not isinstance(ev[5],int)or ev[5]<0: print(f"W:Skip pack entry '{fn}':Invalid size({ev[2]})or offset({ev[5]}).",file=sys.stderr);continue
                        try: packed_entry=struct.pack(self.entry_struct_fmt,*ev); mdb_plain.extend(packed_entry); packed_entry_count+=1
                        except Exception as e: print(f"ERR:Pack entry fail '{fn}':{e}.Skip.",file=sys.stderr)
                    mdr=bytes(mdb_plain); mtw=mdr;
                    if self.is_encrypted:
                        if not self.crypto: raise RuntimeError("Encrypt but no crypto");
                        try: mtw=self.crypto.encrypt_ecb(mdr)
                        except Exception as e: print(f"ERR:Blowfish encrypt meta fail:{e}.Store plain.",file=sys.stderr);mtw=mdr
                    f.write(mtw)
                    meta_end_actual=self.header_length+len(mtw); data_start_actual=(meta_end_actual+al-1)&~(al-1);
                    pad=data_start_actual-f.tell();
                    if pad<0: raise RuntimeError(f"Internal ERR:Data start({data_start_actual})<meta end({f.tell()})");
                    if pad>0: f.write(b'\x00'*pad)
                    if f.tell()!=data_start_actual: raise RuntimeError(f"Internal ERR:Stream pos({f.tell()})!=data start({data_start_actual})")
                    f.write(ds.getvalue())
                    f.seek(0)
                    f.write(struct.pack(format_struct(self.byte_order_char,FMT_HEADER_COMMON),MAGIC_ARC_LE,v,packed_entry_count)) # Use final count
            except Exception as e:
                 print(f"ERR:Write output fail {output_path}:{e}",file=sys.stderr);
                 if os.path.exists(output_path): 
                    try: os.remove(output_path)
                    except Exception as ce: print(f"W:Cleanup fail {output_path}:{ce}",file=sys.stderr)
                 raise RuntimeError(f"Save fail {os.path.basename(output_path)}:{e}")from e
        except Exception as e: raise RuntimeError(f"Save prepare fail:{e}")from e

    def close(self): pass

# --- BATCH OPERATIONS (Workers and Orchestrators) ---

# _list_extract_worker(arc_path_str, output_base_dir_str, key1, key2, status_queue)
def _list_extract_worker(arc_path_str: str, output_base_dir_str: str, key1: str | None, key2: str | None, status_queue: queue.Queue):
    """Worker to extract a single ARC file from a list or recursive scan."""
    arc_path = pathlib.Path(arc_path_str)
    output_base_dir = pathlib.Path(output_base_dir_str)
    arc = None # Initialize arc object

    try:
        arc_filename = arc_path.name
        arc_basename = arc_path.stem
        output_folder = output_base_dir / arc_basename

        status_queue.put({'type': 'status', 'msg': f"Loading {arc_filename}...", 'level': STATUS_DEBUG})

        # Load the ARC file - MTArc.load handles key setup and parsing, and raises exceptions on failure
        arc = MTArc()
        # Pass status_queue to load for more detailed warnings/errors during parsing? No, load prints directly.
        arc.load(str(arc_path), key1=key1, key2=key2) # Load can raise exceptions

        # Ensure output folder exists
        try: output_folder.mkdir(parents=True, exist_ok=True)
        except Exception as e:
             raise IOError(f"Failed to create output folder {output_folder}: {e}") from e


        platform_name = Platform(arc.platform).name if isinstance(arc.platform, Platform) else f"Platform {arc.platform}"
        status_queue.put({'type': 'status', 'msg': f" Extracting {len(arc.files)} files from {platform_name} ARC {arc_filename} to {output_folder.name}...", 'level': STATUS_INFO})

        # Process files within this ARC
        processed_count = 0
        error_count = 0
        for file_info in arc.files:
            # Defensive check for file_info structure
            if not isinstance(file_info, dict) or "full_filename" not in file_info or "offset" not in file_info or "compressed_size" not in file_info:
                 status_queue.put({'type':'status','msg':f"  Skipping invalid file info in {arc_filename}: {file_info!r}",'level':STATUS_WARN})
                 error_count += 1 # Count as a file that couldn't be processed
                 continue # Skip this file info

            try:
                # extract_file uses the loaded arc object's state and path
                file_data = arc.extract_file(file_info, str(arc_path)) # Pass arc_path for consistency

                # Construct the full output path including subdirectories from the filename
                # Use pathlib, it handles separators correctly.
                relative_file_path_str = file_info.get("full_filename", "") # Defensive get
                # Sanitize filename components minimally to prevent path traversal or invalid names
                safe_components = []
                # Split path, sanitize each component individually
                for component in pathlib.Path(relative_file_path_str).parts:
                    # Remove/replace problematic characters. Example: ':' on Windows, null bytes, .. for traversal.
                    safe_comp = component.replace(':', '_').replace('\x00', '').replace('..', '__')
                    # Add more replacements if needed based on OS
                    # Windows invalid chars: < > : " / \ | ? *
                    safe_comp = safe_comp.replace('<', '_').replace('>', '_').replace('"', '_').replace('|', '_').replace('?', '_').replace('*', '_').replace('/', '_').replace('\\', '_')

                    # Avoid adding empty components unless it's the root (not applicable here as we start relative)
                    if safe_comp:
                         safe_components.append(safe_comp)

                # Handle case where filename is empty or only separators resulted in no safe components
                if not safe_components:
                     status_queue.put({'type':'status','msg':f"  Skipping entry with invalid/empty derived filename in {arc_filename}",'level':STATUS_WARN})
                     error_count += 1
                     continue

                # Create the safe path relative to the output folder
                # Join components robustly using joinpath
                output_file_path = output_folder.joinpath(*safe_components)

                # Ensure parent directories exist for the specific file path
                output_file_path.parent.mkdir(parents=True, exist_ok=True)

                # Write the extracted file data
                with open(output_file_path, 'wb') as out_f: out_f.write(file_data)
                processed_count += 1

            except OSError as e: # Catch OS errors like invalid filename characters or path issues
                 status_queue.put({'type': 'status', 'msg': f"  OS Error writing '{file_info.get('full_filename','?')}' from {arc_filename}: {e}", 'level': STATUS_ERROR})
                 status_queue.put({'type':'status','msg':f"  Trace: {traceback.format_exc()}",'level':STATUS_DEBUG}) # Log traceback for debug info
                 error_count += 1
            except Exception as e:
                # Log error for this specific file extraction, but continue with the next file in the ARC
                status_queue.put({'type': 'status', 'msg': f"  Error extracting '{file_info.get('full_filename','?')}' from {arc_filename}: {e}", 'level': STATUS_ERROR})
                status_queue.put({'type':'status','msg':f"  Trace: {traceback.format_exc()}",'level':STATUS_DEBUG}) # Log traceback for debug info
                error_count += 1

        # Check if any files were successfully processed
        if processed_count > 0 and error_count == 0:
            # All files extracted successfully
            status_queue.put({'type': 'status', 'msg': f"Finished extracting {arc_filename} ({processed_count} files)", 'level': STATUS_SUCCESS})
            return arc_filename, True # Signal overall success for this ARC
        elif processed_count > 0 and error_count > 0:
            # Some files extracted, some failed
            status_queue.put({'type': 'status', 'msg': f"Finished extracting {arc_filename} with errors ({processed_count} successful, {error_count} failed)", 'level': STATUS_WARN})
            return arc_filename, False # Signal partial success/warning for this ARC
        elif error_count > 0:
             # No files extracted, only errors occurred within the ARC
             status_queue.put({'type': 'status', 'msg': f"Failed to extract any files from {arc_filename} ({error_count} errors)", 'level': STATUS_ERROR})
             return arc_filename, False # Signal total failure for this ARC
        else: # Should only happen if arc.files was empty (valid case)
             status_queue.put({'type': 'status', 'msg': f"No files found in {arc_filename}.", 'level': STATUS_INFO})
             return arc_filename, True # Treat as success if ARC was empty


    except (FileNotFoundError, PermissionError, IOError, ValueError, RuntimeError) as e:
         # Catch specific anticipated errors from load or setup
         status_queue.put({'type':'status','msg':f"Failed loading/processing ARC {arc_path.name}: {e}",'level':STATUS_ERROR}); return arc_path.name,False
    except Exception as e:
        # Catch any other unexpected errors during ARC loading or initial setup
        status_queue.put({'type': 'status', 'msg': f"An unexpected error occurred processing ARC {arc_path.name}: {e}", 'level': STATUS_ERROR})
        status_queue.put({'type':'status','msg':f"Trace: {traceback.format_exc()}",'level':STATUS_DEBUG}) # Log traceback for debug info
        return arc_path.name, False # Signal failure

    finally:
        # Ensure MTArc resources are closed (though currently doesn't hold files open persistently)
        if arc: arc.close()


# Worker for single folder based injection
# _list_inject_worker(source_folder_str, output_rebuilt_dir_str, key1, key2, status_queue)
# Also used for Folder Inject Dir
def _list_inject_worker(source_folder_str: str, output_rebuilt_dir_str: str, key1: str | None, key2: str | None, status_queue: queue.Queue):
    """Worker to rebuild a single ARC from a source folder."""
    source_folder_path = pathlib.Path(source_folder_str)
    output_rebuilt_dir = pathlib.Path(output_rebuilt_dir_str)
    arc = None # Initialize arc object

    try:
        folder_name = source_folder_path.name
        output_arc_path = output_rebuilt_dir / f"{folder_name}.arc"
        status_queue.put({'type': 'status', 'msg': f"Processing folder {folder_name} for rebuild...", 'level': STATUS_DEBUG})

        files_to_pack = []
        has_files_in_folder = False # Flag to check if folder contains any files
        error_reading_files = False # Flag to track if any file read errors occurred

        # Use scandir and handle potential errors during directory listing or file reading
        try:
            # Ensure source folder exists and is accessible
            if not source_folder_path.is_dir():
                 raise FileNotFoundError(f"Source folder not found: {source_folder_path.name}")
            if not os.access(source_folder_path, os.R_OK):
                 raise PermissionError(f"Read permission denied for folder: {source_folder_path.name}")

            # Iterate through top-level entries in the source folder
            for entry in os.scandir(source_folder_path):
                # Check if entry is a file and readable
                try:
                    if entry.is_file():
                        has_files_in_folder = True
                        filename = entry.name; full_path = entry.path
                        # status_queue.put({'type':'status','msg':f"  Adding {filename}",'level':STATUS_DEBUG}) # Too noisy
                        # Check read permission for the file itself
                        if not os.access(full_path, os.R_OK):
                            status_queue.put({'type':'status','msg':f"  Permission denied reading file {filename} in {folder_name}. Skipping.",'level':STATUS_ERROR})
                            error_reading_files = True
                            continue # Skip this file

                        try:
                            # Read file data
                            with open(full_path, 'rb') as f: data = f.read()

                            # Create file_info dictionary
                            fi=create_file_info();
                            fi["full_filename"]=filename; # Store original filename
                            base,ext=os.path.splitext(filename)

                            # Encode base filename bytes (truncated to 64)
                            try:fnb=base.encode('ascii')
                            except UnicodeEncodeError:fnb=base.encode('utf-8',errors='ignore')
                            fi["filename_base"]=fnb[:64];

                            # Calculate hash for extension
                            # Get extension without the dot, handle empty extension case
                            ext_without_dot = ext[1:] if ext and len(ext) > 1 else ""
                            # Look up in reverse map first (from MHGU file), fallback to calculation
                            fi["ext_hash"]=REV_EXTENSION_MAP.get(ext.lower(), calculate_arc_hash(ext_without_dot)) # Prioritize map


                            fi["data"]=data; # Store actual file data
                            fi["platform"]=Platform.Switch; # Force Switch for packing
                            fi["unknown1"]=0; # Default unknown1 for new files (based on typical v9)

                            # Basic validation on file size? Max file size in ARC metadata is int (2GB)
                            if len(data) > 0x7FFFFFFF: # Approx max signed int size
                                 status_queue.put({'type':'status','msg':f"  Warning: File {filename} is very large ({len(data)} bytes), may exceed max size supported by ARC entry metadata.",'level':STATUS_WARN})
                                 # Continue, but it might fail during packing/struct writing

                            files_to_pack.append(fi) # Add to the list of files to pack

                        except Exception as e:
                            # Catch errors during file reading
                            status_queue.put({'type':'status','msg':f"  Error reading {filename} from {folder_name}:{e}",'level':STATUS_ERROR})
                            status_queue.put({'type':'status','msg':f"  Trace: {traceback.format_exc()}",'level':STATUS_DEBUG})
                            error_reading_files = True # Mark that an error occurred

                    elif entry.is_dir():
                         status_queue.put({'type':'status','msg':f"  Skipping subdirectory {entry.name} in {folder_name}. Only packing top-level files.",'level':STATUS_WARN})
                    # else: skip other entry types like symlinks, fifos, etc.

                # Catch errors related to entry status/metadata (e.g., broken symlink)
                except OSError as e:
                     status_queue.put({'type':'status','msg':f"  Error accessing entry {entry.name} in {folder_name}: {e}. Skipping.",'level':STATUS_ERROR})
                     error_reading_files = True # Count as an error
                except Exception as e:
                     # Catch any other unexpected error during entry processing
                     status_queue.put({'type':'status','msg':f"  An unexpected error accessing {entry.name} in {folder_name}: {e}. Skipping.",'level':STATUS_ERROR});
                     status_queue.put({'type':'status','msg':f"  Trace: {traceback.format_exc()}",'level':STATUS_DEBUG});
                     error_reading_files = True

            # End scandir loop

        except (FileNotFoundError, PermissionError) as e:
             status_queue.put({'type':'status','msg':f"Error accessing input folder {folder_name}: {e}",'level':STATUS_ERROR}); return folder_name,False
        except Exception as e:
            # Catch unexpected errors during initial directory scanning
            status_queue.put({'type':'status','msg':f"An unexpected error occurred scanning folder {folder_name}: {e}",'level':STATUS_ERROR});
            status_queue.put({'type':'status','msg':f"Trace: {traceback.format_exc()}",'level':STATUS_DEBUG});
            return folder_name,False # Signal failure due to scan error


        # Check results after scanning the folder
        if not has_files_in_folder: # Folder contained no files (might have only subdirs or be empty)
            status_queue.put({'type':'status','msg':f"Skipping empty folder: {folder_name}",'level':STATUS_WARN}); return folder_name,False
        if not files_to_pack: # Folder had entries, but none were successfully read/processed into files_to_pack
            status_queue.put({'type':'status','msg':f"Skipping folder {folder_name} as no files were successfully read.",'level':STATUS_ERROR}); return folder_name,False
        if error_reading_files:
             status_queue.put({'type': 'status', 'msg': f"Warning: Some files in {folder_name} had read errors and were skipped.", 'level': STATUS_WARN})


        # Sort files alphabetically by full filename before packing (for consistency)
        try: files_to_pack.sort(key=lambda fi: fi.get("full_filename", "")) # Use defensive get for key
        except Exception as e:
             print(f"Warning: Failed to sort files for folder {folder_name}: {e}", file=sys.stderr)
             status_queue.put({'type':'status','msg':f"Warning: Failed to sort files for {folder_name}.",'level':STATUS_WARN})
             # Continue without sorting if sort fails


        status_queue.put({'type':'status','msg':f" Rebuilding {output_arc_path.name} ({len(files_to_pack)} files){' (Encrypted)' if key1 and key2 else ''}...",'level':STATUS_INFO})
        arc = MTArc(); # Create new instance for saving

        # Ensure output directory exists and is writable before saving
        try: output_rebuilt_dir.mkdir(parents=True, exist_ok=True)
        except Exception as e:
             raise IOError(f"Failed to create output directory {output_rebuilt_dir}: {e}") from e

        # Check write permission for the specific output file path *or* its parent if it doesn't exist
        if output_arc_path.exists():
            if not os.access(output_arc_path, os.W_OK):
                 raise PermissionError(f"Write permission denied for existing output file: {output_arc_path.name}")
        # Check parent permission if output file doesn't exist
        elif not output_arc_path.parent.exists():
            # If parent dir doesn't exist, mkdir should have created it or failed
            raise IOError(f"Output parent directory does not exist: {output_arc_path.parent}")
        elif not os.access(output_arc_path.parent, os.W_OK):
             raise PermissionError(f"Write permission denied for output directory: {output_rebuilt_dir.name}")

        # Check if the destination is the source folder itself (avoid overwriting input with partial output)
        if source_folder_path.resolve() == output_arc_path.parent.resolve():
             # This logic is flawed - output parent is the directory, source is the dir inside.
             # Need to check if output *file* path is inside source *folder* path.
             try:
                 # Use resolve() for both for robust comparison of absolute paths
                 if output_arc_path.resolve().is_relative_to(source_folder_path.resolve()):
                    status_queue.put({'type':'status','msg':f"Error: Output ARC path '{output_arc_path.name}' would be inside the input folder '{folder_name}'. Aborting save.",'level':STATUS_ERROR})
                    return folder_name, False
             except ValueError: pass # Happens if paths are on different drives/not relative


        # Save the ARC file - arc.save handles encryption and writing
        arc.save(str(output_arc_path), files_to_pack, key1=key1, key2=key2) # Save can raise exceptions

        status_queue.put({'type':'status','msg':f"Successfully rebuilt {output_arc_path.name}",'level':STATUS_SUCCESS})
        return folder_name, True # Signal success

    except (FileNotFoundError, PermissionError, IOError, ValueError, RuntimeError) as e:
         # Catch specific anticipated errors and report them
         status_queue.put({'type':'status','msg':f"Failed processing folder {folder_name}: {e}",'level':STATUS_ERROR});
         status_queue.put({'type':'status','msg':f"Trace: {traceback.format_exc()}",'level':STATUS_DEBUG}) # Log traceback for debug info
         return folder_name,False
    except Exception as e:
        # Catch any unexpected error during the rest of processing (save)
        status_queue.put({'type': 'status', 'msg': f"An unexpected error occurred processing folder {source_folder_path.name}: {e}", 'level': STATUS_ERROR})
        status_queue.put({'type':'status','msg':f"Trace: {traceback.format_exc()}",'level':STATUS_DEBUG}) # Log traceback for debug info
        return source_folder_path.name, False # Signal failure
    finally:
        # Ensure MTArc resources are closed (though currently doesn't hold files open persistently)
        if arc: arc.close()


# Orchestrator for single file/folder lists
def run_batch_parallel(worker_func, item_list, output_dir, progress_callback, status_callback, key1, key2, max_workers=None):
    """Runs a batch of tasks (items) in parallel using a worker function."""
    if not item_list:
        status_callback("No items selected for batch.", STATUS_WARN); progress_callback(100); return

    # Basic validation on output directory before starting threads
    if not output_dir: # Check if string is empty
         status_callback("Output directory path is empty.", STATUS_ERROR); progress_callback(0); return
    output_path = pathlib.Path(output_dir)
    # Validate output directory exists and is writable
    try:
        if output_path.exists(): # Check if directory exists
            if not output_path.is_dir(): raise NotADirectoryError(f"Output path exists but is not a directory: {output_dir}")
            if not os.access(output_path, os.W_OK): raise PermissionError(f"Write permission denied for output directory: {output_dir}")
        else: output_path.mkdir(parents=True, exist_ok=True) # Attempt to create if it doesn't exist
    except Exception as e:
         status_callback(f"Output directory error: {e}", STATUS_ERROR); progress_callback(0); return


    total_tasks = len(item_list)
    status_callback(f"Starting parallel batch processing for {total_tasks} items...", STATUS_INFO)
    completed_tasks = 0 # Track completed tasks to update progress

    # Determine max workers (default to number of CPU cores or a fixed number if needed)
    # Using default None lets ThreadPoolExecutor decide based on cores/io
    # max_workers = max_workers if max_workers is not None else os.cpu_count() or 1
    # For I/O bound tasks, sometimes more than cores is beneficial, but let's use default for now.

    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        status_queue = queue.Queue() # Queue for status updates from workers
        # Submit tasks: worker needs (item_path_str, output_dir_str, k1, k2, queue)
        # Ensure item is a string path for the worker if it comes from a listbox
        futures = [executor.submit(worker_func, str(item), str(output_path), key1, key2, status_queue) for item in item_list]

        # Process results as they complete and drain status queue
        for future in concurrent.futures.as_completed(futures):
            # Process any status messages from the queue first
            while not status_queue.empty():
                try: msg = status_queue.get_nowait(); status_callback(msg['msg'], msg['level'])
                except queue.Empty: break

            try:
                # Get result (or exception if worker failed)
                item_name, success = future.result()
                # The worker already reported specific success/failure messages for the item
            except Exception as e:
                # Catch critical errors from worker thread (e.g., unexpected crashes)
                status_callback(f"Critical error from worker thread processing result: {e}", STATUS_ERROR)
                status_callback(f"Trace: {traceback.format_exc()}", STATUS_DEBUG)

            completed_tasks += 1
            # Update main progress bar
            progress_callback(completed_tasks / total_tasks * 100)

    # Final status queue drain after all futures are completed
    while not status_queue.empty():
        try: msg = status_queue.get_nowait(); status_callback(msg['msg'], msg['level'])
        except queue.Empty: break

    status_callback("Batch operation complete.", STATUS_SUCCESS)


# --- Recursive Extract Worker and Orchestrator ---
# (_list_extract_worker is used as the worker for recursive extract)

def recursive_batch_extract(source_root_dir: str, output_base_dir: str, progress_callback: callable, status_callback: callable, key1: str | None, key2: str | None, max_workers=None):
    """Finds all .arc files recursively and extracts them in parallel."""
    status_callback("Scanning for ARC files...", STATUS_INFO)
    source_path = pathlib.Path(source_root_dir)
    output_path = pathlib.Path(output_base_dir)

    # Input validation
    if not source_root_dir: status_callback("Input Missing: Please select source directory.", STATUS_ERROR); progress_callback(0); return # Basic GUI-level check duplicated for safety
    if not output_base_dir: status_callback("Output Missing: Please select output base directory.", STATUS_ERROR); progress_callback(0); return # Basic GUI-level check duplicated for safety

    if not source_path.is_dir():
         status_callback("Source directory not found or is not a directory.", STATUS_ERROR); progress_callback(0); return
    # Validate and/or create output directory
    try:
        if not output_path.exists(): output_path.mkdir(parents=True, exist_ok=True)
        elif not output_path.is_dir(): raise NotADirectoryError(f"Output path exists but is not a directory: {output_base_dir}")
        if not os.access(output_path, os.W_OK): raise PermissionError(f"Write permission denied for output directory: {output_base_dir}")
        if not os.access(source_path, os.R_OK): raise PermissionError(f"Read permission denied for source directory: {source_root_dir}")
    except Exception as e:
        status_callback(f"Directory validation error: {e}", STATUS_ERROR); progress_callback(0); return


    try: arc_files = list(source_path.rglob('*.arc')) # Find all .arc files recursively
    except Exception as e:
         status_callback(f"Error scanning source directory for ARC files: {e}", STATUS_ERROR); progress_callback(0); return


    if not arc_files:
        status_callback("No *.arc files found in the source directory.", STATUS_WARN); progress_callback(100); return

    total_files = len(arc_files)
    status_callback(f"Found {total_files} ARC files. Starting parallel extraction...", STATUS_INFO)
    completed_tasks = 0 # Track completed tasks

    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        status_queue = queue.Queue() # Queue for status updates from workers
        # Submit tasks: worker needs (arc_path_str, output_base_dir_str, k1, k2, queue)
        # CORRECTED: Call _list_extract_worker
        futures = [executor.submit(_list_extract_worker, str(arc_file), str(output_path), key1, key2, status_queue) for arc_file in arc_files]

        for future in concurrent.futures.as_completed(futures):
            # Process any status messages from the queue first
            while not status_queue.empty():
                try: msg = status_queue.get_nowait(); status_callback(msg['msg'], msg['level'])
                except queue.Empty: break

            try:
                # Get result (or exception if worker failed)
                arc_name, success = future.result()
                # Worker already printed specific success/failure for the file
            except Exception as e:
                status_callback(f"Critical error from worker thread processing result: {e}", STATUS_ERROR)
                status_callback(f"Trace: {traceback.format_exc()}", STATUS_DEBUG)

            completed_tasks += 1
            # CORRECTED: Use total_files for calculation
            progress_callback(completed_tasks / total_files * 100)

    # Final status queue drain
    while not status_queue.empty():
        try: msg = status_queue.get_nowait(); status_callback(msg['msg'], msg['level'])
        except queue.Empty: break

    status_callback("Recursive batch extraction complete.", STATUS_SUCCESS)


# --- Folder Inject Worker and Orchestrator ---
# (_list_inject_worker is used as the worker for folder inject)

def folder_batch_inject(original_arc_dir: str, edited_content_dir: str, output_rebuilt_dir: str, progress_callback: callable, status_callback: callable, key1: str | None, key2: str | None, max_workers=None):
    """Matches edited folders to original ARCs and rebuilds them in parallel."""
    status_callback("Scanning for edited content folders and matching ARCs...", STATUS_INFO)
    original_path = pathlib.Path(original_arc_dir)
    edited_path = pathlib.Path(edited_content_dir)
    output_path = pathlib.Path(output_rebuilt_dir)

    # Input validation
    if not original_arc_dir: status_callback("Input Missing: Select Original ARC directory.", STATUS_ERROR); progress_callback(0); return
    if not edited_content_dir: status_callback("Input Missing: Select Edited Content directory.", STATUS_ERROR); progress_callback(0); return
    if not output_rebuilt_dir: status_callback("Output Missing: Select Output directory.", STATUS_ERROR); progress_callback(0); return

    if not original_path.is_dir(): status_callback("Original ARC dir not found.", STATUS_ERROR); progress_callback(0); return
    if not edited_path.is_dir(): status_callback("Edited content dir not found.", STATUS_ERROR); progress_callback(0); return
    if not os.access(original_path, os.R_OK): status_callback("Read permission denied for original ARC dir.", STATUS_ERROR); progress_callback(0); return
    if not os.access(edited_path, os.R_OK): status_callback("Read permission denied for edited content dir.", STATUS_ERROR); progress_callback(0); return
    try: # Validate and/or create output directory
        if output_path.exists():
            if not output_path.is_dir(): raise NotADirectoryError(f"Output path exists but is not a directory: {output_rebuilt_dir}")
            if not os.access(output_path, os.W_OK): raise PermissionError(f"Write permission denied for output directory: {output_rebuilt_dir}")
        else: output_path.mkdir(parents=True, exist_ok=True)
    except Exception as e: status_callback(f"Output directory error: {e}", STATUS_ERROR); progress_callback(0); return

    tasks = [] # List of (edited_folder_path, original_arc_path, output_arc_path) tuples
    try: # Scan for tasks
        # Iterate through the edited content directory's top-level items
        for entry in edited_path.iterdir():
            if entry.is_dir():
                folder_name = entry.name
                orig_arc = original_path / f"{folder_name}.arc"
                out_arc = output_path / f"{folder_name}.arc"
                if orig_arc.is_file():
                    if os.access(orig_arc, os.R_OK):
                        # Check for output overwriting input sources
                        if orig_arc.resolve() == out_arc.resolve(): status_queue.put({'type':'status','msg':f"Skipping '{folder_name}': Output path is same as original ARC.",'level':STATUS_ERROR}); continue
                        try:
                             # Check if output path is *inside* the input edited folder (avoid overwriting input files)
                             # Use resolve() for both for robust comparison of absolute paths
                             if out_arc.resolve().is_relative_to(entry.resolve()):
                                status_queue.put({'type':'status','msg':f"Skipping '{folder_name}': Output ARC path '{out_arc.name}' would be inside the input edited folder '{entry.name}'. Aborting task.",'level':STATUS_ERROR})
                                continue # Skip this task
                         # Catch ValueError if paths are on different drives/not relative
                        except ValueError: pass # No relation, safe

                        tasks.append((entry, orig_arc, out_arc))
                    else: status_queue.put({'type':'status','msg':f"Skipping '{folder_name}': Read permission denied for original ARC '{orig_arc.name}'.", 'level': STATUS_WARN}); continue
                else: status_queue.put({'type':'status','msg':f"Skipping '{folder_name}': Matching original ARC not found at '{orig_arc.name}'.", 'level': STATUS_WARN}); continue
            # else: skip files or other entries at the top level of edited_content_dir
    except Exception as e: status_queue.put( {'type':'status','msg':f"Error scanning directories for tasks: {e}",'level':STATUS_ERROR}); status_queue.put({'type':'status','msg':f"Trace:{traceback.format_exc()}",'level':STATUS_DEBUG}); progress_callback(0); return

    if not tasks: status_queue("No matching folders with readable original ARCs found.", STATUS_WARN); progress_callback(100); return

    total_tasks = len(tasks); status_queue(f"Found {total_tasks} folders/ARCs to process. Starting parallel rebuild...", STATUS_INFO);
    completed_tasks = 0 # Track completed tasks

    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        status_queue = queue.Queue()
        # Submit tasks: worker needs (edited_folder_path_str, output_rebuilt_dir_str, k1, k2, queue)
        # Pass edited_folder_path_str and output_path_str (as the base for rebuilt ARCs)
        futures = [executor.submit(_list_inject_worker, str(task[0]), str(output_path), key1, key2, status_queue) for task in tasks]

        for future in concurrent.futures.as_completed(futures):
            while not status_queue.empty():
                try: msg = status_queue.get_nowait(); status_callback(msg['msg'], msg['level'])
                except queue.Empty: break
            try: folder_name, success = future.result() # Worker reports success/failure
            except Exception as e: status_callback(f"Critical error from worker thread result: {e}", STATUS_ERROR); status_callback(f"Trace: {traceback.format_exc()}", STATUS_DEBUG)
            completed_tasks += 1; progress_callback(completed_tasks / total_tasks * 100)

    while not status_queue.empty():
        try: msg = status_queue.get_nowait(); status_callback(msg['msg'], msg['level'])
        except queue.Empty: break
    status_callback("Folder batch injection (rebuild) complete.", STATUS_SUCCESS)


# --- GUI CODE ---
class ArcToolApp:
    def __init__(self, root):
        self.root = root
        self.root.title("SaladSoftware ARC Tool")
        # root.geometry("800x700") # Let Tkinter calculate size based on widgets
        self.root.configure(bg=BG_COLOR)

        # --- Fonts ---
        self.default_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE)
        self.bold_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE, weight="bold")

        # --- Thread-safe Queue ---
        self.queue = queue.Queue() # Queue for thread-safe updates from workers

        # --- Style Configuration ---
        self.style = ttk.Style()
        self.configure_styles()

        # --- Encryption Key Inputs (Keep at top) ---
        #key_frame = ttk.Frame(root, style='TFrame'); key_frame.pack(pady=5, padx=10, fill='x')
        # ttk.Label(key_frame, text="Blowfish Keys (Optional for Encrypted ARCs):", style='Header.TLabel').grid(row=0, column=0, columnspan=4, sticky='w')
        # ttk.Label(key_frame, text="Key 1:").grid(row=1, column=0, sticky='w', padx=5)
        #self.key1_var = tk.StringVar(); # Assign StringVar first
        #key1_entry = ttk.Entry(key_frame, textvariable=self.key1_var, width=30, show='*'); key1_entry.grid(row=1, column=1, sticky='ew', padx=5)
        #ttk.Label(key_frame, text="Key 2:").grid(row=1, column=2, sticky='w', padx=5)
        #self.key2_var = tk.StringVar(); # Assign StringVar first
        # Corrected column assignment
        #key2_entry = ttk.Entry(key_frame, textvariable=self.key2_var, width=30, show='*'); key2_entry.grid(row=1, column=3, sticky='ew', padx=5)
        #key_frame.grid_columnconfigure(1, weight=1); key_frame.grid_columnconfigure(3, weight=1)

        # --- Main Structure (4 Tabs) ---
        self.notebook = ttk.Notebook(root, style='TNotebook')
        self.list_extract_frame = ttk.Frame(self.notebook, style='TFrame')
        self.list_inject_frame = ttk.Frame(self.notebook, style='TFrame')
        self.rec_extract_frame = ttk.Frame(self.notebook, style='TFrame')
        self.folder_inject_frame = ttk.Frame(self.notebook, style='TFrame')

        # Add tabs to the notebook
        self.notebook.add(self.list_extract_frame, text='Extract Files (List)')
        self.notebook.add(self.list_inject_frame, text='Inject Folders (List)')
        self.notebook.add(self.rec_extract_frame, text='Recursive Extract Dir')
        self.notebook.add(self.folder_inject_frame, text='Folder Inject Dir')
        self.notebook.pack(pady=5, padx=10, expand=True, fill='both')

        # Populate ALL tabs
        self.create_list_extract_widgets()
        self.create_list_inject_widgets()
        self.create_recursive_extract_widgets()
        self.create_folder_inject_widgets()

        # --- Status Bar & Progress Bar ---
        # Pack these from the bottom so they stay there
        self.status_frame = ttk.Frame(root, style='Status.TFrame', height=100); self.status_frame.pack(pady=(0, 5), padx=10, fill='x', side=tk.BOTTOM)
        self.status_frame.grid_rowconfigure(0, weight=1); self.status_frame.grid_columnconfigure(0, weight=1)
        # Increased height for status text
        self.status_text = scrolledtext.ScrolledText(self.status_frame, wrap=tk.WORD, font=self.default_font, bg=WIDGET_BG, fg=TEXT_COLOR, bd=1, relief='sunken', height=8);
        self.status_text.grid(row=0, column=0, sticky='nsew'); self.status_text.configure(state='disabled')
        # Configure tags for status colors
        self.status_text.tag_config(STATUS_ERROR, foreground=STATUS_ERROR_FG); self.status_text.tag_config(STATUS_WARN, foreground=STATUS_WARN_FG); self.status_text.tag_config(STATUS_SUCCESS, foreground=STATUS_SUCCESS_FG); self.status_text.tag_config(STATUS_INFO, foreground=STATUS_INFO_FG); self.status_text.tag_config(STATUS_DEBUG, foreground=STATUS_DEBUG_FG)

        self.progress_var = tk.DoubleVar(); # Variable for progress bar
        self.progress_bar = ttk.Progressbar(root, orient='horizontal', length=100, mode='determinate', variable=self.progress_var, style='TProgressbar');
        self.progress_bar.pack(pady=(0, 10), padx=10, fill='x', side=tk.BOTTOM) # Pack at bottom

        # Start checking the queue for updates from worker threads
        self.check_queue()

    def configure_styles(self):
        """Configures the ttk styles for the GUI elements."""
        self.style.theme_use('clam'); # Use 'clam' for better color control
        # General widget settings
        self.style.configure('.',background=BG_COLOR,foreground=TEXT_COLOR,font=self.default_font,fieldbackground=WIDGET_BG,troughcolor=BG_COLOR,borderwidth=1);
        self.style.map('.',foreground=[('disabled','#aaaaaa')]);
        # Specific widget styles
        self.style.configure('TFrame',background=BG_COLOR);
        self.style.configure('Status.TFrame',background=BG_COLOR);
        self.style.configure('TLabel',background=BG_COLOR,foreground=TEXT_COLOR,padding=5);
        self.style.configure('Header.TLabel',font=self.bold_font,foreground=TEXT_COLOR);
        # Button styles
        self.style.configure('TButton',background=BUTTON_BG,foreground=BUTTON_FG,bordercolor=BUTTON_BORDER,focuscolor=HIGHLIGHT_BG,lightcolor=BUTTON_BG,darkcolor=BUTTON_BG,padding=6);
        self.style.map('TButton',background=[('active',BUTTON_ACTIVE_BG),('pressed',BUTTON_PRESSED_BG)],foreground=[('active',BUTTON_FG),('pressed',BUTTON_FG)]);
        # Entry (Input) styles
        self.style.configure('TEntry',fieldbackground=WIDGET_BG,foreground=INPUT_TEXT_COLOR,insertcolor=INPUT_TEXT_COLOR,bordercolor=BUTTON_BORDER);
        self.style.map('TEntry',selectbackground=[('focus',HIGHLIGHT_BG)],selectforeground=[('focus',HIGHLIGHT_TEXT)]);
        # Listbox styles (using tk.Listbox, style applied via root.option_add)
        self.root.option_add('*Listbox*background',WIDGET_BG);
        self.root.option_add('*Listbox*foreground',TEXT_COLOR);
        self.root.option_add('*Listbox*selectBackground',HIGHLIGHT_BG);
        self.root.option_add('*Listbox*selectForeground',HIGHLIGHT_TEXT);
        self.root.option_add('*Listbox*font',self.default_font);
        self.root.option_add('*Listbox*bd',1);
        self.root.option_add('*Listbox*relief','sunken');
        # Notebook (Tab) styles
        self.style.configure('TNotebook',background=BG_COLOR,borderwidth=0);
        self.style.configure('TNotebook.Tab',background=HEADER_BG,foreground=HEADER_TEXT,padding=[10,5],font=self.default_font,borderwidth=1);
        self.style.map('TNotebook.Tab',background=[('selected',HEADER_ACTIVE_BG)],foreground=[('selected',HEADER_ACTIVE_TEXT)],expand=[('selected',[1,1,1,1])]);
        # Progressbar styles
        self.style.configure('TProgressbar',thickness=20,background=STATUS_SUCCESS_FG,troughcolor=WIDGET_BG);


    # --- Widget Creation Methods for all 4 tabs ---
    def _create_dir_input(self, parent, label, row, var_name):
        """Helper to create Label/Entry/Button row for directory input."""
        ttk.Label(parent, text=label, style='Header.TLabel').grid(row=row, column=0, sticky='w', padx=5, pady=(10,2))
        frame=ttk.Frame(parent); frame.grid(row=row+1, column=0, sticky='ew', padx=5, pady=(0,5)); frame.grid_columnconfigure(0, weight=1)

        v=tk.StringVar(); setattr(self, var_name, v); # Create and store the variable
        e=ttk.Entry(frame, textvariable=v, width=60); e.grid(row=0, column=0, sticky='ew')
        b=ttk.Button(frame, text="Browse...", command=lambda v=v: self._select_directory(v)); b.grid(row=0, column=1, padx=(5,0))
        return v # Return the variable for convenience

    def _select_directory(self, string_var):
        """Callback for Browse directory buttons."""
        directory=filedialog.askdirectory(title="Select Directory")
        if directory: string_var.set(directory)


    def create_list_extract_widgets(self):
        """Widgets for the 'Extract Files (List)' tab."""
        frame=self.list_extract_frame; frame.grid_columnconfigure(0, weight=1); frame.grid_rowconfigure(1, weight=1) # Configure resizing
        ttk.Label(frame, text="Input ARC Files:", style='Header.TLabel').grid(row=0, column=0, columnspan=3, sticky='w', pady=(10,5))
        self.list_extract_listbox=tk.Listbox(frame, width=80, height=10, selectmode=tk.EXTENDED); self.list_extract_listbox.grid(row=1, column=0, columnspan=2, padx=5, pady=5, sticky='nsew')
        sb=ttk.Scrollbar(frame, orient='vertical', command=self.list_extract_listbox.yview); sb.grid(row=1, column=2, sticky='nsw', pady=5); self.list_extract_listbox.config(yscrollcommand=sb.set)
        bf=ttk.Frame(frame); bf.grid(row=2, column=0, columnspan=2, sticky='ew') # Button frame
        ttk.Button(bf, text="Select Files", command=self.select_list_extract_files).pack(side=tk.LEFT, padx=5, pady=5)
        ttk.Button(bf, text="Clear List", command=lambda: self.list_extract_listbox.delete(0, tk.END)).pack(side=tk.RIGHT, padx=5, pady=5)
        self._create_dir_input(frame, "Output Directory:", 3, "list_extract_output_var")
        ttk.Button(frame, text="Start Extraction", command=self.start_list_extraction).grid(row=5, column=0, columnspan=3, pady=(20,10))

    def create_list_inject_widgets(self):
        """Widgets for the 'Inject Folders (List)' tab."""
        frame=self.list_inject_frame; frame.grid_columnconfigure(0, weight=1); frame.grid_rowconfigure(1, weight=1) # Configure resizing
        ttk.Label(frame, text="Input Source Folders:", style='Header.TLabel').grid(row=0, column=0, columnspan=3, sticky='w', pady=(10,5))
        self.list_inject_listbox=tk.Listbox(frame, width=80, height=10, selectmode=tk.EXTENDED); self.list_inject_listbox.grid(row=1, column=0, columnspan=2, padx=5, pady=5, sticky='nsew')
        sb=ttk.Scrollbar(frame, orient='vertical', command=self.list_inject_listbox.yview); sb.grid(row=1, column=2, sticky='nsw', pady=5); self.list_inject_listbox.config(yscrollcommand=sb.set)
        bf=ttk.Frame(frame); bf.grid(row=2, column=0, columnspan=2, sticky='ew') # Button frame
        ttk.Button(bf, text="Add Folder(s)", command=self.select_list_inject_folders).pack(side=tk.LEFT, padx=5, pady=5)
        ttk.Button(bf, text="Clear List", command=lambda: self.list_inject_listbox.delete(0, tk.END)).pack(side=tk.RIGHT, padx=5, pady=5)
        self._create_dir_input(frame, "Output Rebuilt ARC Directory:", 3, "list_inject_output_var")
        ttk.Button(frame, text="Start Rebuild", command=self.start_list_injection).grid(row=5, column=0, columnspan=3, pady=(20,10))

    def create_recursive_extract_widgets(self):
        """Widgets for the 'Recursive Extract Dir' tab."""
        frame=self.rec_extract_frame; frame.grid_columnconfigure(0, weight=1); # Configure resizing
        self._create_dir_input(frame, "Source ARC Directory (Recursive):", 0, "rec_extract_source_var")
        self._create_dir_input(frame, "Output Base Directory:", 2, "rec_extract_output_var")
        ttk.Button(frame, text="Start Recursive Extraction", command=self.start_recursive_extraction).grid(row=4, column=0, pady=(20,10))

    def create_folder_inject_widgets(self):
        """Widgets for the 'Folder Inject Dir' tab."""
        frame=self.folder_inject_frame; frame.grid_columnconfigure(0, weight=1); # Configure resizing
        self._create_dir_input(frame, "Original ARC Directory:", 0, "folder_inject_orig_arc_var")
        self._create_dir_input(frame, "Edited Content Directory (Contains Folders):", 2, "folder_inject_edited_dir_var")
        self._create_dir_input(frame, "Output Rebuilt ARC Directory:", 4, "folder_inject_output_var")
        ttk.Button(frame, text="Start Folder Injection", command=self.start_folder_injection).grid(row=6, column=0, pady=(20,10))


    # --- File/Folder Selection Logic ---
    def select_list_extract_files(self):
        """Opens file dialog to select multiple .arc files and adds them to the listbox."""
        files=filedialog.askopenfilenames(title="Select ARC Files", filetypes=[("MT ARC","*.arc"),("All Files","*.*")])
        if files:
            # Add files only if they are not already in the listbox
            current_items = set(self.list_extract_listbox.get(0, tk.END))
            for f in files:
                if f not in current_items:
                    self.list_extract_listbox.insert(tk.END, f)

    def select_list_inject_folders(self):
        """Opens directory dialog to select a folder and adds it to the listbox."""
        directory=filedialog.askdirectory(title="Select Source Folder")
        if directory:
            # Add directory only if not already in the listbox
            current_items = set(self.list_inject_listbox.get(0, tk.END))
            if directory not in current_items:
                 self.list_inject_listbox.insert(tk.END, directory)


    # --- Action Starters (Call _run_task) ---
    def _get_keys(self):
        """Gets encryption keys from GUI input fields. Returns (key1, key2) or (None, None). Shows warning if only one key is entered."""
        k1=self.key1_var.get();k2=self.key2_var.get()
        if k1 and k2: return k1,k2
        elif k1 or k2:
             # Only one key provided, invalid state for MTF
             messagebox.showwarning("Key Incomplete","Please enter both Key 1 and Key 2, or leave both blank for no encryption.")
             return None, None # Indicate invalid state (handled by caller checking return value)
        else: return None, None # No keys provided, valid state for unencrypted


    def _run_task(self, target_func, args_tuple):
        """Starts a batch task in a separate thread after checking keys and inputs."""
        # Get keys from GUI, handles validation check internally
        k1, k2 = self._get_keys()
        # If _get_keys returned (None, None) because only one key was entered, abort.
        # It will show a warning, no need to re-check type here.
        if k1 is None and k2 is None and (self.key1_var.get() or self.key2_var.get()):
             return # Abort if key state is invalid (user was warned)

        # Pass keys, progress callback, status queue down to the batch function
        full_args = args_tuple + (self.update_progress, self.queue_status, k1, k2)

        # Reset progress bar
        self.progress_var.set(0)

        # Use a more specific message based on the target function name
        task_name = target_func.__name__.replace('_batch', '').replace('_list', ' List').replace('_recursive', ' Recursive').replace('_folder', ' Folder').replace('_', ' ').strip().title()
        self.add_status_message(f"Starting {task_name} task...", STATUS_INFO)

        # Run the batch function in a thread
        thread = threading.Thread(target=target_func, args=full_args, daemon=True) # daemon=True allows app to exit if thread is still running
        thread.start()


    def start_list_extraction(self):
        """Initiates extraction of selected files using the parallel list runner."""
        items = self.list_extract_listbox.get(0, tk.END)
        out_dir = self.list_extract_output_var.get()

        # Input validation (basic checks, more robust checks handled in run_batch_parallel worker validation)
        if not items: messagebox.showwarning("Input Missing","Please select one or more ARC files to extract."); return
        if not out_dir: messagebox.showwarning("Output Missing","Please select an output directory."); return

        # Call the generic parallel runner with the list worker
        self._run_task(run_batch_parallel, (_list_extract_worker, items, out_dir))


    def start_list_injection(self):
        """Initiates injection (rebuild) of selected folders using the parallel list runner."""
        items = self.list_inject_listbox.get(0, tk.END)
        out_dir = self.list_inject_output_var.get()

        # Input validation (basic checks, more robust checks handled in run_batch_parallel worker validation)
        if not items: messagebox.showwarning("Input Missing","Please add one or more source folders to inject."); return
        if not out_dir: messagebox.showwarning("Output Missing","Please select an output directory."); return
        # Validate source folders exist client-side before starting thread (better user feedback)
        for folder_path in items:
            if not os.path.isdir(folder_path): messagebox.showerror("Input Invalid",f"Source folder not found: {folder_path}"); return

        # Call the generic parallel runner with the list worker and the list of items
        self._run_task(run_batch_parallel, (_list_inject_worker, items, out_dir))


    def start_recursive_extraction(self):
        """Initiates recursive extraction from a source directory."""
        src = self.rec_extract_source_var.get()
        out = self.rec_extract_output_var.get()

        # Input validation (basic checks, more robust checks handled in recursive_batch_extract)
        if not src: messagebox.showwarning("Input Missing","Please select the source directory containing ARC files."); return
        if not out: messagebox.showwarning("Output Missing","Please select the output base directory."); return

        # Call the recursive batch function directly (it handles finding files)
        self._run_task(recursive_batch_extract, (src, out))


    def start_folder_injection(self):
        """Initiates folder injection (rebuild) using original and edited directories."""
        orig = self.folder_inject_orig_arc_var.get()
        edit = self.folder_inject_edited_dir_var.get()
        out = self.folder_inject_output_var.get()

        # Input validation (basic checks, more robust checks handled in folder_batch_inject)
        if not orig: messagebox.showwarning("Input Missing","Please select the directory containing original ARC files."); return
        if not edit: messagebox.showwarning("Input Missing","Please select the directory containing edited content folders."); return
        if not out: messagebox.showwarning("Output Missing","Please select the output directory for rebuilt ARCs."); return

        # Call the folder batch function directly (it handles scanning folders)
        self._run_task(folder_batch_inject, (orig, edit, out))


    # --- Queue/Status/Progress Handling ---
    def update_progress(self,v):
        """Updates the GUI progress bar (called from worker threads via queue)."""
        # Ensure value is within bounds 0-100 before setting
        self.queue.put({'type':'progress','value':max(0.0, min(100.0, float(v)))}) # Ensure float

    def queue_status(self,m,l=STATUS_INFO):
        """Adds a status message to the queue (called from worker threads)."""
        self.queue.put({'type':'status','msg':m,'level':l})

    def check_queue(self):
        """Processes messages from the queue and updates the GUI."""
        try:
            while True:
                # Get message without blocking
                m=self.queue.get_nowait()
                t=m.get('type')
                if t=='progress':
                    # Set the progress bar value
                    self.progress_var.set(m.get('value',0.0))
                elif t=='status':
                    # Add status message to the text widget
                    self.add_status_message(m.get('msg',''),m.get('level',STATUS_INFO))
                # else: ignore unknown message types

        except queue.Empty:
            # No messages currently in the queue
            pass
        except Exception as e:
            # Catch unexpected errors during queue processing in the main thread
            print(f"Critical error processing queue: {e}", file=sys.stderr)
            print(f"Trace: {traceback.format_exc()}", file=sys.stderr)
            # Attempt to add a message to the status window if possible
            try: self.add_status_message(f"Critical GUI queue error: {e}", STATUS_ERROR)
            except Exception: pass # Give up if status update itself fails

        finally:
            # Schedule the next check
            self.root.after(100,self.check_queue) # Check queue every 100ms

    def add_status_message(self,m,l=STATUS_INFO):
        """Appends a message to the status text widget with formatting (called from main thread)."""
        try:
            self.status_text.configure(state='normal') # Enable editing
            # Add a timestamp for clarity in logs
            timestamp = datetime.now().strftime("[%H:%M:%S]")
            self.status_text.insert(tk.END,f"{timestamp} {m}\n",l) # Insert text with tag (level)
            self.status_text.configure(state='disabled') # Disable editing
            self.status_text.see(tk.END) # Scroll to the end
        except Exception as e:
            # Fallback print if GUI update fails
            print(f"Error updating status GUI: {e}", file=sys.stderr)
            print(f"Status message: {m}", file=sys.stderr)
            # Traceback is already logged by the worker or higher level error handlers


# --- MAIN EXECUTION ---
if __name__ == "__main__":
    # Check for pycryptodome dependency before starting GUI
    try: from Crypto.Cipher import Blowfish
    except ImportError:
        messagebox.showerror("Dependency Missing","Required library 'pycryptodome' not found.\nPlease install it using:\npip install pycryptodome")
        sys.exit(1) # Exit immediately if dependency is not met

    # Optional: Add basic CLI argument parsing for headless mode or specifying defaults? (Out of scope for now)

    # Load the extension map from the specified file
    extension_map_file_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), EXTENSION_MAP_FILE)
    load_extension_map(extension_map_file_path)
    if not EXTENSION_MAP: # If map failed to load or is empty
         messagebox.showwarning("Extension Map", f"Could not load or parse '{EXTENSION_MAP_FILE}'.\nFile extensions will be derived from hashes only.")


    root = tk.Tk()
    app = ArcToolApp(root)
    root.mainloop()