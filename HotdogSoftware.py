#!/usr/bin/python
# HotdogSoftware ARC Tool by Handburger (Target Version 17 - v1.6)
# Reverted ARC logic for v17 compatibility (loses Switch v9 focus).
# Includes theme, font, error handling, CONCURRENT recursive extraction (optional structure retention), and tutorial.

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext, font as tkFont
import os
import threading
import queue
import time
import zlib
import binascii
import struct
import sys
import traceback # For detailed error logging
from enum import Enum, auto
import concurrent.futures # Added for concurrency
from pathlib import Path # For path manipulation

# --- Constants ---
TARGET_ARC_VERSION = 17 # Target version for export/parsing assumptions
# Supported versions list reflects the original script's intent now
SUPPORTED_VERSIONS = [7, 17, 19] # Versions the parser *might* handle okay
ARC_INDEX_FILENAME = "arc_index"
DEFAULT_FONT_FAMILY = "JetBrains Mono" # Primary desired font
FALLBACK_FONT_FAMILIES = ("Consolas", "Courier New", "monospace") # Alternatives
DEFAULT_FONT_SIZE = 10
# Max concurrent extraction workers (adjust based on system/IO limits)
MAX_EXTRACT_WORKERS = os.cpu_count() or 4

# --- Color Scheme ---
BG_COLOR = '#2b2b2b'
TEXT_COLOR = '#ffebcd' # Blanched Almond / Light Beige
WIDGET_BG = '#3c3f41' # Darker Gray for entry/list/text background
INPUT_TEXT_COLOR = '#f0f0f0' # Lighter text for input fields
BUTTON_BG = '#4c4c4c' # Medium Gray
BUTTON_FG = TEXT_COLOR
BUTTON_ACTIVE_BG = '#5c5c5c' # Slightly lighter gray for active/hover
BUTTON_PRESSED_BG = '#636363' # Highlight color for pressed
BUTTON_BORDER = '#1e1e1e' # Dark border for buttons
HEADER_BG = '#4a4a4a' # Notebook tab header bg (Inactive)
HEADER_TEXT = TEXT_COLOR
HEADER_ACTIVE_BG = WIDGET_BG # Notebook tab header bg (Active)
HEADER_ACTIVE_TEXT = '#ffffff' # White text for active tab
HIGHLIGHT_BG = '#52596b' # Selection background (e.g., Listbox) - Bluish Gray
HIGHLIGHT_TEXT = '#ffffff' # Selection foreground
STATUS_ERROR_FG = '#ff6b6b' # Light Red for errors in status
STATUS_WARN_FG = '#ffb366' # Orange for warnings in status
STATUS_SUCCESS_FG = '#86e3a0' # Light Green for success in status
STATUS_INFO_FG = TEXT_COLOR # Default info color for status
STATUS_DEBUG_FG = '#999999' # Muted debug

# --- Error Codes Enum ---
class ArcErrorCode(Enum):
    SUCCESS = 0
    FILE_NOT_FOUND = auto()
    INDEX_NOT_FOUND = auto()
    INDEX_INVALID_FORMAT = auto()
    INDEX_EMPTY = auto()
    DIRECTORY_NOT_FOUND = auto()
    INVALID_INPUT = auto()
    IO_ERROR_READ = auto()
    IO_ERROR_WRITE = auto()
    OS_ERROR = auto()
    ARC_PARSE_HEADER = auto()
    ARC_PARSE_ENTRY = auto()
    ARC_PARSE_BOUNDS = auto()
    ARC_INVALID_VERSION = auto()
    ARC_EXPORT_ERROR = auto()
    COMPRESSION_ERROR = auto() # zlib errors
    PERMISSION_ERROR = auto()
    UNICODE_ERROR = auto()
    OPERATION_CANCELLED = auto() # User cancelled via dialog (Not currently used, but available)
    UNKNOWN_ERROR = auto()

# --- START OF INLINED util.py CONTENT ---

LOGGING = 1 # Default logging level (0=off, 1=basic, 2=info)

def enable_log(level): global LOGGING; LOGGING = level
def log(msg):
    if LOGGING > 0: print(msg) # Console log
def log_info(msg):
    if LOGGING > 1: print(f"INFO: {msg}")
def log_warn(msg): print(f"WARNING: {msg}")
def log_saving(fn): log(f"Saving {fn}...")
def log_loading(fn): log(f"Loading {fn}...")

# Modified error function to raise specific exceptions where possible
def error(msg, code=ArcErrorCode.UNKNOWN_ERROR):
    print(f"ERROR [{code.name}]: {msg}") # Log to console
    # Raise a specific exception type based on code if helpful,
    # otherwise raise a generic RuntimeError containing the code and message.
    if code == ArcErrorCode.FILE_NOT_FOUND or code == ArcErrorCode.INDEX_NOT_FOUND:
        raise FileNotFoundError(f"[{code.name}] {msg}")
    elif code == ArcErrorCode.IO_ERROR_READ or code == ArcErrorCode.IO_ERROR_WRITE:
        raise IOError(f"[{code.name}] {msg}")
    elif code == ArcErrorCode.PERMISSION_ERROR:
        raise PermissionError(f"[{code.name}] {msg}")
    elif code == ArcErrorCode.OS_ERROR:
        raise OSError(f"[{code.name}] {msg}")
    else: # For ARC errors, index format, unknown, etc.
        raise RuntimeError(f"[{code.name}] {msg}")

def readFile(path):
    if not isinstance(path, (str, bytes, os.PathLike)):
        error(f"Invalid path type provided to readFile: {type(path)}", ArcErrorCode.INVALID_INPUT)
    # Check existence and type *before* opening
    if not os.path.exists(path):
        error(f"File not found: {path}", ArcErrorCode.FILE_NOT_FOUND)
    if not os.path.isfile(path):
        error(f"Path is not a file: {path}", ArcErrorCode.INVALID_INPUT)
    try:
        # Open with 'rb' for binary read
        with open(path, 'rb') as f:
            return bytearray(f.read())
    except IOError as e:
        error(f'Read error on {path}: {e}', ArcErrorCode.IO_ERROR_READ)
    except PermissionError as e:
        error(f'Permission denied reading {path}: {e}', ArcErrorCode.PERMISSION_ERROR)
    except Exception as e:
        error(f'Unexpected error reading {path}: {e}', ArcErrorCode.UNKNOWN_ERROR)

def writeFile(path, data):
    if not isinstance(path, (str, bytes, os.PathLike)):
        error(f"Invalid path type provided to writeFile: {type(path)}", ArcErrorCode.INVALID_INPUT)
    if not isinstance(data, (bytes, bytearray, memoryview)):
        error(f"Invalid data type provided to writeFile: {type(data)}", ArcErrorCode.INVALID_INPUT)
    try:
        # Ensure the directory exists *before* opening the file
        dir_path = os.path.dirname(path)
        if dir_path:
             # Check if dir_path exists and is a directory, raise error if it's a file
             if os.path.exists(dir_path) and not os.path.isdir(dir_path):
                  error(f'Cannot create directory, path exists but is not a directory: {dir_path}', ArcErrorCode.OS_ERROR)
             # Create directories if they don't exist
             os.makedirs(dir_path, exist_ok=True)

        # Open with 'wb' for binary write
        with open(path, 'wb') as f:
            f.write(data)
    except IOError as e:
        # Catch generic IO errors (disk full, etc.)
        error(f'Write error on {path}: {e}', ArcErrorCode.IO_ERROR_WRITE)
    except OSError as e:
        # Catch OS-level errors (invalid path chars, mkdir issues)
        error(f'OS error writing or creating directory for {path}: {e}', ArcErrorCode.OS_ERROR)
    except PermissionError as e:
        # Catch permission errors specifically
        error(f'Permission denied writing {path}: {e}', ArcErrorCode.PERMISSION_ERROR)
    except Exception as e:
        # Catch any other unexpected exceptions during write/mkdir
        error(f'Unexpected error writing {path}: {e}', ArcErrorCode.UNKNOWN_ERROR)

# struct based read/write functions - with basic bounds checking
def _check_bounds(buf, offset, length):
    buf_len = len(buf)
    # Ensure offset and length are non-negative and fit within buffer
    if offset < 0 or length < 0 or offset + length > buf_len:
        error(f"Read/write out of bounds: offset={offset}, length={length}, size={buf_len}", ArcErrorCode.ARC_PARSE_BOUNDS)

def read_block(buf, offset, length):
    _check_bounds(buf, offset, length)
    # Return immutable bytes, safer than returning slice of mutable bytearray
    return bytes(buf[offset:offset + length])
def read_byte(buf, offset):
    _check_bounds(buf, offset, 1)
    return buf[offset]
def read_word(buf, offset):
    _check_bounds(buf, offset, 2)
    try:
        # Read 2 bytes as unsigned short, little-endian
        return struct.unpack_from('<H', buf, offset=offset)[0]
    except struct.error as e:
        # Handle potential errors during unpacking (e.g., if buffer ends unexpectedly)
        error(f"Struct unpack error (word) at offset {offset}: {e}", ArcErrorCode.ARC_PARSE_ENTRY)
def read_dword(buf, offset):
    _check_bounds(buf, offset, 4)
    try:
        # Read 4 bytes as unsigned int, little-endian
        return struct.unpack_from('<I', buf, offset=offset)[0]
    except struct.error as e:
        error(f"Struct unpack error (dword) at offset {offset}: {e}", ArcErrorCode.ARC_PARSE_ENTRY)
def write_byte(buf, offset, value):
    _check_bounds(buf, offset, 1)
    # Ensure value is a valid byte (0-255)
    if not 0 <= value <= 255:
         error(f"Invalid byte value: {value}", ArcErrorCode.INVALID_INPUT)
    buf[offset] = value
def write_word(buf, offset, value):
    _check_bounds(buf, offset, 2)
    try:
        # Pack value as unsigned short, little-endian into the buffer
        struct.pack_into('<H', buf, offset, value)
    except struct.error as e:
        # Handle potential errors during packing (e.g., value out of range for short)
        error(f"Struct pack error (word) for value {value} at offset {offset}: {e}", ArcErrorCode.ARC_EXPORT_ERROR)
def write_dword(buf, offset, value):
    _check_bounds(buf, offset, 4)
    try:
        # Pack value as unsigned int, little-endian into the buffer
        struct.pack_into('<I', buf, offset, value)
    except struct.error as e:
        error(f"Struct pack error (dword) for value {value} at offset {offset}: {e}", ArcErrorCode.ARC_EXPORT_ERROR)

def write_block(buf, offset, value):
    # Ensure input `value` is bytes or bytearray
    if isinstance(value, str):
        try:
            # Use latin-1 for compatibility with original script's implicit handling?
            # UTF-8 might be safer if paths contain non-ASCII, but needs testing.
            value = value.encode('latin-1', errors='replace')
        except UnicodeError as e:
            error(f"Encoding error for block at offset {offset}: {e}", ArcErrorCode.UNICODE_ERROR)
    elif not isinstance(value, (bytes, bytearray)):
         error(f"Invalid type for write_block: {type(value)}", ArcErrorCode.INVALID_INPUT)

    write_len = len(value)
    # Check if the write fits within the *target buffer's* current allocated size
    if offset < 0 or offset + write_len > len(buf):
         # This error indicates the target buffer (e.g., file_entries_buf) wasn't pre-allocated correctly
         error(f"Write block out of bounds: offset={offset}, length={write_len}, target_size={len(buf)}", ArcErrorCode.ARC_PARSE_BOUNDS)

    # Write the bytes into the buffer slice
    buf[offset:offset + write_len] = value

# --- END OF INLINED util.py CONTENT ---


# --- START OF REVERTED/MODIFIED arc.py CONTENT (Targeting v17) ---

# Extension map
ext = {
 "73850d05": ".arc",
    "39c52040": ".lcm",
    "0026e7ff": ".ccl",
    "535d969f": ".ctc",
    "51fc779f": ".sbc",
    "4e397417": ".ean",
    "6d5ae854": ".efl",
    "3aabba02": ".emc",
    "0a0e48d4": ".emd",
    "3d8bbbac": ".etd",
    "60869a71": ".evt",
    "11c35522": ".gr2",
    "628dfb41": ".gr2s",
    "0437bcf2": ".grw",
    "25fd693f": ".ipl",
    "52776ab1": ".ips",
    "15302ef4": ".lyt",
    "708e0028": ".lanl",
    "3516c3d2": ".lfd",
    "62440501": ".lmd",
    "3756ee15": ".ptex",
    "682b1925": ".lfx",
    "14b5c8e6": ".sbk",
    "7bea3086": ".cfl",
    "2618de3f": ".srq",
    "4a4b677c": ".rev_ctr",
    "67195a2e": ".mca",
    "3a6a5a4d": ".stq",
    "68cd2933": ".ses",
    "6e171a6e": ".mss",
    "2749c8a8": ".mrl",
    "148b6f89": ".mef",
    "58a15856": ".mod",
    "76820d81": ".lmt",
    "31f693d6": ".moflex",
    "1bbfd18e": ".mib",
    "4c0db839": ".sdl",
    "07437cce": ".ase",
    "0ecd7df4": ".scs",
    "0315e81f": ".sds",
    "2a8800ee": ".sai",
    "6b41a2f9": ".scd",
    "065375d5": ".sis",
    "19278d07": ".skst",
    "70c56d5e": ".skmt",
    "2c59eea9": ".sksg",
    "241f5deb": ".tex",
    "5f36b659": ".way",
    "7b54b600": ".atd",
    "3e2a4d8e": ".amlt",
    "000692f5": ".amskl",
    "21f33e01": ".amslt",
    "790203b0": ".angryprm",
    "7f2e2ee0": ".areaacttbl",
    "1ee1ed64": ".areacmnlink",
    "56d892d0": ".areaeatdat",
    "6ff78212": ".areainfo",
    "4bf84f6f": ".arealinkdat",
    "0947f3c8": ".areapatrol",
    "15e98d21": ".areaseldat",
    "327e327e": ".abd",
    "737234f5": ".acd",
    "3c51e03c": ".ard",
    "017ca1b2": ".ased",
    "7896b60a": ".asd",
    "1ac7b52d": ".bdd",
    "368e9519": ".bgsd",
    "5f6a387f": ".cms",
    "0a7db17e": ".deco",
    "1f149aec": ".mdd",
    "32ca92f8": ".esl",
    "5adc692c": ".emsizetbl",
    "1800eb37": ".emyure",
    "59d9c3da": ".dtb",
    "1bbc291e": ".dtp",
    "48e8ac29": ".dtt",
    "630ed7bb": ".nan",
    "583f70b0": ".rdb",
    "252bd342": ".ebcd",
    "4541367c": ".pts",
    "30991f46": ".frl",
    "2543b93e": ".ses",
    "10ebe843": ".mss",
    "3e0e02fc": ".fsh",
    "496f8f22": ".fup",
    "06c7327b": ".fmt",
    "156a8085": ".fmi",
    "61c203a4": ".fms",
    "22948394": ".gui",
    "2d462600": ".gfd",
    "07f768af": ".gii",
    "242bb29a": ".gmd",
    "33a84e14": ".hgi",
    "70bb64ba": ".hde",
    "4e2ef008": ".hdp",
    "4eb68cee": ".hds",
    "5653c1b0": ".hts",
    "294a5e8d": ".hta",
    "141c243a": ".insectabirity",
    "38534e81": ".isa",
    "11de9ef6": ".isd",
    "6e765e35": ".insectessenceskill",
    "48b16938": ".isl",
    "76a1d9a2": ".isp",
    "7c4883a8": ".itm",
    "5b8e6bf3": ".itp",
    "63f62424": ".ipt",
    "6e972f76": ".kad",
    "02dd067f": ".kod",
    "41e33404": ".lan",
    "197e4d7a": ".maptime",
    "7cd0e77e": ".mpm",
    "6d81cfdd": ".oar",
    "4b51e836": ".olvl",
    "0c0fab06": ".otml",
    "5ea6aa68": ".oxpb",
    "7039f76f": ".oxpv",
    "0f86c052": ".oskl",
    "7c5e6060": ".osa",
    "7a395cb7": ".sab",
    "2f1c6767": ".saou",
    "3c285cc6": ".otd",
    "5b0dd78a": ".otp",
    "681fa774": ".owp",
    "5139901d": ".plbasecmd",
    "4b4c2bd3": ".plcmdtbllist",
    "233a2c4d": ".plgmktype",
    "18a9225c": ".pma",
    "66c89ed2": ".plpartsdisp",
    "540d49c1": ".plweplist",
    "450a16e3": ".pntpos",
    "6fcc7ad4": ".pec",
    "5a525c16": ".pel",
    "254309c9": ".psl",
    "20ed9750": ".pep",
    "61cf79af": ".qsg",
    "6ec8125c": ".raps",
    "1e329efc": ".rlt",
    "5b3c302d": ".rem",
    "58072136": ".sfsa",
    "2553701d": ".sem",
    "0c6d4399": ".sid",
    "4aa69872": ".shell",
    "1eb12c38": ".sep",
    "39c8dc68": ".skd",
    "4c3942e3": ".skt",
    "15d782fb": ".sbkr",
    "2b40ae8f": ".equr",
    "1bcc4966": ".srqr",
    "232e228c": ".revr_ctr",
    "79c47b59": ".mca",
    "167dbbff": ".stqr",
    "710688e2": ".squs",
    "54539aee": ".sup",
    "74a22486": ".spval",
    "751aff22": ".tams",
    "4199032b": ".w00d",
    "437d7704": ".w00d",
    "29482ccb": ".w00m",
    "56e21768": ".w01d",
    "2cbf1c3a": ".w01d",
    "65e22c55": ".w01m",
    "6f6f2bad": ".w02d",
    "4788a739": ".w02d",
    "6b6d2bb6": ".w02m",
    "78143fee": ".w03d",
    "284acc07": ".w03d",
    "27c72b28": ".w03m",
    "1c755227": ".w04d",
    "4a96d77e": ".w04d",
    "2d022231": ".w04m",
    "32837aa1": ".w06d",
    "4e630743": ".w06d",
    "6f27254c": ".w06m",
    "25f86ee2": ".w07d",
    "21a16c7d": ".w07d",
    "238d25d2": ".w07m",
    "7a41a133": ".w08d",
    "50aa37f0": ".w08d",
    "7aad377e": ".w08m",
    "6d3ab570": ".w09d",
    "3f685cce": ".w09d",
    "360737e0": ".w09m",
    "2e5b6815": ".w10d",
    "02f3a8c4": ".w10d",
    "3e333888": ".w10m",
    "39207c56": ".w11d",
    "6d31c3fa": ".w11d",
    "72993816": ".w11m",
    "00ad4093": ".w12d",
    "060678f9": ".w12d",
    "7c163ff5": ".w12m",
    "17d654d0": ".w13d",
    "69c413c7": ".w13d",
    "30bc3f6b": ".w13m",
    "73b73919": ".w14d",
    "0b1808be": ".w14d",
    "3a793672": ".w14m",
    "5d2e4199": ".ane",
    "3b04f5a1": ".ape",
    "058ace42": ".acn",
    "7522dd13": ".arcd",
    "63f2d70d": ".apd",
    "0ab54515": ".bui",
    "542767ec": ".cskd",
    "01a1196b": ".doi",
    "2229d051": ".dcd",
    "5ca6db93": ".sla00",
    "440d0451": ".slw00",
    "330a34c7": ".slw01",
    "2a03657d": ".slw02",
    "5d0455eb": ".slw03",
    "4360c048": ".slw04",
    "2d6ea164": ".slw06",
    "5a6991f2": ".slw07",
    "4ad68c63": ".slw08",
    "3dd1bcf5": ".slw09",
    "5d163510": ".slw10",
    "2a110586": ".slw11",
    "3318543c": ".slw12",
    "441f64aa": ".slw13",
    "5a7bf109": ".slw14",
    "6a1670f0": ".fld",
    "24080fff": ".fht",
    "5812ac77": ".gpd",
    "77d70343": ".atr",
    "58bc1c29": ".ext",
    "160329f8": ".rem",
    "3443f314": ".iaf",
    "300db281": ".igf",
    "3fa5ad6a": ".ict",
    "233a9f13": ".kcg",
    "0c7468ea": ".kcm",
    "6d964d19": ".kca",
    "0c6c4dbf": ".kcr",
    "24f0a487": ".kcs",
    "237e6120": ".kc1",
    "3a77309a": ".kc2",
    "4d70000c": ".kc3",
    "66d7cd8a": ".mai",
    "7f416ce5": ".mcn",
    "117d7cd0": ".mcm",
    "19c994c4": ".mex",
    "7d025838": ".mla",
    "2a68813f": ".mlc",
    "4a91ddb9": ".mle",
    "64844d84": ".mri",
    "36c909fd": ".mre",
    "626bc4d6": ".mrs",
    "041925d7": ".mvp",
    "6d5aaa39": ".npcBd",
    "43062a33": ".npcId",
    "699ac631": ".npcMdl",
    "0430075d": ".nis",
    "164f60ff": ".nld",
    "3488527b": ".npcMd",
    "1a273e8b": ".npcSd",
    "1a3e9cba": ".ntd",
    "0620fd81": ".oec",
    "2bcfb893": ".otil",
    "7b572569": ".olsk",
    "79ff11c9": ".olos",
    "6f56b442": ".opl",
    "69b525df": ".otpt",
    "10cedaea": ".pcl",
    "25a60bc4": ".ssjje",
    "332cf371": ".ssjjp",
    "619d23df": ".slt",
    "5e5b44c8": ".sls",
    "458de878": ".sad",
    "25334dde": ".trdl",
    "29751294": ".tril",
    "55fca0f5": ".tlil",
    "2754877d": ".trll",
    "19f2ab31": ".tpil",
    "056ccdbc": ".tucyl",
    "2fc0c6c5": ".tuto",
    "62220853": ".vfp",
    "42354dc6": ".wcd",
    "15fce6c6": ".wpd",
}

# ARC Class - REVERTED to logic closer to original Dasding script for v7/17/19
class ARC:
    magic = [b'ARC\x00']
    # Supported versions reflect the original script's apparent scope
    supported_versions = SUPPORTED_VERSIONS # [7, 17, 19]

    def __init__(self, arc_data=None):
        self.magic = ARC.magic[0]
        self.version = TARGET_ARC_VERSION # Default version for creation
        self.file_list = []
        self.file_count = 0
        self.padding_dword = 0 # Placeholder, might not be used consistently
        if arc_data:
            try:
                self.import_arc(arc_data)
            except Exception as e:
                # Catch import errors and re-raise with context if needed
                error(f"Failed to import ARC data: {e}", ArcErrorCode.ARC_PARSE_HEADER)

    def default_meta(self):
        self.magic = ARC.magic[0]
        self.version = TARGET_ARC_VERSION
        self.file_list = []
        self.file_count = 0
        self.padding_dword = 0

    def import_arc(self, arc_data):
        if not isinstance(arc_data, (bytes, bytearray)):
            error("ARC data must be bytes or bytearray", ArcErrorCode.INVALID_INPUT)
        self.parse_header(arc_data)
        # Header parsing checks version support
        self.parse_file_list(arc_data)
        self.parse_files(arc_data)

    def parse_header(self, arc_data):
        # Need at least 8 bytes (v7) or 12 bytes (v17/19)
        min_header_size = 8
        if len(arc_data) < min_header_size:
             error(f"Invalid ARC file: Too small for header (need {min_header_size}, got {len(arc_data)}).", ArcErrorCode.ARC_PARSE_HEADER)

        self.magic = read_block(arc_data, 0x00, 4)
        if self.magic not in ARC.magic:
             error(f"Invalid Magic Identifier: {self.magic!r}. Expected {ARC.magic[0]!r}.", ArcErrorCode.ARC_PARSE_HEADER)

        self.version = read_word(arc_data, 0x04)
        if self.version not in self.supported_versions:
             # Log warning but allow proceeding, as original script did? Or error?
             log_warn(f'Unsupported ARC Version: {self.version}. Expected one of {self.supported_versions}. Proceeding with caution.')
             # Optionally error out:
             # error(f'Unsupported ARC Version: {self.version}. Tool supports {self.supported_versions}.', ArcErrorCode.ARC_INVALID_VERSION)

        self.file_count = read_word(arc_data, 0x06)

        # Check for padding dword based on version (original script's logic)
        # Requires 12 bytes for v17/19 header check
        if self.version == 19 or self.version == 17:
            if len(arc_data) < 12:
                 error(f"ARC V{self.version} expects 12+ byte header, got {len(arc_data)}", ArcErrorCode.ARC_PARSE_HEADER)
            self.padding_dword = read_dword(arc_data, 0x08) # Read it, might not be used later
        else: # Assume v7 or others don't have it
            self.padding_dword = 0

    def parse_file_list(self, arc_data):
        # Determine table offset based on version (original script's logic)
        if self.version == 19 or self.version == 17:
            file_table_offset = 0x0C
        elif self.version == 7:
            file_table_offset = 0x08
        else:
            # If version wasn't in supported list but we proceeded, use a default
            log_warn(f"Using default table offset (0x0C) for unsupported version {self.version}")
            file_table_offset = 0x0C # Default guess

        # Assume fixed 80-byte entry length (original script's assumption)
        file_table_length = 0x50
        # Calculate expected end based on file count and offset
        expected_table_end = file_table_offset + self.file_count * file_table_length

        if self.file_count < 0: # Should not happen if read correctly, but check anyway
             error(f"Invalid file count: {self.file_count}", ArcErrorCode.ARC_PARSE_HEADER)
        # Allow file_count == 0
        if self.file_count > 0 and expected_table_end > len(arc_data):
             error(f"File table exceeds ARC size (Count: {self.file_count}, Expected End: {expected_table_end:#x}, ARC Size: {len(arc_data):#x})", ArcErrorCode.ARC_PARSE_BOUNDS)

        file_list = []
        current_offset = file_table_offset
        for idx in range(self.file_count):
            entry_start_offset = current_offset
            f = {'index': idx} # Add index for error reporting
            try:
                # Read standard 80-byte entry structure
                raw_filename = read_block(arc_data, entry_start_offset + 0, 64)
                # Decode filename safely - try utf-8 first as it's more common
                try:
                    f['file'] = raw_filename.split(b'\x00', 1)[0].decode('utf-8', errors='replace')
                except UnicodeDecodeError:
                    # Fallback to latin-1 if utf-8 fails
                    f['file'] = raw_filename.split(b'\x00', 1)[0].decode('latin-1', errors='replace')

                ext_bytes = read_block(arc_data, entry_start_offset + 64, 4)
                f['raw_ext'] = binascii.hexlify(ext_bytes) # Keep hex string representation
                f['extension_bytes'] = ext_bytes # Keep raw bytes

                f['size'] = read_dword(arc_data, entry_start_offset + 68) # Compressed Size

                # Read "uncompressed size" field which includes flags in high byte
                raw_unc_size_field = read_dword(arc_data, entry_start_offset + 72)
                f['raw_unc_size_field'] = raw_unc_size_field # Store the raw value for potential reference

                f['offset'] = read_dword(arc_data, entry_start_offset + 76) # Data Offset

                # Extract flag and size using original script's method (Likely for LE v7/17/19)
                # High byte (bits 24-31) as flag
                f['comp_flag'] = (raw_unc_size_field >> 24) & 0xFF
                # Lower 3 bytes (bits 0-23) as size
                f['unc_size'] = raw_unc_size_field & 0x00FFFFFF

                # Basic sanity checks on values
                if f['size'] < 0 or f['unc_size'] < 0 or f['offset'] < 0:
                     log_warn(f"Entry {idx} ('{f['file']}') has negative size/offset values. May indicate corruption.")
                # Check if offset points somewhere reasonable (e.g., after the file table)
                # This check might be too strict if ARCs can have data before the table end. Relaxing it.
                # if f['offset'] > 0 and f['offset'] < expected_table_end:
                #      log_warn(f"Entry {idx} ('{f['file']}') offset ({f['offset']:#x}) points inside file table. Likely corruption.")
                # Check if offset+size exceeds ARC bounds (more robust check done in parse_files)

                # Process extension
                if ext_bytes in ext:
                    f['extension'] = ext[ext_bytes]
                else:
                    # Use the hex representation as the extension if unknown
                    unknown_ext_str = f['raw_ext'].decode('ascii', errors='ignore') # Use ignore for safety
                    log_info(f'Unknown File Signature: {unknown_ext_str} for entry {idx}')
                    f['extension'] = '.' + unknown_ext_str

                # Combine filename and extension, normalize path separators
                f['file'] = f['file'].replace("\\", '/') + f['extension']

                file_list.append(f)
                current_offset += file_table_length

            except RuntimeError as e: # Catch errors from read_* functions (e.g., bounds, struct errors)
                error(f"Failed parsing entry {idx} at offset {entry_start_offset:#x}: {e}", ArcErrorCode.ARC_PARSE_ENTRY)
            except Exception as e:
                # Catch any other unexpected errors during entry processing
                error(f"Unexpected error parsing entry {idx} at offset {entry_start_offset:#x}: {e}", ArcErrorCode.ARC_PARSE_ENTRY)

        self.file_list = file_list

    def parse_files(self, arc_data):
        arc_len = len(arc_data)
        for f in self.file_list:
             # Check offset and size validity again before reading data block
             # Ensure offset and size are non-negative and don't exceed ARC boundaries
            if f['offset'] < 0 or f['size'] < 0 or f['offset'] + f['size'] > arc_len:
                 log_warn(f"File entry {f['index']} ('{f['file']}') data region invalid (Offset: {f['offset']:#x}, Size: {f['size']:#x}, ARC Size: {arc_len:#x}). Skipping data read.")
                 f['data'] = b'' # Assign empty data
                 f['error'] = ArcErrorCode.ARC_PARSE_BOUNDS.name # Mark error
                 continue

            # Read compressed data block safely using read_block (which includes bounds check)
            try:
                 compressed_data = read_block(arc_data, f['offset'], f['size'])
            except RuntimeError as e: # Catch bounds errors from read_block itself
                 log_warn(f"Error reading data block for file entry {f['index']} ('{f['file']}'): {e}. Skipping.")
                 f['data'] = b''
                 f['error'] = ArcErrorCode.ARC_PARSE_BOUNDS.name
                 continue

            if f['size'] == 0:
                 f['data'] = b'' # Empty file
            # Original script *always* tried decompressing if size > 0. Let's stick to that for v17 logic.
            elif f['size'] > 0:
                try:
                    # Use memoryview for potentially better performance with zlib
                    f['data'] = zlib.decompress(memoryview(compressed_data))
                    # Verify decompressed size matches the extracted lower 3 bytes
                    if len(f['data']) != f['unc_size']:
                         log_warn(f"Decompressed size mismatch for entry {f['index']} ('{f['file']}'). Expected {f['unc_size']} (from low 3 bytes), got {len(f['data'])}. Flag was {f.get('comp_flag', '?'):#x}.")
                         # Don't mark as fatal error, but store warning
                         f['warning'] = "Size mismatch after decompression"
                except zlib.error as e:
                     # If decompression fails, store the original (compressed) data
                     log_warn(f"Zlib decompression failed for entry {f['index']} ('{f['file']}'): {e}. Storing compressed data instead.")
                     f['data'] = compressed_data # Keep original data
                     f['error'] = ArcErrorCode.COMPRESSION_ERROR.name
                     f['error_details'] = str(e) # Store specific zlib error message
                except Exception as e:
                     # Catch other potential errors during decompression
                     log_warn(f"Unexpected decompression error for entry {f['index']} ('{f['file']}'): {e}")
                     f['data'] = compressed_data
                     f['error'] = ArcErrorCode.UNKNOWN_ERROR.name
                     f['error_details'] = str(e)
            else: # size is negative (already logged warning during file list parsing)
                f['data'] = b''
                if not f.get('error'): # Avoid overwriting previous errors
                    f['error'] = ArcErrorCode.INVALID_INPUT.name
                    f['error_details'] = "Invalid (negative) compressed size"

    def export_arc(self):
        # Use the instance's version, which defaults to TARGET_ARC_VERSION
        # Determine header size and table offset based on the instance's version
        if self.version not in self.supported_versions:
             log_warn(f"Exporting with potentially unsupported version {self.version}. Using layout based on V{TARGET_ARC_VERSION}.")
             # Force layout based on TARGET_ARC_VERSION for consistency
             if TARGET_ARC_VERSION == 19 or TARGET_ARC_VERSION == 17:
                 header_size = 0x0C; file_table_offset = 0x0C
             elif TARGET_ARC_VERSION == 7:
                 header_size = 0x08; file_table_offset = 0x08
             else: # Should not happen if TARGET_ARC_VERSION is valid
                 error(f"Cannot determine export layout for target version {TARGET_ARC_VERSION}", ArcErrorCode.ARC_INVALID_VERSION)
             current_export_version = TARGET_ARC_VERSION # Use target for layout decisions
        else:
             current_export_version = self.version # Use the ARC's actual version

        # Determine layout based on the version being exported
        if current_export_version == 19 or current_export_version == 17:
            header_size = 0x0C; file_table_offset = 0x0C
        elif current_export_version == 7:
            header_size = 0x08; file_table_offset = 0x08
        else: # Should not be reachable if check above is strict, but handle defensively
            error(f"Cannot determine export layout for version {current_export_version}", ArcErrorCode.ARC_INVALID_VERSION)

        # Assume fixed 80-byte entry length for these versions
        file_table_length = 0x50

        # Prepare header buffer
        header_buf = bytearray(header_size)
        write_block(header_buf, 0x0, self.magic)
        write_word(header_buf, 0x04, current_export_version) # Write the determined version
        write_word(header_buf, 0x06, len(self.file_list))
        if header_size == 0x0C:
             # Write the stored padding dword (read from original or default 0)
             write_dword(header_buf, 0x08, self.padding_dword)

        # Prepare file table entries buffer and list for compressed data
        file_entries_buf = bytearray(file_table_length * len(self.file_list))
        compressed_data_list = []

        log_info(f"Compressing {len(self.file_list)} files for ARC v{current_export_version}...")
        for idx, f in enumerate(self.file_list):
            entry_offset_in_table = idx * file_table_length
            filename_part, extension_part = os.path.splitext(f['file'])
            # Encode filename (try utf-8, fallback latin-1), ensure backslashes for ARC internal path
            try:
                try: filename_bytes = filename_part.replace('/', '\\').encode('utf-8', errors='strict')
                except UnicodeEncodeError: filename_bytes = filename_part.replace('/', '\\').encode('latin-1', errors='replace')
            except Exception as e:
                 error(f"Filename encoding error for entry {idx} ('{filename_part}'): {e}", ArcErrorCode.UNICODE_ERROR)

            # Create zero-padded buffer for filename and write into it safely
            filename_padded = bytearray(64)
            write_block(filename_padded, 0, filename_bytes) # write_block handles length limit

            # Get extension bytes from hex string stored in file info
            try:
                 extension_bytes = binascii.unhexlify(f['raw_ext'])
            except (binascii.Error, TypeError) as e:
                 log_warn(f"Invalid raw_ext '{f.get('raw_ext', 'N/A')}' for entry {idx} ('{f['file']}'). Using default '.dat' hash. Error: {e}")
                 extension_bytes = b'\x00\x10\x17\x40' # Placeholder for .dat? Needs verification

            # Get raw data, ensuring it's bytes
            raw_data = f.get('data', b'')
            if not isinstance(raw_data, (bytes, bytearray)):
                log_warn(f"Invalid data type for entry {idx} ('{f['file']}'): {type(raw_data)}. Using empty data.")
                raw_data = b''
            unc_data_len = len(raw_data)

            # Compress data (always compress for simplicity, as per original script?)
            try:
                 cdata = zlib.compress(raw_data) # Use default zlib compression
                 compressed_data_list.append(cdata)
                 cdata_len = len(cdata)
            except zlib.error as e:
                 error(f"Zlib compression failed for entry {idx} ('{f['file']}'): {e}", ArcErrorCode.COMPRESSION_ERROR)
            except Exception as e:
                 error(f"Unexpected compression error for entry {idx} ('{f['file']}'): {e}", ArcErrorCode.UNKNOWN_ERROR)

            # Determine uncompressed size field value (with flag) using original script's logic
            # Default flag 0x20, special flag 0xA0 for .mod based on file extension
            comp_flag = 0xA0 if extension_part.lower() == '.mod' else 0x20
            # Combine flag (high byte) and size (lower 3 bytes)
            unc_size_field = (comp_flag << 24) | (unc_data_len & 0x00FFFFFF)

            # Write entry structure (v7/17/19 layout) into the pre-allocated buffer
            try:
                write_block(file_entries_buf, entry_offset_in_table + 0, filename_padded) # Filename (64 bytes)
                write_block(file_entries_buf, entry_offset_in_table + 64, extension_bytes) # Extension hash (4 bytes)
                write_dword(file_entries_buf, entry_offset_in_table + 68, cdata_len) # Comp size (4 bytes)
                write_dword(file_entries_buf, entry_offset_in_table + 72, unc_size_field) # Unc size + flag (4 bytes)
                write_dword(file_entries_buf, entry_offset_in_table + 76, 0) # Offset placeholder (4 bytes)
            except RuntimeError as e: # Catch bounds errors etc. from write_* helpers
                 error(f"Failed writing entry {idx} to internal buffer: {e}", ArcErrorCode.ARC_EXPORT_ERROR)
            except Exception as e:
                 error(f"Unexpected error writing entry {idx} to internal buffer: {e}", ArcErrorCode.ARC_EXPORT_ERROR)

        # Calculate final data offset - NO SPECIAL ALIGNMENT in this reverted logic
        file_table_end_offset = len(header_buf) + len(file_entries_buf)
        # Data starts immediately after the file table
        final_file_data_start_offset = file_table_end_offset
        log_info(f"Data start offset (no alignment assumed for v{current_export_version}): {final_file_data_start_offset:#x}")

        # Combine all parts: header, file table, then all compressed data blocks
        final_arc_buf = bytearray()
        try:
             final_arc_buf.extend(header_buf)
             final_arc_buf.extend(file_entries_buf)
        except MemoryError:
             error("Memory error while constructing ARC header/table.", ArcErrorCode.UNKNOWN_ERROR)
        except Exception as e:
             error(f"Unexpected error constructing ARC header/table: {e}", ArcErrorCode.ARC_EXPORT_ERROR)

        # Append compressed data and update offsets in the file table part of the final buffer
        current_data_write_offset = final_file_data_start_offset
        for idx, cdata in enumerate(compressed_data_list):
            entry_offset_in_table = idx * file_table_length
            # Calculate absolute position of the offset field (offset 76 within entry) within final_arc_buf
            # Offset = header size + position within table + field offset within entry
            # Need to use file_table_offset which depends on header size
            offset_field_location = file_table_offset + entry_offset_in_table + 76

            try:
                # Write the actual data offset into the file table section of final_arc_buf
                write_dword(final_arc_buf, offset_field_location, current_data_write_offset)
                # Append the compressed data to the end of final_arc_buf
                final_arc_buf.extend(cdata)
                # Update the offset for the next file's data block
                current_data_write_offset += len(cdata)
            except MemoryError:
                 error(f"Memory error while writing file data for entry {idx}.", ArcErrorCode.UNKNOWN_ERROR)
            except RuntimeError as e: # Catch bounds errors from write_dword
                 error(f"Failed writing offset for entry {idx}: {e}", ArcErrorCode.ARC_EXPORT_ERROR)
            except Exception as e:
                 error(f"Unexpected error writing data/offset for entry {idx}: {e}", ArcErrorCode.ARC_EXPORT_ERROR)

        log_info(f"Total ARC size: {len(final_arc_buf)}")
        return final_arc_buf

    def add_file(self, filename, data, ext_hex_str):
        # Basic validation on input
        if not isinstance(filename, str) or not filename:
             log_warn(f"Invalid or empty filename provided to add_file. Skipping.")
             return False # Indicate failure to add
        if not isinstance(data, (bytes, bytearray)):
             log_warn(f"Invalid data type for '{filename}'. Using empty data.")
             data = b''
        # Validate hex string format and length
        if not isinstance(ext_hex_str, str) or len(ext_hex_str) != 8:
            log_warn(f"Invalid extension hex string format/length '{ext_hex_str}' for '{filename}'. Using default.")
            ext_hex_str = "00101740" # Placeholder for .dat? Needs verification
        else:
            try:
                # Attempt to validate if it's a hex string
                _ = bytes.fromhex(ext_hex_str)
            except (ValueError, TypeError):
                log_warn(f"Invalid extension hex string content '{ext_hex_str}' for '{filename}'. Using default.")
                ext_hex_str = "00101740" # Placeholder for .dat?

        f = {}
        f['file'] = filename # Store relative path as provided
        f['data'] = data
        f['raw_ext'] = ext_hex_str # Store validated/defaulted hex string
        # No 'unk1' field in this reverted structure
        self.file_list.append(f)
        return True # Indicate success

    def __str__(self):
        # Indicate the target version it's currently configured for
        return f"ARC Target v{self.version}, Files: {len(self.file_list)}"

# --- END OF REVERTED/MODIFIED arc.py CONTENT ---


# --- GUI Application Class ---
class ArcToolApp(tk.Tk):
    def __init__(self):
        super().__init__()
        # Update title to reflect target version
        self.title(f"HotdogSoftware ARC Tool by Handburger (Target v{TARGET_ARC_VERSION})")
        self.protocol("WM_DELETE_WINDOW", self.on_closing) # Handle closing while processing

        # --- Font Setup ---
        self.app_font = self.find_font()
        log_info(f"Using font: {self.app_font.actual()}")

        # --- Style Setup ---
        self.configure_style()
        self.config(bg=BG_COLOR) # Set root window background

        # --- GUI State Variables ---
        self.arc_files_to_extract = [] # Stores full paths currently displayed in listbox
        self.extract_output_dir = tk.StringVar()
        self.create_input_dir = tk.StringVar()
        self.create_output_file = tk.StringVar()
        self.retain_structure_var = tk.BooleanVar(value=False) # Toggle for structure retention
        self.scan_root_dir = None # Store the root dir used for recursive scan to calculate relative paths
        self.status_queue = queue.Queue()
        self.is_processing = False # Flag to track if worker is running
        self.worker_thread = None # Holds reference to the ThreadPoolExecutor future if needed
        self.after_id = None # Store ID for the .after() scheduled task

        # UI Setup
        self.controls_to_disable = [] # Keep track of widgets to disable
        self.create_widgets()
        self.check_status_queue() # Start the status queue checker

    def find_font(self):
        """Finds preferred font or falls back."""
        available_fonts = list(tkFont.families())
        font_family = DEFAULT_FONT_FAMILY
        if font_family not in available_fonts:
            log_warn(f"Font '{font_family}' not found.")
            for fallback in FALLBACK_FONT_FAMILIES:
                if fallback in available_fonts:
                    font_family = fallback
                    log_warn(f"Using fallback font: '{font_family}'")
                    break
            else:
                # If no fallbacks found, use Tkinter's default
                font_family = tkFont.nametofont("TkDefaultFont").actual()["family"]
                log_warn(f"No preferred or fallback fonts found. Using default: '{font_family}'")
        # Return the font object
        return tkFont.Font(family=font_family, size=DEFAULT_FONT_SIZE)

    def configure_style(self):
        """Configures the ttk style for the application."""
        style = ttk.Style(self)
        # Use a theme that allows more customization, like 'clam' or 'alt'
        # If 'clam' isn't available on all systems, might need a fallback theme logic
        try:
            style.theme_use('clam')
        except tk.TclError:
            log_warn("Style theme 'clam' not available, using default.")
            # Use default theme if clam fails

        # --- General Widget Styling (Applied to all ttk widgets) ---
        style.configure('.',
                        background=BG_COLOR,
                        foreground=TEXT_COLOR,
                        font=self.app_font,
                        relief=tk.FLAT, # Flat look for most widgets
                        borderwidth=0) # No border for most widgets

        # --- Frame ---
        style.configure('TFrame', background=BG_COLOR)

        # --- Label ---
        style.configure('TLabel', background=BG_COLOR, foreground=TEXT_COLOR)
        style.configure('Status.TLabel', background=BG_COLOR) # Specific style for status label if needed
        style.configure('Header.TLabel', background=HEADER_BG, foreground=HEADER_TEXT, padding=5) # Example for headers

        # --- Button ---
        style.configure('TButton',
                        background=BUTTON_BG,
                        foreground=BUTTON_FG,
                        bordercolor=BUTTON_BORDER, # Border color
                        relief=tk.RAISED, # Give buttons some dimension
                        borderwidth=1, # Button border width
                        padding=(10, 5), # Horizontal and vertical padding
                        font=self.app_font) # Ensure button font is set
        # Map states (hover, pressed, disabled)
        style.map('TButton',
                  background=[('pressed', '!disabled', BUTTON_PRESSED_BG), # Background when pressed
                              ('active', '!disabled', BUTTON_ACTIVE_BG), # Background when hovered
                              ('disabled', WIDGET_BG)], # Background when disabled
                  foreground=[('disabled', HIGHLIGHT_BG)], # Text color when disabled
                  relief=[('pressed', tk.SUNKEN)]) # Relief style when pressed

        # --- Entry (for displaying paths) ---
        style.configure('TEntry',
                        fieldbackground=WIDGET_BG, # Background of the text area
                        foreground=INPUT_TEXT_COLOR, # Text color
                        insertcolor=INPUT_TEXT_COLOR, # Cursor color
                        borderwidth=1,
                        relief=tk.SUNKEN) # Sunken look for entry fields
        # Map disabled state
        style.map('TEntry',
                  fieldbackground=[('disabled', BG_COLOR)], # Different background when disabled
                   foreground=[('disabled', HIGHLIGHT_BG)]) # Different text color when disabled

        # --- Notebook (Tabs) ---
        style.configure('TNotebook', background=BG_COLOR, borderwidth=0)
        style.configure('TNotebook.Tab',
                        background=HEADER_BG, # Background for inactive tabs
                        foreground=HEADER_TEXT, # Text color for inactive tabs
                        padding=(10, 5),
                        font=self.app_font, # Ensure tab font is set
                        borderwidth=0) # No border around tab itself
        # Map selected state for tabs
        style.map('TNotebook.Tab',
                  background=[('selected', HEADER_ACTIVE_BG)], # Background for the selected tab
                  foreground=[('selected', HEADER_ACTIVE_TEXT)], # Text color for the selected tab
                  expand=[('selected', (1, 1, 1, 0))]) # Optional slight padding expansion when selected

        # --- Scrollbar ---
        # Style for Vertical scrollbars
        style.configure('Vertical.TScrollbar',
                        background=WIDGET_BG, # Background of the scrollbar handle
                        troughcolor=BG_COLOR, # Background of the trough (channel)
                        borderwidth=0,
                        arrowcolor=TEXT_COLOR) # Color of the arrow buttons
        # Style for Horizontal scrollbars
        style.configure('Horizontal.TScrollbar',
                        background=WIDGET_BG, troughcolor=BG_COLOR, borderwidth=0, arrowcolor=TEXT_COLOR)
        # Map active state (when hovered/dragged)
        style.map('Vertical.TScrollbar', background=[('active', BUTTON_ACTIVE_BG)])
        style.map('Horizontal.TScrollbar', background=[('active', BUTTON_ACTIVE_BG)])

        # --- LabelFrame ---
        style.configure('TLabelframe', background=BG_COLOR, borderwidth=1, relief=tk.GROOVE)
        # Style the label part of the LabelFrame
        style.configure('TLabelframe.Label', background=BG_COLOR, foreground=TEXT_COLOR, font=self.app_font)

        # Style for Checkbutton
        style.configure('TCheckbutton',
                        background=BG_COLOR, # Background matches window
                        foreground=TEXT_COLOR, # Text color
                        font=self.app_font, # Use app font
                        indicatorcolor=WIDGET_BG) # Color of the check box itself (unselected)
        style.map('TCheckbutton',
                  indicatorcolor=[('selected', HIGHLIGHT_BG), # Color when selected
                                  ('active', BUTTON_ACTIVE_BG)], # Color when hovered
                  foreground=[('disabled', HIGHLIGHT_BG)]) # Text color when disabled

    def create_widgets(self):
        # Main container frame with padding
        main_frame = ttk.Frame(self, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)

        # Notebook for tabs
        notebook = ttk.Notebook(main_frame)
        extract_tab = ttk.Frame(notebook, padding="10")
        create_tab = ttk.Frame(notebook, padding="10")
        # Update tab titles to reflect the target version
        notebook.add(extract_tab, text='Extract ARC(s)')
        notebook.add(create_tab, text=f'Create ARC (v{TARGET_ARC_VERSION})')
        notebook.pack(expand=True, fill='both', pady=(0, 10))

        # Setup content for each tab
        self.setup_extract_tab(extract_tab)
        self.setup_create_tab(create_tab)

        # Status area label
        status_label = ttk.Label(main_frame, text="Status / Log:", style='Status.TLabel')
        status_label.pack(fill=tk.X, padx=0, pady=(5, 0))

        # Frame for the status text widget
        status_frame = ttk.Frame(main_frame)
        status_frame.pack(fill=tk.BOTH, expand=True, padx=0, pady=(0, 0))

        # ScrolledText widget for status/log output
        self.status_text = scrolledtext.ScrolledText(status_frame, wrap=tk.WORD, height=10,
                                                     bg=WIDGET_BG, fg=TEXT_COLOR, # Background/Foreground
                                                     font=self.app_font, # Use defined font
                                                     insertbackground=TEXT_COLOR, # Cursor color
                                                     selectbackground=HIGHLIGHT_BG, # Selection colors
                                                     selectforeground=HIGHLIGHT_TEXT,
                                                     borderwidth=0, relief=tk.FLAT, # Flat look
                                                     state=tk.DISABLED) # Start read-only
        self.status_text.pack(fill=tk.BOTH, expand=True)

        # Configure color tags for status messages
        self.status_text.tag_configure("ERROR", foreground=STATUS_ERROR_FG)
        self.status_text.tag_configure("WARN", foreground=STATUS_WARN_FG)
        self.status_text.tag_configure("SUCCESS", foreground=STATUS_SUCCESS_FG)
        self.status_text.tag_configure("INFO", foreground=STATUS_INFO_FG) # Default info color
        self.status_text.tag_configure("DEBUG", foreground=STATUS_DEBUG_FG) # Muted debug color

        # --- Menu Bar ---
        menubar = tk.Menu(self, bg=BG_COLOR, fg=TEXT_COLOR, relief=tk.FLAT, bd=0,
                          activebackground=BUTTON_ACTIVE_BG, activeforeground=TEXT_COLOR)

        # File Menu
        filemenu = tk.Menu(menubar, tearoff=0, bg=WIDGET_BG, fg=TEXT_COLOR, relief=tk.FLAT, bd=0,
                           activebackground=HIGHLIGHT_BG, activeforeground=HIGHLIGHT_TEXT)
        filemenu.add_command(label="Exit", command=self.on_closing, font=self.app_font)
        menubar.add_cascade(label="File", menu=filemenu, font=self.app_font)

        # Help Menu
        helpmenu = tk.Menu(menubar, tearoff=0, bg=WIDGET_BG, fg=TEXT_COLOR, relief=tk.FLAT, bd=0,
                           activebackground=HIGHLIGHT_BG, activeforeground=HIGHLIGHT_TEXT)
        helpmenu.add_command(label="Tutorial / Help", command=self.show_tutorial, font=self.app_font)
        helpmenu.add_separator()
        helpmenu.add_command(label="About", command=self.show_about, font=self.app_font)
        menubar.add_cascade(label="Help", menu=helpmenu, font=self.app_font)

        # Apply the menu bar to the main window
        self.config(menu=menubar)

    def setup_extract_tab(self, parent):
        # --- Frame for Input Selection ---
        selection_frame = ttk.LabelFrame(parent, text="Select Input")
        selection_frame.grid(row=0, column=0, columnspan=3, padx=5, pady=5, sticky="ew")

        # Button to select individual files
        btn_select_arcs = ttk.Button(selection_frame, text="Select ARC File(s)...", command=self.select_arc_files)
        btn_select_arcs.grid(row=0, column=0, padx=5, pady=5, sticky="ew")
        self.controls_to_disable.append(btn_select_arcs)

        # Button for recursive directory scan
        btn_select_dir_recursive = ttk.Button(selection_frame, text="Select Directory (Recursive)...", command=self.select_recursive_dir)
        btn_select_dir_recursive.grid(row=0, column=1, padx=5, pady=5, sticky="ew")
        self.controls_to_disable.append(btn_select_dir_recursive)

        # Configure columns in selection frame to expand equally
        selection_frame.columnconfigure(0, weight=1)
        selection_frame.columnconfigure(1, weight=1)

        # --- Frame for File List Display ---
        listbox_frame = ttk.LabelFrame(parent, text="Files to Extract")
        listbox_frame.grid(row=1, column=0, columnspan=3, padx=5, pady=5, sticky="nsew")

        # Listbox (using tk.Listbox for direct color control)
        self.listbox_arcs = tk.Listbox(listbox_frame, height=7, selectmode=tk.EXTENDED,
                                        bg=WIDGET_BG, fg=INPUT_TEXT_COLOR, # Colors
                                        selectbackground=HIGHLIGHT_BG, # Selection colors
                                        selectforeground=HIGHLIGHT_TEXT,
                                        font=self.app_font, # Font
                                        borderwidth=1, relief=tk.SUNKEN, # Border/Relief
                                        exportselection=False) # Keep selection on focus loss
        self.listbox_arcs.grid(row=0, column=0, padx=5, pady=5, sticky="nsew")

        # Scrollbars for Listbox (using themed ttk.Scrollbar)
        scrollbar_arcs_y = ttk.Scrollbar(listbox_frame, orient=tk.VERTICAL, command=self.listbox_arcs.yview)
        scrollbar_arcs_y.grid(row=0, column=1, padx=0, pady=5, sticky="ns") # Place right of listbox
        scrollbar_arcs_x = ttk.Scrollbar(listbox_frame, orient=tk.HORIZONTAL, command=self.listbox_arcs.xview)
        scrollbar_arcs_x.grid(row=1, column=0, padx=5, pady=0, sticky="ew") # Place below listbox
        self.listbox_arcs.config(yscrollcommand=scrollbar_arcs_y.set, xscrollcommand=scrollbar_arcs_x.set)

        # Button to clear the list
        btn_clear_list = ttk.Button(listbox_frame, text="Clear List", command=self.clear_extract_list, width=10)
        btn_clear_list.grid(row=0, column=2, padx=(10, 5), pady=5, sticky="n") # Place next to scrollbar top
        self.controls_to_disable.append(btn_clear_list)

        # Configure listbox frame grid
        listbox_frame.columnconfigure(0, weight=1) # Listbox expands horizontally
        listbox_frame.rowconfigure(0, weight=1) # Listbox expands vertically

        # --- Frame for Output Selection & Options ---
        output_frame = ttk.LabelFrame(parent, text="Select Output & Options")
        output_frame.grid(row=2, column=0, columnspan=3, padx=5, pady=(10, 5), sticky="ew")

        # Button to select output directory
        btn_select_extract_dir = ttk.Button(output_frame, text="Select Output Directory...", command=self.select_extract_dir)
        btn_select_extract_dir.grid(row=0, column=0, padx=5, pady=5, sticky="ew")
        self.controls_to_disable.append(btn_select_extract_dir)

        # Entry to display selected output directory (read-only)
        entry_extract_dir = ttk.Entry(output_frame, textvariable=self.extract_output_dir, state='readonly')
        entry_extract_dir.grid(row=0, column=1, padx=5, pady=5, sticky="ew")
        output_frame.columnconfigure(1, weight=1) # Make entry expand

        # --- Retain Structure Toggle ---
        # Use themed Checkbutton
        self.retain_structure_check = ttk.Checkbutton(
            output_frame,
            text="Retain Source Directory Structure (Recursive Scan Only)",
            variable=self.retain_structure_var,
            state=tk.DISABLED) # Start disabled
        self.retain_structure_check.grid(row=1, column=0, columnspan=2, padx=5, pady=(0, 5), sticky="w")
        self.controls_to_disable.append(self.retain_structure_check) # Add to disable list

        # --- Extract Button ---
        btn_extract = ttk.Button(parent, text="Extract Listed/Selected ARC(s)", command=self.start_extraction)
        btn_extract.grid(row=3, column=0, columnspan=3, padx=5, pady=(10, 5)) # Add padding below
        self.controls_to_disable.append(btn_extract)

        # Configure parent grid (Extract Tab)
        parent.rowconfigure(1, weight=1) # Allow listbox area to expand vertically

    def setup_create_tab(self, parent):
        # Frame for selecting input directory
        input_dir_frame = ttk.LabelFrame(parent, text="Select Input Directory (containing extracted files + arc_index)")
        input_dir_frame.grid(row=0, column=0, columnspan=3, padx=5, pady=(5, 10), sticky="ew")

        btn_select_create_dir = ttk.Button(input_dir_frame, text="Select Directory...", command=self.select_create_dir)
        btn_select_create_dir.grid(row=0, column=0, padx=5, pady=5, sticky="ew")
        self.controls_to_disable.append(btn_select_create_dir)
        entry_create_dir = ttk.Entry(input_dir_frame, textvariable=self.create_input_dir, state='readonly')
        entry_create_dir.grid(row=0, column=1, padx=5, pady=5, sticky="ew")
        input_dir_frame.columnconfigure(1, weight=1) # Make entry expand

        # Frame for selecting output file
        output_file_frame = ttk.LabelFrame(parent, text="Select Output ARC File")
        output_file_frame.grid(row=1, column=0, columnspan=3, padx=5, pady=5, sticky="ew")

        btn_select_create_file = ttk.Button(output_file_frame, text="Select File...", command=self.select_create_file)
        btn_select_create_file.grid(row=0, column=0, padx=5, pady=5, sticky="ew")
        self.controls_to_disable.append(btn_select_create_file)
        entry_create_file = ttk.Entry(output_file_frame, textvariable=self.create_output_file, state='readonly')
        entry_create_file.grid(row=0, column=1, padx=5, pady=5, sticky="ew")
        output_file_frame.columnconfigure(1, weight=1) # Make entry expand

        # Create Button
        btn_create = ttk.Button(parent, text=f"Create ARC (v{TARGET_ARC_VERSION})", command=self.start_creation)
        btn_create.grid(row=2, column=0, columnspan=3, padx=5, pady=(15, 5)) # Add more padding above
        self.controls_to_disable.append(btn_create)

        # Configure column weights for the main Create Tab grid
        parent.columnconfigure(0, weight=1)
        parent.columnconfigure(1, weight=1)
        parent.columnconfigure(2, weight=1) # Distribute space if needed


    # --- Callbacks ---
    def clear_extract_list(self):
        """Clears the listbox and the internal list of files to process."""
        if self.is_processing:
            self.log_status("Cannot clear list while processing.", level="warn")
            return
        self.listbox_arcs.delete(0, tk.END)
        self.arc_files_to_extract = [] # Clear the internal list as well
        self.scan_root_dir = None # Clear scan root dir reference
        # Disable and reset the retain structure checkbox
        if self.retain_structure_check.winfo_exists(): # Check if widget exists
            self.retain_structure_check.config(state=tk.DISABLED)
        self.retain_structure_var.set(False)
        self.log_status("Cleared extraction list.", level="info")

    def select_arc_files(self):
        """Allows user to select one or more ARC files to add to the list."""
        if self.is_processing: return
        # Remember last directory? (Optional enhancement)
        files = filedialog.askopenfilenames(
            title="Select ARC files",
            filetypes=[("ARC Archives", "*.arc"), ("All Files", "*.*")]
            # initialdir=self.last_browse_dir # Add if tracking last dir
            )
        if files:
            # self.last_browse_dir = os.path.dirname(files[0]) # Store directory
            new_files_added = 0
            # Get current list from listbox to check for duplicates
            current_list = set(self.listbox_arcs.get(0, tk.END))
            for f_path in files:
                # Validate: is it a string path, does it exist, is it a file, does it end with .arc?
                if isinstance(f_path, str) and os.path.isfile(f_path) and f_path.lower().endswith(".arc"):
                     if f_path not in current_list:
                          self.listbox_arcs.insert(tk.END, f_path)
                          current_list.add(f_path) # Add to set for checking
                          new_files_added += 1
                     else:
                          self.log_status(f"Skipped duplicate: {os.path.basename(f_path)}", level="debug")
                else:
                    self.log_status(f"Skipped invalid selection: {f_path}", level="warn", code=ArcErrorCode.INVALID_INPUT)

            # Update the internal list to match the listbox content *after* adding all
            self.arc_files_to_extract = self.listbox_arcs.get(0, tk.END)
            self.log_status(f"Added {new_files_added} valid ARC file(s) to list. Total in list: {len(self.arc_files_to_extract)}", level="info")

            # Disable retain structure toggle if files were added manually
            self.scan_root_dir = None
            if self.retain_structure_check.winfo_exists():
                self.retain_structure_check.config(state=tk.DISABLED)
            self.retain_structure_var.set(False)

    def select_recursive_dir(self):
        """Selects a directory and finds all .arc files within it recursively."""
        if self.is_processing: return
        directory = filedialog.askdirectory(
            title="Select Root Directory to Scan for ARC files"
            # initialdir=self.last_browse_dir # Optional
            )
        if not directory:
            return # User cancelled

        # self.last_browse_dir = directory # Store directory
        self.log_status(f"Scanning '{directory}' recursively for .arc files...", level="info")
        found_arcs = []
        scan_errors = 0
        # Use a separate thread for potentially long scans? For now, keep it simple for stability.
        try:
            for root, _, files in os.walk(directory, onerror=lambda err: self.log_status(f"OS Walk Error accessing '{err.filename}': {err.strerror}", level="error", code=ArcErrorCode.OS_ERROR)):
                for filename in files:
                    if filename.lower().endswith(".arc"):
                        try:
                             full_path = os.path.join(root, filename)
                             # Check if it's actually a file and readable (basic check)
                             if os.path.isfile(full_path) and os.access(full_path, os.R_OK):
                                 found_arcs.append(full_path)
                             elif not os.path.isfile(full_path):
                                 self.log_status(f"Skipping non-file item found during scan: {full_path}", level="debug")
                             else: # Not readable
                                  self.log_status(f"Skipping unreadable file during scan: {full_path}", level="warn", code=ArcErrorCode.PERMISSION_ERROR)
                                  scan_errors += 1
                        except OSError as e:
                             # Handles errors like path too long, etc.
                             self.log_status(f"Error accessing path during scan: {e}", level="warn", code=ArcErrorCode.OS_ERROR)
                             scan_errors += 1
                        except Exception as e:
                             # Catch any other unexpected errors during file check
                             self.log_status(f"Unexpected error during file check: {e}", level="warn", code=ArcErrorCode.UNKNOWN_ERROR)
                             scan_errors += 1
        except Exception as e:
            # Catch errors during the os.walk setup itself
            self.log_status(f"Error scanning directory '{directory}': {e}", level="error", code=ArcErrorCode.OS_ERROR)
            messagebox.showerror("Error", f"Failed to scan directory:\n{e}")
            return

        if not found_arcs:
            msg = f"No readable .arc files found in '{directory}'."
            if scan_errors > 0: msg += f" ({scan_errors} access/read errors occurred during scan)"
            self.log_status(msg, level="warn")
            messagebox.showinfo("Scan Complete", msg)
            # Still disable retain structure if nothing found
            self.scan_root_dir = None
            if self.retain_structure_check.winfo_exists(): self.retain_structure_check.config(state=tk.DISABLED)
            self.retain_structure_var.set(False)
            return

        # Add found files to the listbox, avoiding duplicates
        new_files_added = 0
        current_list = set(self.listbox_arcs.get(0, tk.END))
        for f_path in found_arcs:
            if f_path not in current_list:
                self.listbox_arcs.insert(tk.END, f_path)
                current_list.add(f_path)
                new_files_added += 1

        # Update the internal list to match listbox
        self.arc_files_to_extract = self.listbox_arcs.get(0, tk.END)

        # --- Enable Retain Structure Toggle ---
        self.scan_root_dir = directory # Store the scanned root
        if self.retain_structure_check.winfo_exists():
            self.retain_structure_check.config(state=tk.NORMAL) # Enable the checkbox
        self.log_status("Recursive scan complete. 'Retain Structure' option enabled.", level="info")
        # ---

        final_scan_msg = f"Found and added {new_files_added} new readable .arc files from '{directory}'. Total in list: {len(self.arc_files_to_extract)}"
        if scan_errors > 0: final_scan_msg += f" ({scan_errors} access/read errors occurred)"
        self.log_status(final_scan_msg, level="info")
        messagebox.showinfo("Scan Complete", final_scan_msg)


    def select_extract_dir(self):
        if self.is_processing: return
        directory = filedialog.askdirectory(title="Select Base Output Directory for Extraction")
        if directory:
            self.extract_output_dir.set(directory)
            self.log_status(f"Set extract output directory: {directory}", level="info")

    def select_create_dir(self):
        if self.is_processing: return
        directory = filedialog.askdirectory(title="Select Input Directory (containing extracted files + arc_index)")
        if directory:
            self.create_input_dir.set(directory)
            self.log_status(f"Set create input directory: {directory}", level="info")
            # Check for index file immediately after selection
            index_path = os.path.join(directory, ARC_INDEX_FILENAME)
            if not os.path.isfile(index_path):
                 self.log_status(f"'{ARC_INDEX_FILENAME}' not found or is not a file in the selected input directory.", level="warn", code=ArcErrorCode.INDEX_NOT_FOUND)
            elif not os.access(index_path, os.R_OK):
                 self.log_status(f"Found '{ARC_INDEX_FILENAME}' but cannot read it (check permissions).", level="warn", code=ArcErrorCode.PERMISSION_ERROR)
            else:
                 self.log_status(f"Found readable '{ARC_INDEX_FILENAME}'.", level="info")

    def select_create_file(self):
        if self.is_processing: return
        filename = filedialog.asksaveasfilename(
            title="Select Output ARC File",
            defaultextension=".arc",
            filetypes=[("ARC Archives", "*.arc"), ("All Files", "*.*")]
            )
        if filename:
            self.create_output_file.set(filename)
            self.log_status(f"Set create output file: {filename}", level="info")

    def show_about(self):
        messagebox.showinfo(
            f"About HotdogSoftware ARC Tool (Target v{TARGET_ARC_VERSION})",
            f"HotdogSoftware ARC Tool by Handburger\n\n"
            f"Extractor/injector for ARC files (Targeting v{TARGET_ARC_VERSION}).\n"
            f"Based on dasding's mhtools logic.\n\n"
            f"Version: 1.6 (Retain Structure Option + Concurrent Extract)"
        )

    def show_tutorial(self):
        """Displays a simple tutorial window."""
        tutorial_text = f"""
HotdogSoftware ARC Tool - Tutorial (Target v{TARGET_ARC_VERSION})

**Extracting ARC Files (Concurrent):**

1.  **Select Input:**
    *   "Select ARC File(s)...": Choose specific `.arc` files. Added files appear in the list. The "Retain Structure" option will be disabled.
    *   "Select Directory (Recursive)...": Scan a folder and its subfolders for `.arc` files. Found files are added to the list. The "Retain Structure" option becomes enabled.
    *   "Clear List": Removes all files from the list and disables "Retain Structure".
2.  **Files List:** Shows files queued for extraction. Select specific files to extract only those, or leave none selected to extract all listed files.
3.  **Select Output & Options:**
    *   "Select Output Directory...": Choose a *base folder* where extracted content will be saved.
    *   "Retain Source Directory Structure": (Only enabled after recursive scan) If checked, the original folder structure relative to the scanned directory will be recreated within the output base folder. If unchecked (or disabled), all extracted ARC folders (`*_extracted`) will be placed directly inside the output base folder.
4.  **Extract:** Click "Extract Listed/Selected ARC(s)".
    *   Multiple ARCs are processed concurrently for speed.
    *   Each ARC's content goes into its own subfolder (e.g., `my_arc_extracted`).
    *   The location of these subfolders depends on the "Retain Structure" toggle (if enabled).
    *   The essential `{ARC_INDEX_FILENAME}` is created in each subfolder. **Do not delete `{ARC_INDEX_FILENAME}` if rebuilding.**

**Creating ARC Files:**

1.  **Select Input:** Choose ONE extraction subfolder (e.g., `my_arc_extracted` or `OutputBase/Relative/Path/my_arc_extracted`) which contains the files AND the `{ARC_INDEX_FILENAME}`.
2.  **Select Output:** Choose the name and location for the new `.arc` file.
3.  **Create:** Click "Create ARC (v{TARGET_ARC_VERSION})". Rebuilds the ARC using **Version {TARGET_ARC_VERSION}** structure and rules.

**Important Notes:**

*   This version targets **ARC Version {TARGET_ARC_VERSION}**. Compatibility with other versions (like Switch v9) depends on structural similarity and is not guaranteed. The internal logic specifically follows the v7/17/19 structure assumptions.
*   The `{ARC_INDEX_FILENAME}` file is crucial for recreation.
*   Check the Status/Log for progress and errors. Concurrent extraction messages might appear interleaved.
"""
        try:
            # Create a Toplevel window
            win_tutorial = tk.Toplevel(self)
            win_tutorial.title("Tutorial / Help")
            win_tutorial.config(bg=BG_COLOR)
            win_tutorial.geometry("650x550") # Adjust size as needed
            win_tutorial.transient(self) # Keep on top of main window
            win_tutorial.grab_set() # Modal behavior

            # Add a ScrolledText widget to display the tutorial
            text_frame = ttk.Frame(win_tutorial, padding=10)
            text_frame.pack(expand=True, fill=tk.BOTH)

            tutorial_widget = scrolledtext.ScrolledText(text_frame, wrap=tk.WORD,
                                                        bg=WIDGET_BG, fg=TEXT_COLOR,
                                                        font=self.app_font, relief=tk.FLAT, bd=0,
                                                        padx=5, pady=5)
            tutorial_widget.insert(tk.INSERT, tutorial_text)
            tutorial_widget.config(state=tk.DISABLED) # Make read-only
            tutorial_widget.pack(expand=True, fill=tk.BOTH)

            # Add a close button
            close_button = ttk.Button(win_tutorial, text="Close", command=win_tutorial.destroy)
            close_button.pack(pady=10)

            # Center the tutorial window (optional)
            win_tutorial.update_idletasks()
            win_width = win_tutorial.winfo_width()
            win_height = win_tutorial.winfo_height()
            # Get geometry relative to the main window (safer than root coords)
            parent_x = self.winfo_x()
            parent_y = self.winfo_y()
            parent_width = self.winfo_width()
            parent_height = self.winfo_height()
            x = parent_x + (parent_width // 2) - (win_width // 2)
            y = parent_y + (parent_height // 2) - (win_height // 2)
            # Ensure window doesn't go off-screen
            screen_width = self.winfo_screenwidth()
            screen_height = self.winfo_screenheight()
            x = max(0, min(x, screen_width - win_width))
            y = max(0, min(y, screen_height - win_height))
            win_tutorial.geometry(f"+{x}+{y}")

        except Exception as e:
            messagebox.showerror("Error", f"Could not display tutorial:\n{e}")
            self.log_status(f"Failed to show tutorial window: {e}", level="error", code=ArcErrorCode.UNKNOWN_ERROR)


    # --- Control Disabling/Enabling ---
    def disable_controls(self):
        """Disables buttons/widgets during processing."""
        self.is_processing = True
        for widget in self.controls_to_disable:
            try:
                # Check if widget exists before trying to configure
                if widget.winfo_exists():
                    widget.config(state=tk.DISABLED)
            except tk.TclError:
                # Ignore errors if widget is destroyed during the process
                pass

    def enable_controls(self):
        """Enables buttons/widgets after processing."""
        self.is_processing = False
        for widget in self.controls_to_disable:
            try:
                if widget.winfo_exists():
                    # Re-enable retain structure only if scan root is still valid
                    if widget == self.retain_structure_check and self.scan_root_dir is None:
                        widget.config(state=tk.DISABLED)
                    else:
                        widget.config(state=tk.NORMAL)
            except tk.TclError:
                pass
        # Clean up worker thread reference (ThreadPoolExecutor manages its own threads)
        self.worker_thread = None # Not strictly necessary but good practice

    # --- Logging & Status Updates ---
    def log_status(self, message, level="info", code=None):
        """Adds a message to the status queue for thread-safe GUI update."""
        if self.status_queue is None: return # Avoid error during shutdown
        timestamp = time.strftime("%H:%M:%S")
        level_upper = level.upper()
        # Map level to tag for coloring
        tag = "INFO" # Default tag
        if level_upper == "ERROR": tag = "ERROR"
        elif level_upper == "WARN": tag = "WARN"
        elif level_upper == "SUCCESS": tag = "SUCCESS"
        elif level_upper == "DEBUG": tag = "DEBUG"

        code_str = f" [{code.name}]" if code else ""
        formatted_message = f"[{timestamp}] [{level_upper}]{code_str} {message}\n"
        log_tags = (tag,) # Use the mapped tag
        try:
            # Put the message and tags tuple into the queue
            self.status_queue.put((formatted_message, log_tags))
        except Exception as e:
            # Avoid crashing if queue fails (e.g., during shutdown)
            print(f"Error putting message in status queue: {e}")

    def update_status_text(self, message, tags):
        """Updates the status text widget in the GUI thread."""
        # Check if the widget still exists before trying to update
        if self.status_text is None or not hasattr(self.status_text, 'winfo_exists') or not self.status_text.winfo_exists():
            return
        try:
             self.status_text.config(state=tk.NORMAL)
             self.status_text.insert(tk.END, message, tags) # Apply tags here
             self.status_text.see(tk.END) # Scroll to the end
             self.status_text.config(state=tk.DISABLED)
        except tk.TclError:
             # Ignore errors if widget is destroyed during update
             pass

    def check_status_queue(self):
        """Periodically checks the queue and updates the GUI."""
        if self.status_queue is None: return # Stop checking on shutdown
        try:
            # Process all available messages in the queue currently
            while True:
                message, tags = self.status_queue.get_nowait()
                self.update_status_text(message, tags)
        except queue.Empty:
            # Queue is empty, do nothing
            pass
        except Exception as e:
             # Log other unexpected errors during queue processing
             print(f"Error processing status queue: {e}")
        # Reschedule the check using after_id to prevent duplicates if already scheduled
        if hasattr(self, 'after_id') and self.after_id:
             try: self.after_cancel(self.after_id)
             except tk.TclError: pass # Ignore if already cancelled/invalid
        if self.status_queue is not None: # Only reschedule if not shutting down
            self.after_id = self.after(100, self.check_status_queue) # Check every 100ms


    # --- Thread Management and Closing ---
    def on_closing(self):
        """Handles window close requests."""
        if self.is_processing:
            if messagebox.askokcancel("Quit", "A process is running. Quit anyway?\n(The process will continue in the background until finished or error.)"):
                # NOTE: This doesn't gracefully stop the thread pool workers.
                # They will continue until they complete or error out.
                self.log_status("Forcibly closing application window during operation.", level="warn")
                # Stop checking the queue and destroy the window
                if hasattr(self, 'after_id') and self.after_id:
                    try: self.after_cancel(self.after_id)
                    except tk.TclError: pass
                self.status_queue = None # Signal queue checker to stop
                self.destroy()
            # else: user cancelled quit, do nothing
        else:
             # Cleanly stop queue checker and destroy window
             if hasattr(self, 'after_id') and self.after_id:
                 try: self.after_cancel(self.after_id)
                 except tk.TclError: pass
             self.status_queue = None
             self.destroy()

    def _start_worker(self, target_func, args_tuple, operation_name):
        """Starts a worker thread (for non-pooled tasks like creation) or manages pooled tasks."""
        if self.is_processing:
            self.log_status(f"{operation_name} already in progress.", level="warn")
            messagebox.showwarning("Busy", f"{operation_name} is already running.")
            return False

        self.disable_controls()
        self.log_status(f"Starting {operation_name}...", level="info")

        # Use a single thread for creation, use thread pool logic for extraction
        # The ThreadPoolExecutor is now managed *within* _bulk_extract_worker
        # So, we always just start the target function in a single new thread here.
        extended_args = args_tuple + (self.enable_controls,) # Add callback
        try:
            self.worker_thread = threading.Thread(target=target_func, args=extended_args, daemon=True)
            self.worker_thread.start()
            return True
        except Exception as e:
             self.log_status(f"Failed to start worker thread for {operation_name}: {e}", level="error", code=ArcErrorCode.UNKNOWN_ERROR)
             self.enable_controls() # Re-enable controls if thread failed to start
             return False


    # --- Core Logic Execution (Threads) ---

    # --- CONCURRENT EXTRACTION ---
    def start_extraction(self):
        # Get validated list of files currently in the listbox
        all_listed_paths = self.listbox_arcs.get(0, tk.END)
        # Ensure paths are strings and exist as files at the moment of starting
        valid_listed_paths = [p for p in all_listed_paths if isinstance(p, str) and os.path.isfile(p)]

        if not valid_listed_paths:
            messagebox.showerror("Error", "No valid/existing ARC files listed for extraction.")
            self.log_status("Extraction failed: No valid input files in list.", level="error", code=ArcErrorCode.INVALID_INPUT)
            return

        # Determine which files to process based on selection
        selected_indices = self.listbox_arcs.curselection()
        if selected_indices:
            # Get selected paths from the *original* listbox content using indices
            # Ensure index is valid for the original list length and path is still valid
            arcs_to_process = [all_listed_paths[i] for i in selected_indices
                               if i < len(all_listed_paths) and isinstance(all_listed_paths[i], str) and os.path.isfile(all_listed_paths[i])]
            if not arcs_to_process:
                messagebox.showerror("Error", "Selected items are invalid or no longer exist.")
                self.log_status("Extraction failed: Invalid selection.", level="error", code=ArcErrorCode.INVALID_INPUT)
                return
            self.log_status(f"Processing {len(arcs_to_process)} selected ARC file(s)...", level="info")
        else:
            arcs_to_process = valid_listed_paths # Process all valid listed files if none selected
            self.log_status(f"Processing all {len(arcs_to_process)} listed ARC file(s)...", level="info")

        # Validate output directory
        output_base_dir = self.extract_output_dir.get()
        if not output_base_dir:
             messagebox.showerror("Error", "No output directory selected.")
             self.log_status("Extraction failed: No output directory.", level="error", code=ArcErrorCode.INVALID_INPUT)
             return
        if not os.path.isdir(output_base_dir):
             messagebox.showerror("Error", f"Output directory does not exist or is not a directory:\n{output_base_dir}")
             self.log_status(f"Extraction failed: Output directory invalid '{output_base_dir}'.", level="error", code=ArcErrorCode.DIRECTORY_NOT_FOUND)
             return

        # Check write permissions for output directory
        if not os.access(output_base_dir, os.W_OK | os.X_OK): # Need write and execute (list) perms
            messagebox.showerror("Error", f"Cannot write to output directory (check permissions):\n{output_base_dir}")
            self.log_status(f"Extraction failed: Cannot write to output dir '{output_base_dir}'.", level="error", code=ArcErrorCode.PERMISSION_ERROR)
            return

        # Get retain structure setting (only relevant if scan_root_dir is set from recursive scan)
        retain_structure = self.retain_structure_var.get() and self.scan_root_dir is not None

        # Start the bulk worker which uses the thread pool
        # Pass the necessary flags and directories
        self._start_worker(self._bulk_extract_worker,
                           (arcs_to_process, output_base_dir, retain_structure, self.scan_root_dir),
                           "Concurrent Extraction")

    def _process_single_arc(self, arc_filepath, specific_output_dir):
        """
        Processes a single ARC file into a *pre-determined* output directory.
        This function is designed to be called by the ThreadPoolExecutor.
        It handles exceptions internally and returns a status tuple.
        Returns: tuple (ArcErrorCode, files_written_count, files_with_errors_count)
        """
        arc_filename = os.path.basename(arc_filepath)
        arc_status = ArcErrorCode.SUCCESS # Status for this specific ARC task
        files_written = 0
        files_with_errors = 0
        # Use file path for more specific logging prefix if needed, basename is usually enough
        file_log_prefix = f"ARC '{arc_filename}'"

        try:
            # --- Pre-checks ---
            # File existence check (might have changed since initial scan)
            if not os.path.isfile(arc_filepath):
                raise FileNotFoundError(f"File disappeared before processing: {arc_filepath}")
            # Read permission check
            if not os.access(arc_filepath, os.R_OK):
                 raise PermissionError(f"Read permission denied: {arc_filepath}")

            # --- Output Directory ---
            # The specific_output_dir is now calculated and passed in.
            # Ensure it exists.
            # Use try-except for makedirs in case of race conditions or permission issues
            try:
                 os.makedirs(specific_output_dir, exist_ok=True)
            except OSError as e:
                 # Log specific OS error for directory creation failure
                 # Reraise as RuntimeError to be caught by the main try-except block
                 error(f"Failed to create output directory '{specific_output_dir}': {e}", ArcErrorCode.OS_ERROR)

            # --- ARC Processing ---
            self.log_status(f"{file_log_prefix}: Reading...", level="debug")
            # readFile handles FileNotFoundError, PermissionError, IOError internally by raising
            arc_data = readFile(arc_filepath)
            # ARC init handles ARC_PARSE_HEADER, ARC_INVALID_VERSION, etc. by raising
            arc = ARC(arc_data)

            # Version check (already done in ARC init, but double-check if needed)
            # if arc.version not in SUPPORTED_VERSIONS:
            #      self.log_status(f"{file_log_prefix}: Skipping - Version {arc.version} not in supported list {SUPPORTED_VERSIONS}.", level="warn", code=ArcErrorCode.ARC_INVALID_VERSION)
            #      return ArcErrorCode.ARC_INVALID_VERSION, 0, 0 # Return status

            # --- Index File ---
            arc_index_path = os.path.join(specific_output_dir, ARC_INDEX_FILENAME)
            self.log_status(f"{file_log_prefix}: Writing index '{ARC_INDEX_FILENAME}'", level="debug")
            # Use 'w' mode (overwrite), ensure UTF-8 encoding for file paths in index
            # Use try-except for file open operation
            try:
                with open(arc_index_path, 'w', encoding='utf-8') as index_file:
                    # --- File Extraction Loop ---
                    for f in arc.file_list:
                        entry_log_prefix = f"{file_log_prefix} Entry {f.get('index', '?')} ('{f.get('file','?')}')"
                        # Check if file had parsing/decompression errors stored previously
                        if f.get('error'):
                            error_code = ArcErrorCode[f.get('error', 'UNKNOWN_ERROR')] if f.get('error') in ArcErrorCode.__members__ else ArcErrorCode.UNKNOWN_ERROR
                            self.log_status(f"{entry_log_prefix}: Skipping write due to previous error: {f.get('error_details', f.get('error','Unknown'))}", level="warn", code=error_code)
                            files_with_errors += 1
                            # Update ARC status if this is the first error for this ARC
                            if arc_status == ArcErrorCode.SUCCESS: arc_status = error_code
                            continue

                        # Validate and prepare internal path
                        internal_path = f.get('file', '').replace('\\', '/') # Ensure forward slashes
                        if internal_path.startswith('/'): internal_path = internal_path[1:] # Remove leading slash
                        if not internal_path: # Handle potentially empty path after cleaning?
                             self.log_status(f"{entry_log_prefix}: Skipping file with empty internal path.", level="warn")
                             files_with_errors += 1; arc_status = ArcErrorCode.INVALID_INPUT if arc_status == ArcErrorCode.SUCCESS else arc_status; continue

                        # Construct output path safely using OS separator
                        relative_path_os = internal_path.replace('/', os.path.sep)
                        try:
                            # Prevent path traversal attempts using basic check
                            if ".." in relative_path_os.split(os.path.sep): raise ValueError("Path traversal detected ('..')")
                            full_output_path = os.path.join(specific_output_dir, relative_path_os)
                            # Optional: Add check for path length limitations?
                        except ValueError as e:
                            self.log_status(f"{entry_log_prefix}: Skipping invalid relative path '{internal_path}': {e}", level="error", code=ArcErrorCode.INVALID_INPUT)
                            files_with_errors += 1; arc_status = ArcErrorCode.INVALID_INPUT if arc_status == ArcErrorCode.SUCCESS else arc_status; continue
                        except Exception as e_path: # Catch other potential path errors
                            self.log_status(f"{entry_log_prefix}: Error constructing output path for '{internal_path}': {e_path}", level="error", code=ArcErrorCode.OS_ERROR)
                            files_with_errors += 1; arc_status = ArcErrorCode.OS_ERROR if arc_status == ArcErrorCode.SUCCESS else arc_status; continue

                        # Write file data and index entry
                        try:
                            file_data = f.get('data', b'') # Get data, default to empty
                            if not isinstance(file_data, (bytes, bytearray)): file_data = b'' # Ensure bytes
                            writeFile(full_output_path, file_data) # Can raise IO/Permission/OS errors
                            files_written += 1
                            # Write to index file
                            raw_ext_str = f.get('raw_ext', b'').decode('ascii', 'ignore') # Safe decode
                            index_file.write(f"{internal_path}\t{raw_ext_str}\n")
                        except Exception as e_write: # Catch writeFile errors
                             # Determine error code from exception type
                             error_code = ArcErrorCode.IO_ERROR_WRITE
                             if isinstance(e_write, PermissionError): error_code = ArcErrorCode.PERMISSION_ERROR
                             elif isinstance(e_write, OSError): error_code = ArcErrorCode.OS_ERROR
                             elif isinstance(e_write, RuntimeError) and "[ArcErrorCode.INVALID_INPUT]" in str(e_write): error_code = ArcErrorCode.INVALID_INPUT # From writeFile type check
                             self.log_status(f"{entry_log_prefix}: Write failed for '{internal_path}' -> '{os.path.basename(full_output_path)}': {e_write}", level="error", code=error_code)
                             files_with_errors += 1
                             if arc_status == ArcErrorCode.SUCCESS: arc_status = error_code
                             # Decide whether to continue extracting other files from this ARC or stop
                             # continue # Default: continue processing other files in this ARC
            except IOError as e_idx: # Error opening/writing index file
                 error(f"Failed to write index file '{arc_index_path}': {e_idx}", ArcErrorCode.IO_ERROR_WRITE)
            except PermissionError as e_idx:
                 error(f"Permission denied writing index file '{arc_index_path}': {e_idx}", ArcErrorCode.PERMISSION_ERROR)


        # --- Catch errors during ARC parsing or outer operations ---
        except (FileNotFoundError, PermissionError, IOError, OSError, RuntimeError) as e_op:
             code = ArcErrorCode.UNKNOWN_ERROR # Default
             # Try to map known exception types to codes
             if isinstance(e_op, FileNotFoundError): code = ArcErrorCode.FILE_NOT_FOUND
             elif isinstance(e_op, PermissionError): code = ArcErrorCode.PERMISSION_ERROR
             elif isinstance(e_op, IOError): code = ArcErrorCode.IO_ERROR_READ if "Read" in str(e_op) else ArcErrorCode.IO_ERROR_WRITE
             elif isinstance(e_op, OSError): code = ArcErrorCode.OS_ERROR
             elif isinstance(e_op, RuntimeError): # Check if it's one of our custom RuntimeErrors
                  for c in ArcErrorCode:
                       if f"[{c.name}]" in str(e_op): code = c; break
             arc_status = code
             # Log error, but let the main worker handle overall status reporting
             self.log_status(f"{file_log_prefix}: Processing failed - {e_op}", level="error", code=arc_status)
        except Exception as e_generic: # Catch all other unexpected errors
             arc_status = ArcErrorCode.UNKNOWN_ERROR
             self.log_status(f"{file_log_prefix}: Unexpected processing error: {e_generic}", level="error", code=arc_status)
             # Log traceback for debugging unexpected issues
             self.log_status(traceback.format_exc(), level="debug")

        # Return status code, number written, number errors for aggregation by the caller
        return arc_status, files_written, files_with_errors

    def _bulk_extract_worker(self, arc_filepaths, output_base_dir, retain_structure, scan_root_dir, callback_on_finish):
        """Worker thread using ThreadPoolExecutor. Calculates target paths and manages pool."""
        total_to_process = len(arc_filepaths)
        success_count = 0 # Count ARCs processed without fatal errors (partial OK)
        processed_count = 0
        start_time = time.time()
        final_status = ArcErrorCode.SUCCESS # Overall status, starts optimistic

        self.log_status(f"Starting concurrent extraction for {total_to_process} ARC(s) using up to {MAX_EXTRACT_WORKERS} workers.", level="info")
        if retain_structure and scan_root_dir:
            self.log_status(f"Retaining source structure relative to: {scan_root_dir}", level="info")
        elif retain_structure:
            # This case should ideally be prevented by disabling the checkbox, but handle defensively
            self.log_status("Retain structure checked but no scan root dir provided. Structure will NOT be retained.", level="warn")
            retain_structure = False # Force off

        # Use ThreadPoolExecutor for managing concurrent tasks
        with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_EXTRACT_WORKERS) as executor:
            future_to_arc_info = {} # Map future to tuple (filepath, target_output_dir)
            submission_errors = 0

            # Submit tasks, calculating target directory for each first
            for arc_filepath in arc_filepaths:
                try:
                    arc_filename = os.path.basename(arc_filepath)
                    # Generate safe folder name for extracted contents
                    safe_arc_name = "".join(c if c.isalnum() or c in (' ', '.', '_', '-') else '_' for c in os.path.splitext(arc_filename)[0])
                    extracted_folder_name = safe_arc_name + "_extracted" # Suffix indicates content

                    # Determine the final specific output directory
                    if retain_structure and scan_root_dir:
                        # Calculate relative path from scan root using pathlib
                        try:
                            arc_path_obj = Path(arc_filepath)
                            scan_root_obj = Path(scan_root_dir)
                            # Get the parent directory relative to the scan root
                            relative_arc_dir = arc_path_obj.parent.relative_to(scan_root_obj)
                            # Construct final output path preserving structure
                            specific_output_dir_path = Path(output_base_dir) / relative_arc_dir / extracted_folder_name
                        except ValueError:
                            # Handle case where arc_filepath is not under scan_root_dir
                            self.log_status(f"ARC '{arc_filename}' is not under scan root '{scan_root_dir}'. Placing directly in output base.", level="warn")
                            specific_output_dir_path = Path(output_base_dir) / extracted_folder_name
                        except Exception as e_path:
                             self.log_status(f"Error calculating relative path for '{arc_filename}': {e_path}. Placing in output base.", level="warn", code=ArcErrorCode.OS_ERROR)
                             specific_output_dir_path = Path(output_base_dir) / extracted_folder_name
                    else:
                        # Default: place directly in output base directory
                        specific_output_dir_path = Path(output_base_dir) / extracted_folder_name

                    # Convert path object back to string for the worker function
                    specific_output_dir_str = str(specific_output_dir_path)

                    # Submit the task to the pool
                    future = executor.submit(self._process_single_arc, arc_filepath, specific_output_dir_str)
                    future_to_arc_info[future] = (arc_filepath, specific_output_dir_str) # Store info

                except Exception as submit_err:
                     # Error before even submitting the task (e.g., path calculation error)
                     submission_errors += 1
                     arc_filename_err = os.path.basename(arc_filepath or "Unknown ARC")
                     self.log_status(f"Error submitting task for {arc_filename_err}: {submit_err}", level="error", code=ArcErrorCode.UNKNOWN_ERROR)
                     if final_status == ArcErrorCode.SUCCESS: final_status = ArcErrorCode.UNKNOWN_ERROR

            if submission_errors > 0:
                 self.log_status(f"{submission_errors} tasks failed to submit.", level="warn")

            # Process results as they complete
            all_results = []
            for future in concurrent.futures.as_completed(future_to_arc_info):
                arc_filepath, target_dir = future_to_arc_info[future]
                arc_filename_res = os.path.basename(arc_filepath or "Unknown ARC") # For logging
                processed_count += 1
                try:
                    # Get the result tuple from the completed future
                    # Result is (arc_status, files_written, files_with_errors)
                    result = future.result()
                    all_results.append(result)
                    arc_status, files_written, files_with_errors = result

                    # Update overall final status: if any task failed or had non-success warnings,
                    # the overall status reflects the *first* non-SUCCESS code encountered.
                    if arc_status != ArcErrorCode.SUCCESS:
                        if final_status == ArcErrorCode.SUCCESS:
                            final_status = arc_status # Record the first error/warning status

                    # Count as overall success if the ARC was processed without fatal errors
                    # Define fatal based on status AND whether *any* files were written
                    is_fatal_arc_error = arc_status not in [ArcErrorCode.SUCCESS] and files_written == 0
                    if not is_fatal_arc_error:
                        # Count success if files were written OR if it was empty/processed ok without error
                        if files_written > 0 or (files_with_errors == 0 and arc_status == ArcErrorCode.SUCCESS):
                            success_count += 1

                except Exception as exc:
                    # This catches unexpected errors *from the future itself* (e.g., task raised unhandled exception)
                    self.log_status(f"Critical error processing result for {arc_filename_res}: {exc}", level="error", code=ArcErrorCode.UNKNOWN_ERROR)
                    self.log_status(traceback.format_exc(), level="debug") # Log full traceback
                    if final_status == ArcErrorCode.SUCCESS:
                        final_status = ArcErrorCode.UNKNOWN_ERROR # Mark overall failure
                    all_results.append((ArcErrorCode.UNKNOWN_ERROR, 0, 1)) # Record failure result

        # --- Final Summary Logging ---
        end_time = time.time(); duration = end_time - start_time
        level = "info"; status_tag = "SUCCESS"

        # Determine final level and status message based on results
        tasks_attempted = len(future_to_arc_info) + submission_errors # Total planned vs submitted
        if final_status != ArcErrorCode.SUCCESS:
            level = "error" if success_count == 0 else "warn" # Error only if zero ARCs succeeded at all
            status_tag = "ERROR" if level == "error" else "WARN"
        elif success_count < tasks_attempted: # Some tasks might have failed submission or processing
            level = "warn"
            status_tag = "WARN"
        else: # All attempted tasks succeeded (even if partially)
            level = "success"
            status_tag = "SUCCESS"

        final_message = f"Extraction finished. {success_count}/{tasks_attempted} ARC(s) processed successfully (or partially)."
        # Add overall status only if it wasn't full success
        final_message += f" Overall Status: {final_status.name}." if final_status != ArcErrorCode.SUCCESS else ""
        if submission_errors > 0: final_message += f" ({submission_errors} tasks failed to start)."
        final_message += f" Time: {duration:.2f}s."

        # Log the final summary with appropriate level and code
        self.log_status(final_message, level=level, code=final_status)

        # --- Trigger GUI Update ---
        # Use self.after to schedule enabling controls back on the main GUI thread
        self.after(0, callback_on_finish)


    # --- CREATION (Remains Sequential) ---
    def start_creation(self):
        input_dir = self.create_input_dir.get(); output_file = self.create_output_file.get(); arc_version = TARGET_ARC_VERSION # Use target
        # --- Input Validation ---
        if not input_dir: messagebox.showerror("Error", "No input directory selected."); self.log_status("Create fail: No input dir.", level="error", code=ArcErrorCode.INVALID_INPUT); return
        if not os.path.isdir(input_dir): messagebox.showerror("Error", f"Input directory not found or is not a directory:\n{input_dir}"); self.log_status(f"Create fail: Input directory invalid '{input_dir}'.", level="error", code=ArcErrorCode.DIRECTORY_NOT_FOUND); return
        if not output_file: messagebox.showerror("Error", "No output ARC file specified."); self.log_status("Create fail: No output file specified.", level="error", code=ArcErrorCode.INVALID_INPUT); return
        # --- Index File Validation ---
        arc_index_path = os.path.join(input_dir, ARC_INDEX_FILENAME)
        if not os.path.isfile(arc_index_path): messagebox.showerror("Error", f"Required '{ARC_INDEX_FILENAME}' not found or is not a file in:\n{input_dir}"); self.log_status(f"Create fail: '{ARC_INDEX_FILENAME}' missing or not file in '{input_dir}'.", level="error", code=ArcErrorCode.INDEX_NOT_FOUND); return
        if not os.access(arc_index_path, os.R_OK): messagebox.showerror("Error", f"Cannot read '{ARC_INDEX_FILENAME}' (check permissions):\n{arc_index_path}"); self.log_status(f"Create fail: Cannot read index '{arc_index_path}'.", level="error", code=ArcErrorCode.PERMISSION_ERROR); return
        # --- Output Directory/File Validation ---
        output_dir = os.path.dirname(output_file);
        if not output_dir: output_dir = "." # Use current directory if only filename given
        try: # Check/create output directory and permissions
            if not os.path.isdir(output_dir): self.log_status(f"Output directory '{output_dir}' missing, creating.", level="info"); os.makedirs(output_dir, exist_ok=True)
            if not os.access(output_dir, os.W_OK | os.X_OK): raise PermissionError(f"Write permission denied for directory '{output_dir}'")
            if os.path.exists(output_file) and not os.access(output_file, os.W_OK): raise PermissionError(f"Output file exists, cannot overwrite '{output_file}'")
        except (OSError, PermissionError) as e: messagebox.showerror("Error", f"Output dir/file access error:\n{output_dir}\n{e}"); self.log_status(f"Create fail: Output dir/file '{output_dir}'. Err: {e}", level="error", code=ArcErrorCode.PERMISSION_ERROR if isinstance(e, PermissionError) else ArcErrorCode.OS_ERROR); return
        # Start the sequential creation worker
        self._start_worker(self._create_worker, (input_dir, output_file, arc_version, arc_index_path), "Creation")

    def _create_worker(self, input_dir, output_filepath, arc_version, arc_index_path, callback_on_finish):
        """Worker thread for creation (sequential). Assumes inputs pre-validated."""
        start_time = time.time(); final_status = ArcErrorCode.SUCCESS; final_message = "Creation finished."; files_not_found = 0; read_errors = 0; invalid_lines = 0; processed_count = 0 # Init counters
        try:
            # --- Read Index File ---
            self.log_status(f"Reading index file: {arc_index_path}", level="debug")
            index_content_bytes = readFile(arc_index_path) # Handles FileNotFoundError, PermissionError, IOError

            # Decode index file safely
            try: index_content_str = index_content_bytes.decode('utf-8', errors='strict')
            except UnicodeDecodeError as e: self.log_status(f"Index file not UTF-8: {e}. Fallback decode.", level="warn", code=ArcErrorCode.UNICODE_ERROR); 
            try: index_content_str = index_content_bytes.decode(errors='replace'); 
            except Exception as e_dec: error(f"Index decode fail: {e_dec}", ArcErrorCode.UNICODE_ERROR)

            # Process index lines
            file_list_lines = [line for line in index_content_str.splitlines() if line.strip()]
            if not file_list_lines: error(f"'{ARC_INDEX_FILENAME}' is empty or contains no processable entries.", ArcErrorCode.INDEX_EMPTY)

            # --- Prepare ARC Object ---
            arc = ARC(); arc.version = arc_version; self.log_status(str(arc), level="debug"); self.log_status(f"Processing {len(file_list_lines)} entries from index...", level="info")

            # --- Process Files from Index ---
            for line_num, line in enumerate(file_list_lines, 1):
                line_prefix = f"Index Line #{line_num}"
                parts = line.split('\t')
                if len(parts) != 2: self.log_status(f"{line_prefix}: Skip invalid format: '{line}'", level="warn", code=ArcErrorCode.INDEX_INVALID_FORMAT); invalid_lines += 1; 
                if final_status == ArcErrorCode.SUCCESS: final_status = ArcErrorCode.INDEX_INVALID_FORMAT; continue
                relative_fwd, raw_hex = parts[0], parts[1]; relative_os = relative_fwd.replace('/', os.path.sep)
                if not relative_fwd or ".." in relative_os.split(os.path.sep): self.log_status(f"{line_prefix}: Skip invalid path: '{relative_fwd}'", level="warn", code=ArcErrorCode.INVALID_INPUT); invalid_lines += 1; 
                if final_status == ArcErrorCode.SUCCESS: final_status = ArcErrorCode.INVALID_INPUT; continue
                full_source = os.path.join(input_dir, relative_os)
                if len(raw_hex) != 8 or not all(c in '0123456789abcdefABCDEF' for c in raw_hex): self.log_status(f"{line_prefix}: Skip invalid hex '{raw_hex}'", level="warn", code=ArcErrorCode.INDEX_INVALID_FORMAT); invalid_lines += 1; 
                if final_status == ArcErrorCode.SUCCESS: final_status = ArcErrorCode.INDEX_INVALID_FORMAT; continue
                if not os.path.isfile(full_source): self.log_status(f"{line_prefix}: Source not found: '{full_source}'", level="error", code=ArcErrorCode.FILE_NOT_FOUND); files_not_found += 1; 
                if final_status == ArcErrorCode.SUCCESS: final_status = ArcErrorCode.FILE_NOT_FOUND; continue
                # Try reading and adding file
                try:
                    file_data = readFile(full_source) # Handles internal errors
                    if arc.add_file(relative_fwd, file_data, raw_hex): processed_count += 1 # add_file validates input
                    else: read_errors += 1; 
                    if final_status == ArcErrorCode.SUCCESS: final_status = ArcErrorCode.INVALID_INPUT # Count failed add as read error
                except RuntimeError as e_read: # Catch readFile errors
                     code = ArcErrorCode.IO_ERROR_READ;
                     if isinstance(e_read, PermissionError): code = ArcErrorCode.PERMISSION_ERROR
                     elif isinstance(e_read, FileNotFoundError): code = ArcErrorCode.FILE_NOT_FOUND # Should be caught above, but handle defensively
                     self.log_status(f"{line_prefix}: Read fail '{full_source}': {e_read}", level="error", code=code); read_errors += 1; 
                     if final_status == ArcErrorCode.SUCCESS: final_status = code; continue
                except Exception as e_add: # Catch unexpected add_file errors
                     self.log_status(f"{line_prefix}: Add fail '{relative_fwd}': {e_add}", level="error", code=ArcErrorCode.UNKNOWN_ERROR); read_errors += 1; 
                     if final_status == ArcErrorCode.SUCCESS: final_status = ArcErrorCode.UNKNOWN_ERROR; continue

            # --- Check if any files were added ---
            if processed_count == 0:
                 summary = []; [summary.append(f"{c} {n}") for c, n in [(files_not_found,"missing"),(read_errors,"read/add errs"),(invalid_lines,"invalid lines")] if c>0]; summary = summary or ["Unknown reason"];
                 final_err_code = final_status if final_status != ArcErrorCode.SUCCESS else ArcErrorCode.UNKNOWN_ERROR
                 error(f"Failed to add any valid files. Issues: {'; '.join(summary)}.", final_err_code)

            # Log summary if issues occurred but some files processed
            if files_not_found > 0 or read_errors > 0 or invalid_lines > 0:
                self.log_status(f"Prepared {processed_count} files. Issues: {files_not_found} missing, {read_errors} read/add errs, {invalid_lines} invalid lines.", level="warn", code=final_status)
            else:
                self.log_status(f"Successfully prepared {processed_count} files for archive.", level="success")

            # --- Export ARC Data ---
            self.log_status("Generating ARC file data...", level="info")
            output_data = arc.export_arc() # Can raise errors

            # --- Write Final ARC File ---
            self.log_status(f"Writing final ARC file: {output_filepath}", level="debug")
            writeFile(output_filepath, output_data) # Can raise errors

            # Determine final message and level
            if final_status == ArcErrorCode.SUCCESS: final_message = f"Creation successful. Output: '{output_filepath}'"; final_level = "success"
            else: final_message = f"Creation finished with warnings. Status: {final_status.name}. Output: '{output_filepath}'"; final_level = "warn"

        except RuntimeError as e_rt: # Catch errors raised by error() or ARC methods
             code = ArcErrorCode.UNKNOWN_ERROR; [code := c for c in ArcErrorCode if f"[{c.name}]" in str(e_rt)]; self.log_status(f"Creation failed: {e_rt}", level="error", code=code); final_status = code; final_message = "Creation failed."; final_level = "error"
        except Exception as e_create: # Catch other unexpected errors
             self.log_status(f"Unexpected error during creation: {e_create}", level="error", code=ArcErrorCode.UNKNOWN_ERROR); self.log_status(traceback.format_exc(), level="debug"); final_status = ArcErrorCode.UNKNOWN_ERROR; final_message = "Creation failed unexpected."; final_level = "error"
        finally:
             end_time = time.time(); duration = end_time - start_time
             if 'final_level' not in locals(): final_level = "error" # Ensure level is set
             final_message += f" Time: {duration:.2f}s."
             self.log_status(final_message, level=final_level, code=final_status)
             self.after(0, callback_on_finish) # Schedule GUI update


# --- Main Execution ---
if __name__ == "__main__":
    # enable_log(2) # Enable debug logging to console if needed
    app = ArcToolApp()
    try:
        app.mainloop()
    except Exception as e:
         # Log fatal errors that might crash the main loop (e.g., Tkinter issues)
         print(f"\n--- FATAL GUI ERROR ---"); print(traceback.format_exc())
         try: messagebox.showerror("Fatal Error", f"Error: {e}\nCheck console.")
         except: pass