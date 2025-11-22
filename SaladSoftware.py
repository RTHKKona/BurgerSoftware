VERSION = "2.4.2" 
# Stability Update: Atomic Writes, Threaded Scanning, Smart CLI & High-DPI Fix

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext, simpledialog
import tkinter.font as tkFont
import os
import sys
import hashlib
import struct
import zlib
import io
import threading
import queue
import pathlib
import concurrent.futures
import traceback
import time
import shutil
import re
import textwrap
import argparse
import ctypes # Added for High-DPI awareness
from collections import namedtuple
from datetime import datetime
from typing import List, Dict, Any, Optional, Union, Tuple

# --- HIGH-DPI FIX FOR WINDOWS ---
try:
    ctypes.windll.shcore.SetProcessDpiAwareness(1)
except Exception:
    try:
        ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass

# Check for PyCryptodome dependency
try:
    from Crypto.Cipher import Blowfish
except ImportError:
    root = tk.Tk()
    root.withdraw()
    messagebox.showerror("Missing Dependency", "The 'pycryptodome' library is required.\nPlease install it using: pip install pycryptodome")
    sys.exit(1)

try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
except ImportError:
    TkinterDnD = None

# --- CONSTANTS ---
BG_COLOR = '#2b2b2b'
TEXT_COLOR = '#ffebcd'
WIDGET_BG = '#3c3f41'
INPUT_TEXT_COLOR = '#f0f0f0'
BUTTON_BG = '#4c4c4c'
BUTTON_FG = TEXT_COLOR
BUTTON_ACTIVE_BG = '#5c5c5c'
BUTTON_PRESSED_BG = '#636363'
BUTTON_BORDER = '#1e1e1e'
HEADER_BG = '#4a4a4a'
HEADER_TEXT = TEXT_COLOR
HEADER_ACTIVE_BG = WIDGET_BG
HEADER_ACTIVE_TEXT = '#ffffff'
HIGHLIGHT_BG = '#52596b'
HIGHLIGHT_TEXT = '#00f7ff'
STATUS_ERROR_FG = '#ff6b6b'
STATUS_WARN_FG = '#ffb366'
STATUS_SUCCESS_FG = '#86e3a0'
STATUS_INFO_FG = TEXT_COLOR
STATUS_DEBUG_FG = '#999999'
CHECKED_TEXT_FG = '#00f7ff'

FONT_FAMILY = "Ubuntu Mono"
FONT_SIZE = 13
FONT_SETTINGS = (FONT_FAMILY, FONT_SIZE)

class Platform:
    UNKNOWN = 0
    PC = 1
    CTR = 2
    PS3 = 3
    Switch = 4

DEFAULT_VERSION = 9
DEFAULT_BYTE_ORDER_CHAR = '<'
DEFAULT_PLATFORM = Platform.Switch

FMT_HEADER_COMMON = "4sHH"
SIZE_HEADER_COMMON = 8
FMT_HEADER_PC_EXTRA = "I"
SIZE_HEADER_PC_EXTRA = 4
FMT_ENTRY = "64sIiii"
SIZE_ENTRY = 80
FMT_ENTRY_SWITCH = "64sIIIII"
SIZE_ENTRY_SWITCH = 84
FMT_ENTRY_EXTENDED_NAME = "128sIiii"
SIZE_ENTRY_EXTENDED_NAME = 144

ZLIB_COMPRESSION_LEVEL = 9
ALIGNMENT_SWITCH = 0x8000
ALIGNMENT_PC_DEFAULT = 0x100
ALIGNMENT_PC_V7_V10_LE = 0x8000
ALIGNMENT_PC_V17_PER_FILE = 0x800

MAGIC_ARC_LE = b'ARC\x00'
MAGIC_ARC_BE = b'\x00CRA'

STATUS_INFO = "info"
STATUS_SUCCESS = "success"
STATUS_WARN = "warn"
STATUS_ERROR = "error"
STATUS_DEBUG = "debug"

# Optimized Worker Caps
MAX_COMPRESSION_WORKERS = os.cpu_count() or 4
MAX_IO_WORKERS = min(os.cpu_count() or 4, 4) # Cap IO workers to prevent disk thrashing/OOM

# Safety Limits
MAX_SAFE_ALLOCATION = 2 * 1024 * 1024 * 1024 # 2GB Safety Limit per file

CHECK_UNCHECKED = "☐"
CHECK_CHECKED = "☑"

EXTENSION_MAP = {}
REV_EXTENSION_MAP = {}
EXTENSION_MAP_FILE = "unique_extensions.txt"
GAME_SPECIFIC_HASH_FILE = "extension_index_line.txt"

DEBUG_PER_FILE = False
DEBUG_VERIFY_HASH = False

# Pre-compiled regex for flattening
FILENAME_SANITIZER = re.compile(r'[\\/:*?"<>|]')

class ARCCSkippedError(ValueError):
    """Custom exception for when an ARCC file is intentionally skipped."""
    pass

def format_struct(endian: str, pattern: str) -> str:
    return endian + pattern

def resource_path(relative_path: str) -> str:
    """Get absolute path to resource, works for dev and for PyInstaller."""
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base_path, relative_path)

def get_safe_path_str(path_obj: pathlib.Path) -> str:
    #Returns a path string safe for Windows long paths (\\?\) to prevent crashes.
    absolute_path = path_obj.resolve()
    if os.name == 'nt' and not str(absolute_path).startswith('\\\\?\\'):
        return f"\\\\?\\{absolute_path}"
    return str(absolute_path)

def get_sha256_hash(filepath: Union[str, pathlib.Path]) -> str:
    """Calculates the SHA256 hash of a file, reading it in chunks."""
    hash_sha256 = hashlib.sha256()
    try:
        with open(get_safe_path_str(pathlib.Path(filepath)), "rb") as f:
            while chunk := f.read(65536):
                hash_sha256.update(chunk)
        return hash_sha256.hexdigest()
    except FileNotFoundError:
        return "ERROR: File not found"
    except Exception as e:
        return f"ERROR: {e}"

# --- ARC UTILITIES ---
ARCHeader = namedtuple("ARCHeader", ["magic", "version", "entry_count"])

def create_file_info() -> Dict[str, Any]:
    return {
        "filename_base": b'',
        "ext_hash": 0,
        "compressed_size": 0,
        "uncompressed_size_raw": 0,
        "offset": 0,
        "unknown1": None,
        "platform": Platform.UNKNOWN,
        "data": None,
        "full_filename": "",
        "is_compressed": False,
        "is_raw_deflate": False,
        "calculated_uncompressed_size": 0,
        "original_is_compressed_hint": False,
        "original_uncompressed_size_raw_hint": 0,
        "data_is_precompressed": False
    }

def calculate_arc_hash(s: str) -> int:
    if not s: return 0
    return (~zlib.crc32(s.encode('latin-1'))) & 0xFFFFFFFF

def load_extension_map(primary_filepath: str, game_specific_filepath: Optional[str] = None):
    global EXTENSION_MAP, REV_EXTENSION_MAP
    EXTENSION_MAP = {}
    REV_EXTENSION_MAP = {}
    
    if not os.path.isfile(primary_filepath):
        print(f"Warning: Primary extension map file not found at '{primary_filepath}'.", file=sys.stderr)
    else:
        try:
            with open(primary_filepath, 'r', encoding='utf-8') as f:
                for line in f:
                    line = line.strip()
                    if not line or line.startswith(('#', '//')): continue
                    if '=' in line:
                        parts = line.split('=', 1)
                        hash_str, ext_str = parts[0].strip(), parts[1].strip()
                        if len(hash_str) == 8:
                            try:
                                hash_val = int(hash_str, 16)
                                ext_with_dot = "." + ext_str
                                EXTENSION_MAP[hash_val] = ext_with_dot
                                REV_EXTENSION_MAP[ext_with_dot.lower()] = hash_val
                            except ValueError: continue
                    else:
                        ext_with_dot = "." + line
                        hash_val = calculate_arc_hash(line)
                        if hash_val not in EXTENSION_MAP:
                            EXTENSION_MAP[hash_val] = ext_with_dot
                        if ext_with_dot.lower() not in REV_EXTENSION_MAP:
                            REV_EXTENSION_MAP[ext_with_dot.lower()] = hash_val
        except Exception as e:
            print(f"Error loading primary extension map: {e}", file=sys.stderr)

    if game_specific_filepath and os.path.isfile(game_specific_filepath):
        try:
            with open(game_specific_filepath, 'r', encoding='utf-8') as f_game:
                for line in f_game:
                    line = line.strip()
                    if not line or line.startswith(('#', '//')): continue
                    parts = line.split(',', 1)
                    if len(parts) == 2:
                        hash_str, ext_str = parts[0].strip(), parts[1].strip()
                        if ext_str.startswith('.'):
                            try:
                                hash_val = int(hash_str, 16)
                                EXTENSION_MAP[hash_val] = ext_str
                                REV_EXTENSION_MAP[ext_str.lower()] = hash_val
                            except ValueError: continue
        except Exception as e:
            print(f"Error loading game-specific extension map: {e}", file=sys.stderr)

def get_full_filename(file_info: Dict[str, Any]) -> str:
    try:
        filename_bytes = file_info.get("filename_base", b'').split(b'\x00', 1)[0]
        try:
            name = filename_bytes.decode('ascii')
        except UnicodeDecodeError:
            name = filename_bytes.decode('shift-jis', errors='replace')
    except Exception:
        name = "decode_error"
    
    hash_val = file_info.get("ext_hash", 0)
    ext = EXTENSION_MAP.get(hash_val, f".{hash_val:08X}")
    # Remove null bytes from final name to prevent OS errors
    return (name + ext).rstrip('\x00')

def get_calculated_uncompressed_size(file_info: Dict[str, Any]) -> int:
    p = file_info.get("platform")
    u_raw = file_info.get("uncompressed_size_raw", 0)
    if p == Platform.PC: return u_raw & 0x00FFFFFF
    if p == Platform.PS3: return u_raw >> 3
    if p == Platform.Switch: return u_raw
    return u_raw & 0x00FFFFFF

def compress_kontract_zlib(data: bytes, is_raw_deflate: bool = False) -> bytes:
    if not data: return b''
    wbits = -zlib.MAX_WBITS if is_raw_deflate else 15
    compressor = zlib.compressobj(level=ZLIB_COMPRESSION_LEVEL, method=zlib.DEFLATED, wbits=wbits)
    compressed_data = compressor.compress(data)
    compressed_data += compressor.flush()
    return compressed_data

def decompress_kontract_zlib(compressed_data: bytes) -> bytes:
    if not compressed_data: return b''
    try:
        return zlib.decompress(compressed_data)
    except zlib.error:
        try:
            return zlib.decompress(compressed_data, -zlib.MAX_WBITS)
        except zlib.error as e_raw:
            raise RuntimeError("Decompression failed for both standard and raw deflate streams.") from e_raw

class MTArc:
    # Slots optimization for memory efficiency when handling thousands of entries
    __slots__ = ['arc_header', 'files', '_raw_file_path', '_file_size', 'version', 'platform', 'byte_order_char', 'entry_has_extended_names']

    def __init__(self):
        self.arc_header = None
        self.files = []
        self._raw_file_path = None
        self._file_size = None
        self.version = 0
        self.platform = Platform.UNKNOWN
        self.byte_order_char = '<'
        self.entry_has_extended_names = False

    def close(self):
        self.files.clear()
        self.files = []
        self.arc_header = None
        self._raw_file_path = None

    def load(self, filepath: str, key1=None, key2=None, status_queue_or_callback=None):
        self.__init__()
        
        def _q_status(msg, level):
            if status_queue_or_callback:
                if hasattr(status_queue_or_callback, 'put'):
                    status_queue_or_callback.put({'type': 'status', 'msg': msg, 'level': level})
                else:
                    status_queue_or_callback(msg, level)
            else:
                print(f"[{level.upper()}]: {msg}", file=sys.stderr)

        try:
            if not os.path.isfile(filepath):
                raise FileNotFoundError(f"File not found: {filepath}")

            self._raw_file_path = filepath
            self._file_size = os.path.getsize(filepath)

            # Use safe path string for Windows long paths
            with open(get_safe_path_str(pathlib.Path(filepath)), 'rb') as f_raw:
                magic = f_raw.read(4)
                f_raw.seek(0)
                prelim_bo = '>' if magic == MAGIC_ARC_BE else '<'
                try:
                    header_buffer = f_raw.read(SIZE_HEADER_COMMON)
                    if len(header_buffer) < SIZE_HEADER_COMMON:
                        raise struct.error("Not enough data for header")
                    _, prelim_ver, _ = struct.unpack(format_struct(prelim_bo, "4sHH"), header_buffer)
                except struct.error:
                    _q_status(f"Could not read preliminary header for {os.path.basename(filepath)}. Skipping.", STATUS_ERROR)
                    return
                finally:
                    f_raw.seek(0)

                if prelim_ver == 9:
                    self.platform, self.byte_order_char = Platform.Switch, '<'
                elif magic == MAGIC_ARC_BE:
                    self.platform, self.byte_order_char = Platform.PS3, '>'
                else:
                    self.platform, self.byte_order_char = Platform.PC, '<'
                
                header_data = f_raw.read(SIZE_HEADER_COMMON)
                self.arc_header = ARCHeader(*struct.unpack(format_struct(self.byte_order_char, "4sHH"), header_data))
                self.version = self.arc_header.version
                
                if self.byte_order_char == '<' and self.version not in [7, 8]:
                    f_raw.read(SIZE_HEADER_PC_EXTRA)

                if self.arc_header.entry_count <= 0: return

                self.entry_has_extended_names = False
                if self.platform != Platform.Switch and self.arc_header.entry_count > 0:
                    current_pos = f_raw.tell()
                    try:
                        first_entry_bytes = f_raw.read(SIZE_ENTRY)
                        if len(first_entry_bytes) >= SIZE_ENTRY:
                            _, ext_hash, _, decomp_size, offset = struct.unpack(format_struct(self.byte_order_char, FMT_ENTRY), first_entry_bytes)
                            if ext_hash == 0 or decomp_size == 0 or offset == 0:
                                self.entry_has_extended_names = True
                    finally:
                        f_raw.seek(current_pos)

                if self.entry_has_extended_names:
                    entry_fmt = format_struct(self.byte_order_char, FMT_ENTRY_EXTENDED_NAME)
                    entry_size = SIZE_ENTRY_EXTENDED_NAME
                    fields = ["filename_base", "ext_hash", "compressed_size", "uncompressed_size_raw", "offset"]
                elif self.platform == Platform.Switch:
                    entry_fmt = '<' + FMT_ENTRY_SWITCH
                    entry_size = SIZE_ENTRY_SWITCH
                    fields = ["filename_base", "ext_hash", "compressed_size", "uncompressed_size_raw", "unknown1", "offset"]
                else:
                    entry_fmt = format_struct(self.byte_order_char, FMT_ENTRY)
                    entry_size = SIZE_ENTRY
                    fields = ["filename_base", "ext_hash", "compressed_size", "uncompressed_size_raw", "offset"]

                self.files = []
                for i in range(self.arc_header.entry_count):
                    fi = create_file_info()
                    fi["platform"] = self.platform
                    entry_data = f_raw.read(entry_size)
                    if len(entry_data) < entry_size: break
                    
                    fi.update(zip(fields, struct.unpack(entry_fmt, entry_data)))
                    fi["calculated_uncompressed_size"] = get_calculated_uncompressed_size(fi)
                    
                    # Safety Check for Corrupt/Malicious files reporting massive sizes
                    if fi["calculated_uncompressed_size"] > MAX_SAFE_ALLOCATION:
                        _q_status(f"Warning: Entry #{i} reports size > 2GB ({fi['calculated_uncompressed_size']}). Skipping memory pre-checks to prevent crash.", STATUS_WARN)
                    
                    is_size_different = fi["compressed_size"] != fi["calculated_uncompressed_size"]
                    
                    fi["is_compressed"] = is_size_different or self.platform == Platform.Switch
                    fi["is_raw_deflate"] = False 

                    if fi["is_compressed"]:
                        peek_pos = f_raw.tell()
                        f_raw.seek(fi["offset"])
                        # Only peek if size is reasonable
                        if fi["compressed_size"] < 10 * 1024 * 1024: # 10MB Peek
                            comp_block = f_raw.read(fi["compressed_size"])
                            try:
                                zlib.decompress(comp_block)
                                fi["is_raw_deflate"] = False
                            except zlib.error:
                                try:
                                    zlib.decompress(comp_block, -zlib.MAX_WBITS)
                                    fi["is_raw_deflate"] = True
                                except zlib.error:
                                    fi["is_compressed"] = False
                        f_raw.seek(peek_pos)
                    
                    fi["full_filename"] = get_full_filename(fi).replace('\\', '/')
                    fi["original_is_compressed_hint"] = fi["is_compressed"]
                    fi["original_is_raw_deflate_hint"] = fi["is_raw_deflate"]
                    fi["original_uncompressed_size_raw_hint"] = fi["uncompressed_size_raw"]
                    self.files.append(fi)

        except Exception as e:
            _q_status(f"CRITICAL ERROR loading ARC: {e}", STATUS_ERROR)
            traceback.print_exc(file=sys.stderr)
            raise

    def get_raw_compressed_block(self, file_info, input_arc_path):
        if not self._raw_file_path or self._raw_file_path != input_arc_path:
            raise RuntimeError("MTArc state is invalid for raw extraction.")
        offset = file_info.get("offset", 0)
        comp_size = file_info.get("compressed_size", 0)
        if comp_size == 0: return b''
        with open(get_safe_path_str(pathlib.Path(self._raw_file_path)), 'rb') as f:
            f.seek(offset)
            return f.read(comp_size)

    def extract_file(self, file_info, input_arc_path):
        data_block = self.get_raw_compressed_block(file_info, input_arc_path)
        # Handle empty ZLIB blocks safely
        if not data_block: 
            return b''
        if file_info.get("is_compressed"):
            wbits = -zlib.MAX_WBITS if file_info.get("is_raw_deflate") else zlib.MAX_WBITS
            return zlib.decompress(data_block, wbits)
        return data_block

    def save(self, output_path, input_file_infos, **kwargs):
        def _q_status(msg, level):
            cb = kwargs.get('status_callback')
            if cb:
                if hasattr(cb, 'put'): cb.put({'type': 'status', 'msg': msg, 'level': level})
                else: cb(msg, level)
            else:
                print(f"[{level.upper()}]: {msg}", file=sys.stderr)

        if not input_file_infos: raise ValueError("No file info to save.")

        p = kwargs.get('target_platform', self.platform)
        v = kwargs.get('target_version', self.version)
        bo = kwargs.get('target_byte_order_char', self.byte_order_char)
        ext_names = kwargs.get('target_entry_has_extended_names', self.entry_has_extended_names)
        
        if ext_names:
            entry_fmt = format_struct(bo, FMT_ENTRY_EXTENDED_NAME)
            entry_size = SIZE_ENTRY_EXTENDED_NAME
        elif p == Platform.Switch:
            entry_fmt = '<' + FMT_ENTRY_SWITCH
            entry_size = SIZE_ENTRY_SWITCH
        else:
            entry_fmt = format_struct(bo, FMT_ENTRY)
            entry_size = SIZE_ENTRY

        header_size = SIZE_HEADER_COMMON
        is_extended_header = (bo == '<' and v not in [7, 8])
        if is_extended_header: header_size += SIZE_HEADER_PC_EXTRA
        
        unaligned_data_offset = header_size + (len(input_file_infos) * entry_size)
        data_start_offset = unaligned_data_offset
        alignment = 0
        if bo == '<':
            if v in [4, 7, 8, 17, 0x10]: alignment = ALIGNMENT_PC_V7_V10_LE
            elif v == 9: alignment = ALIGNMENT_SWITCH
            elif v == 0x11: alignment = ALIGNMENT_PC_DEFAULT
        if alignment > 0:
            data_start_offset = (unaligned_data_offset + alignment - 1) & ~(alignment - 1)
        
        # --- PARALLEL COMPRESSION STEP ---
        files_to_compress = []
        for idx, fi in enumerate(input_file_infos):
            if not fi.get('data_is_precompressed', False) and fi.get("original_is_compressed_hint", True):
                files_to_compress.append((idx, fi))
        
        processed_data_map = {} 

        def _compress_task(args):
            idx, fi = args
            raw_data = fi.get("data", b"")
            is_raw = fi.get("original_is_raw_deflate_hint", False)
            return idx, compress_kontract_zlib(raw_data, is_raw)

        if files_to_compress:
            _q_status(f"Compressing {len(files_to_compress)} files in parallel...", STATUS_DEBUG)
            # Use CPU Count for compression
            with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_COMPRESSION_WORKERS) as executor:
                results = executor.map(_compress_task, files_to_compress)
                for idx, comp_data in results:
                    processed_data_map[idx] = comp_data
        
        # --- WRITE STEP ---
        current_offset = data_start_offset
        metadata_list = []

        # Write to the output path (expected to be temporary or resolved by caller)
        with open(get_safe_path_str(pathlib.Path(output_path)), 'wb') as f:
            magic = MAGIC_ARC_BE if bo == '>' else b'ARC\x00'
            f.write(struct.pack(format_struct(bo, "4sHH"), magic, v, len(input_file_infos)))
            if is_extended_header: f.write(struct.pack('<I', 0))
            
            entries_start_pos = f.tell()
            f.write(b'\x00' * (len(input_file_infos) * entry_size))
            
            padding_size = data_start_offset - f.tell()
            if padding_size > 0: f.write(b'\x00' * padding_size)
            
            for idx, fi in enumerate(input_file_infos):
                meta = fi.copy()
                
                if fi.get('data_is_precompressed', False):
                    final_data = fi.get("data", b"")
                    uncomp_size = fi.get("calculated_uncompressed_size", 0)
                elif idx in processed_data_map:
                    final_data = processed_data_map[idx]
                    uncomp_size = len(fi.get("data", b""))
                else:
                    final_data = fi.get("data", b"")
                    uncomp_size = len(final_data)

                f.write(final_data)
                
                meta["offset"] = current_offset
                meta["compressed_size"] = len(final_data)
                
                orig_raw_size_hint = fi.get("original_uncompressed_size_raw_hint", 0)
                if p == Platform.PC:
                    meta["uncompressed_size_raw"] = (orig_raw_size_hint & 0xFF000000) | (uncomp_size & 0x00FFFFFF)
                elif p == Platform.Switch:
                    meta["uncompressed_size_raw"] = uncomp_size
                    meta["unknown1"] = zlib.crc32(final_data) & 0xFFFFFFFF 
                elif p == Platform.PS3:
                    meta["uncompressed_size_raw"] = (orig_raw_size_hint & 0x7) | (uncomp_size << 3)
                else:
                    meta["uncompressed_size_raw"] = uncomp_size
                
                metadata_list.append(meta)
                current_offset += len(final_data)

            f.seek(entries_start_pos)
            for meta in metadata_list:
                name_bytes = meta.get("filename_base", b"")
                name_padded = name_bytes.ljust(128 if ext_names else 64, b'\x00')
                
                if p == Platform.Switch:
                    vals = (name_padded, meta["ext_hash"], meta["compressed_size"], meta["uncompressed_size_raw"], meta.get("unknown1", 0), meta["offset"])
                else:
                    vals = (name_padded, meta["ext_hash"], meta["compressed_size"], meta["uncompressed_size_raw"], meta["offset"])
                
                f.write(struct.pack(entry_fmt, *vals))

        _q_status(f"Successfully saved ARC to '{os.path.basename(output_path)}'.", STATUS_SUCCESS)

# --- WORKER FUNCTIONS ---

def _from_scratch_rebuild_worker(source_folder_str, output_dir_str, key1, key2, status_callback_worker, **kwargs):
    source_folder_path = pathlib.Path(source_folder_str)
    output_dir = pathlib.Path(output_dir_str)
    
    # Stability: Atomic Write using .tmp
    arc_base_name = source_folder_path.name[:-4] if source_folder_path.name.endswith("_arc") else source_folder_path.name
    final_arc_path = output_dir / f"{arc_base_name}.arc"
    temp_arc_path = output_dir / f"{arc_base_name}.arc.tmp"

    try:
        status_callback_worker(f"Starting scratch-rebuild for '{source_folder_path.name}'.", STATUS_INFO)
        
        files_to_pack = []
        disk_files = sorted([p for p in source_folder_path.rglob('*') if p.is_file()])
        
        for file_path_obj in disk_files:
            fi = create_file_info()
            arc_fn = str(file_path_obj.relative_to(source_folder_path)).replace(os.sep, '/')
            base_name, ext = os.path.splitext(arc_fn)
            fi.update({
                "full_filename": arc_fn, 
                "filename_base": base_name.encode('ascii', 'ignore'),
                "ext_hash": calculate_arc_hash(ext) if not ext[1:].isupper() else int(ext[1:], 16),
                "data": file_path_obj.read_bytes(),
                "original_is_compressed_hint": True,
                "original_is_raw_deflate_hint": False,
                "data_is_precompressed": False
            })
            files_to_pack.append(fi)

        arc_saver = MTArc()
        arc_saver.save(str(temp_arc_path), files_to_pack, status_callback=status_callback_worker)
        
        # Rename atomic
        if final_arc_path.exists():
            final_arc_path.unlink()
        temp_arc_path.rename(final_arc_path)

        return source_folder_path.name, True

    except Exception as e:
        if temp_arc_path.exists(): 
            try: temp_arc_path.unlink()
            except: pass
        status_callback_worker(f"CRITICAL ERROR in scratch-rebuild for '{source_folder_path.name}': {e}", STATUS_ERROR)
        traceback.print_exc(file=sys.stderr)
        return source_folder_path.name, False

def _in_place_rebuild_worker(source_folder_str, _ignored_output_dir, key1, key2, status_callback_worker, **kwargs):
    move_originals_on_success = kwargs.get('move_originals', False)
    source_folder_path = pathlib.Path(source_folder_str)
    
    arc_base_name = source_folder_path.name[:-4]
    original_arc_path = source_folder_path.parent / (arc_base_name + ".arc")
    backup_arc_path = source_folder_path.parent / (arc_base_name + "_original.arc")
    # Temp file for atomic write
    temp_arc_path = source_folder_path.parent / (arc_base_name + ".arc.tmp_rebuild")
    target_backup_path = None

    try:
        if not original_arc_path.is_file():
            raise FileNotFoundError(f"Cannot perform in-place rebuild: Original file '{original_arc_path}' not found.")
        
        if backup_arc_path.exists() and not move_originals_on_success:
             status_callback_worker(f"ERROR: A backup file '{backup_arc_path.name}' already exists.", STATUS_ERROR)
             return source_folder_path.name, False
        
        status_callback_worker(f"Starting high-fidelity rebuild for '{original_arc_path.name}'...", STATUS_INFO)
        original_arc = MTArc()
        original_arc.load(str(original_arc_path), status_queue_or_callback=status_callback_worker)

        files_to_pack = []
        
        for original_fi in original_arc.files:
            new_fi = original_fi.copy()
            disk_file_path = source_folder_path / original_fi['full_filename']
            
            use_original_data = False
            disk_data = b""

            if not disk_file_path.is_file():
                status_callback_worker(f"'{original_fi['full_filename']}' missing. Re-using original.", STATUS_WARN)
                use_original_data = True
            else:
                # Memory Optimization: Don't read full file yet
                disk_file_stat = disk_file_path.stat()
                orig_uncomp_size = get_calculated_uncompressed_size(original_fi)

                # 1. Fast Check: Size Difference
                if disk_file_stat.st_size != orig_uncomp_size:
                    use_original_data = False
                else:
                    # 2. Compare bytes (Safety check without loading everything if possible)
                    # For absolute safety we extract original to memory to compare
                    original_decompressed = original_arc.extract_file(original_fi, str(original_arc_path))
                    with open(get_safe_path_str(disk_file_path), 'rb') as f_disk:
                        disk_data_temp = f_disk.read()
                    
                    if disk_data_temp == original_decompressed:
                        use_original_data = True
                        del disk_data_temp # Free memory
                        del original_decompressed
                    else:
                        use_original_data = False
                        # disk_data_temp is needed, store it
                        disk_data = disk_data_temp
                        del original_decompressed
            
            if use_original_data:
                # Copy raw compressed bytes from old file (Instant)
                new_fi['data'] = original_arc.get_raw_compressed_block(original_fi, str(original_arc_path))
                new_fi['data_is_precompressed'] = True
            else:
                # Mark for later parallel compression
                if not disk_data: # If not loaded during compare
                    disk_data = disk_file_path.read_bytes()
                
                status_callback_worker(f"Change detected in '{original_fi['full_filename']}'.", STATUS_DEBUG)
                new_fi['data'] = disk_data
                new_fi['data_is_precompressed'] = False
            
            files_to_pack.append(new_fi)

        arc_saver = MTArc()
        save_kwargs = { 
            'status_callback': status_callback_worker, 
            'target_version': original_arc.version, 
            'target_platform': original_arc.platform,
            'target_byte_order_char': original_arc.byte_order_char, 
            'target_entry_has_extended_names': original_arc.entry_has_extended_names 
        }
        # Write to .tmp file first
        arc_saver.save(str(temp_arc_path), files_to_pack, **save_kwargs)
        
        original_arc.close()
        arc_saver.close()

        # Atomic Swap
        if backup_arc_path.exists(): backup_arc_path.unlink()
        original_arc_path.rename(backup_arc_path)
        
        # Rename with retry for Windows file locking
        for _ in range(3):
            try:
                temp_arc_path.rename(original_arc_path)
                break
            except OSError:
                time.sleep(1)
        else:
            raise OSError(f"Could not rename temp file to {original_arc_path}")

        status_callback_worker(f"Successfully rebuilt '{original_arc_path.name}'.", STATUS_SUCCESS)
        
        if move_originals_on_success:
            try:
                original_data_dir = original_arc_path.parent / "original_data"
                original_data_dir.mkdir(exist_ok=True)
                target_backup_path = original_data_dir / backup_arc_path.name
                shutil.move(str(backup_arc_path), str(target_backup_path))
                target_folder_path = original_data_dir / source_folder_path.name
                if target_folder_path.exists(): shutil.rmtree(target_folder_path)
                shutil.move(str(source_folder_path), str(target_folder_path))
            except Exception as move_e:
                status_callback_worker(f"Rebuild OK, but move failed: {move_e}", STATUS_ERROR)

        # Debug Hash Verification
        if DEBUG_VERIFY_HASH:
            status_callback_worker("--- STARTING HASH VERIFICATION ---", STATUS_DEBUG)
            check_path = target_backup_path if (move_originals_on_success and target_backup_path) else backup_arc_path
            orig_hash = get_sha256_hash(check_path)
            new_hash = get_sha256_hash(original_arc_path)
            status_callback_worker(f"Original: {orig_hash}", STATUS_DEBUG)
            status_callback_worker(f"New:      {new_hash}", STATUS_DEBUG)
            if orig_hash == new_hash: status_callback_worker("HASH MATCH: Identical.", STATUS_SUCCESS)
            else: status_callback_worker("HASH MISMATCH.", STATUS_ERROR)

        return source_folder_path.name, True
        
    except Exception as e:
        status_callback_worker(f"CRITICAL ERROR: {e}", STATUS_ERROR)
        traceback.print_exc(file=sys.stderr)
        if temp_arc_path.is_file(): temp_arc_path.unlink()
        if backup_arc_path.is_file() and not original_arc_path.exists(): backup_arc_path.rename(original_arc_path)
        return source_folder_path.name, False

def _list_extract_worker(arc_path_str, output_base_dir_str, key1, key2, status_callback_worker):
    arc_path = pathlib.Path(arc_path_str)
    arc = MTArc()
    try:
        arc.load(str(arc_path), status_queue_or_callback=status_callback_worker)
        output_folder = arc_path.parent / f"{arc_path.stem}_arc"
        output_folder.mkdir(parents=True, exist_ok=True)
        
        for fi in arc.files:
            try:
                out_path = output_folder / fi['full_filename']
                out_path.parent.mkdir(parents=True, exist_ok=True)
                # Safe Path Writing
                with open(get_safe_path_str(out_path), 'wb') as f_out:
                    f_out.write(arc.extract_file(fi, str(arc_path)))
            except Exception as e:
                status_callback_worker(f"Error extracting '{fi.get('full_filename','?')}': {e}", STATUS_ERROR)
                
        status_callback_worker(f"Finished extracting {arc_path.name}", STATUS_SUCCESS)
        return arc_path.name, True
    except Exception as e:
        status_callback_worker(f"Failed to process {arc_path.name}: {e}", STATUS_ERROR)
        return arc_path.name, False
    finally:
        arc.close()

def _flatten_extract_worker(arc_path_str, common_output_dir_str, key1, key2, status_callback_worker):
    arc_path = pathlib.Path(arc_path_str)
    common_output_dir = pathlib.Path(common_output_dir_str)
    arc = MTArc()
    try:
        arc.load(str(arc_path), status_queue_or_callback=status_callback_worker)
        for fi in arc.files:
            try:
                data = arc.extract_file(fi, str(arc_path))
                # Optimized Regex
                sanitized_name = FILENAME_SANITIZER.sub('_', pathlib.Path(fi['full_filename']).name)
                flat_name = f"{arc_path.stem}_{sanitized_name}"
                counter = 1
                out_path = common_output_dir / flat_name
                
                while out_path.exists():
                    out_path = common_output_dir / f"{arc_path.stem}_{pathlib.Path(sanitized_name).stem}_{counter}{pathlib.Path(sanitized_name).suffix}"
                    counter += 1
                
                with open(get_safe_path_str(out_path), 'wb') as f_out:
                    f_out.write(data)
            except Exception as e:
                status_callback_worker(f"Error flat-extracting '{fi['full_filename']}': {e}", STATUS_ERROR)
        status_callback_worker(f"Finished flat extraction for {arc_path.name}", STATUS_SUCCESS)
        return arc_path.name, True
    except Exception as e:
        status_callback_worker(f"Failed to process {arc_path.name} for flat extraction: {e}", STATUS_ERROR)
        return arc_path.name, False
    finally:
        arc.close()

def recursive_batch_extract(source_root_dir, _, progress_callback, status_callback, key1, key2):
    source_path = pathlib.Path(source_root_dir)
    arc_files = [str(f) for f in source_path.rglob('*.arc') if f.is_file()]
    if not arc_files:
        status_callback("No *.arc files found.", STATUS_WARN)
        return
    run_batch_parallel(_list_extract_worker, arc_files, None, progress_callback, status_callback, key1, key2)

def recursive_flatten_extract(source_root_dir, common_output_dir, progress_callback, status_callback, key1, key2):
    source_path = pathlib.Path(source_root_dir)
    arc_files = [str(f) for f in source_path.rglob('*.arc') if f.is_file()]
    if not arc_files:
        status_callback("No *.arc files found.", STATUS_WARN)
        return
    run_batch_parallel(_flatten_extract_worker, arc_files, common_output_dir, progress_callback, status_callback, key1, key2)

def run_batch_parallel(worker_func, item_list, output_dir, progress_callback, status_callback, key1, key2, **kwargs):
    if not item_list: return []
    results = []
    # Optimization: Use MAX_IO_WORKERS to prevent IO Thrashing/OOM
    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_IO_WORKERS) as executor:
        futures = []
        for i, item in enumerate(item_list):
            worker_kwargs = {}
            for key, val_list in kwargs.items():
                if isinstance(val_list, list) and i < len(val_list):
                    worker_kwargs[key] = val_list[i]
            
            futures.append(executor.submit(worker_func, item, output_dir, key1, key2, status_callback, **worker_kwargs))

        completed = 0
        for future in concurrent.futures.as_completed(futures):
            try:
                result = future.result()
                results.append(result)
            except Exception as e:
                status_callback(f"Worker thread error: {e}", STATUS_ERROR)
                results.append((None, False))
            completed += 1
            if progress_callback:
                progress_callback(completed / len(futures) * 100)
                
    status_callback("Batch operation complete.", STATUS_SUCCESS)
    return results

# --- GUI AND CLI CODE ---
class ArcToolApp:
    def __init__(self, root, startup_file=None):
        self.root = root
        self.root.title("SaladSoftware ARC Tool")
        self.root.configure(bg=BG_COLOR)
        self.root.geometry("1532x950")
        
        self.default_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE)
        self.bold_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE, weight="bold")
        self.title_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE + 2, weight="bold")
        self.tab_label_font = tkFont.Font(family=FONT_FAMILY, size=FONT_SIZE - 2)
        
        self.queue = queue.Queue()
        self.style = ttk.Style()
        self.configure_styles()

        self.main_paned_window = ttk.PanedWindow(root, orient=tk.VERTICAL, style='TPanedwindow')
        self.main_paned_window.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        self.top_pane_frame = ttk.Frame(self.main_paned_window, style='TFrame')
        self.main_paned_window.add(self.top_pane_frame, weight=3)

        header_frame = ttk.Frame(self.top_pane_frame, style='TFrame')
        header_frame.pack(pady=5, padx=10, fill='x')
        
        ttk.Label(header_frame, text=f"~ Handburger's SaladSoftware MT Arc Tool ~ Version {VERSION}", style='TLabel', font=self.title_font).pack(side=tk.LEFT, anchor='w')
        
        self.help_button = ttk.Button(header_frame, text="Help", command=self.show_help, style='TButton')
        self.help_button.pack(side=tk.RIGHT, padx=5, pady=5)
        
        self.debug_verify_hash_button = ttk.Button(header_frame, text="...", command=self.toggle_debug_verify_hash, style='TButton')
        self.debug_verify_hash_button.pack(side=tk.RIGHT, padx=(0, 5))
        
        self.debug_per_file_button = ttk.Button(header_frame, text="...", command=self.toggle_debug_per_file, style='TButton')
        self.debug_per_file_button.pack(side=tk.RIGHT, padx=(0, 5))
        self.update_debug_buttons_text()

        attribution_text = "Uses Kuriimu1 and Kuriimu2 MT Arc Logic (GPL-3.0 License - legal permission to copy, distribute, and modify)"
        ttk.Label(self.top_pane_frame, text=attribution_text, style='TLabel', font=self.tab_label_font).pack(anchor='w', pady=(0, 10), padx=10)

        self.notebook = ttk.Notebook(self.top_pane_frame, style='TNotebook')
        
        self.list_extract_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)
        self.folder_inject_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)
        self.list_inject_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)
        self.rec_extract_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)
        self.rec_inject_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)
        self.flatten_extract_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)
        self.internal_arc_extract_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)
        self.internal_arc_inject_frame = ttk.Frame(self.notebook, style='TFrame', padding=10)

        self.notebook.add(self.list_extract_frame, text='1. Extract from ARC(s)')
        self.notebook.add(self.folder_inject_frame, text='2. Repack Folder (In-Place)')
        self.notebook.add(self.list_inject_frame, text='3. Build New ARC from Folder')
        self.notebook.add(self.rec_extract_frame, text='Batch: Extract All in Folder')
        self.notebook.add(self.rec_inject_frame, text='Batch: Repack Folders (In-Place)')
        self.notebook.add(self.flatten_extract_frame, text='Batch: Extract All (Single Folder)')
        self.notebook.add(self.internal_arc_extract_frame, text='Advanced: Partial Extract')
        self.notebook.add(self.internal_arc_inject_frame, text='Advanced: Partial Inject')

        self.notebook.pack(pady=5, padx=10, expand=True, fill='both')

        self.create_list_extract_widgets()
        self.create_list_inject_widgets()
        self.create_recursive_extract_widgets()
        self.create_folder_inject_widgets()
        self.create_recursive_inject_widgets()
        self.create_flatten_extract_widgets()
        self.create_internal_arc_extract_widgets()
        self.create_internal_arc_inject_widgets()

        self.bottom_pane_frame = ttk.Frame(self.main_paned_window, style='TFrame')
        self.main_paned_window.add(self.bottom_pane_frame, weight=1)
        
        self.status_frame = ttk.Frame(self.bottom_pane_frame, style='Status.TFrame')
        self.status_frame.pack(pady=0, padx=10, fill='both', expand=True, side=tk.TOP)
        self.status_frame.grid_rowconfigure(0, weight=1)
        self.status_frame.grid_columnconfigure(0, weight=1)
        
        self.status_text = scrolledtext.ScrolledText(self.status_frame, wrap=tk.WORD, font=self.default_font, bg=WIDGET_BG, fg=TEXT_COLOR, bd=1, relief='sunken', height=10)
        self.status_text.grid(row=0, column=0, sticky='nsew')
        self.status_text.configure(state='disabled')
        
        self.status_text.tag_config(STATUS_ERROR, foreground=STATUS_ERROR_FG)
        self.status_text.tag_config(STATUS_WARN, foreground=STATUS_WARN_FG)
        self.status_text.tag_config(STATUS_SUCCESS, foreground=STATUS_SUCCESS_FG)
        self.status_text.tag_config(STATUS_INFO, foreground=STATUS_INFO_FG)
        self.status_text.tag_config(STATUS_DEBUG, foreground=STATUS_DEBUG_FG)
        
        self.progress_var = tk.DoubleVar()
        self.progress_bar = ttk.Progressbar(self.bottom_pane_frame, orient='horizontal', length=100, mode='determinate', variable=self.progress_var, style='TProgressbar')
        self.progress_bar.pack(pady=10, padx=10, fill='x', side=tk.BOTTOM)
        
        self.current_arc_for_internal_view = None
        self.tree_item_data = {}
        self.current_arc_for_internal_inject_view = None
        self.internal_inject_tree_item_data = {}
        self.files_to_inject_map = {}
        
        if TkinterDnD:
            self.setup_drag_and_drop()
        else:
            self.add_status_message("Drag and drop disabled. Install: 'pip install tkinterdnd2'", STATUS_WARN)
            
        self.check_queue()
        # <--- 2. Added check for startup file
        if startup_file:
            # Small delay to ensure window is rendered before switching tabs
            self.root.after(100, lambda: self.handle_startup_file(startup_file))

    # <--- 3. Added new method to handle the switch
    def handle_startup_file(self, filepath):
        try:
            self.add_status_message(f"Startup file detected: {os.path.basename(filepath)}", STATUS_INFO)
            self.internal_arc_filepath_var.set(filepath)
            self.load_arc_into_treeview(filepath)
            # Select the Advanced Partial Extract tab
            self.notebook.select(self.internal_arc_extract_frame)
        except Exception as e:
            self.add_status_message(f"Error loading startup file: {e}", STATUS_ERROR)

    def configure_styles(self):
        s = self.style
        s.theme_use('clam')
        s.configure('.', background=BG_COLOR, foreground=TEXT_COLOR, font=self.default_font, fieldbackground=WIDGET_BG, troughcolor=BG_COLOR, borderwidth=1)
        s.map('.', foreground=[('disabled', '#aaaaaa')])
        s.configure('TFrame', background=BG_COLOR)
        s.configure('TPanedwindow', background=BG_COLOR)
        s.configure('TLabel', background=BG_COLOR, foreground=TEXT_COLOR, padding=5)
        s.configure('Header.TLabel', font=self.bold_font)
        s.configure('TButton', background=BUTTON_BG, foreground=BUTTON_FG, bordercolor=BUTTON_BORDER, padding=(10, 6))
        s.map('TButton', background=[('active', BUTTON_ACTIVE_BG), ('pressed', BUTTON_PRESSED_BG)])
        s.configure('TEntry', fieldbackground=WIDGET_BG, foreground=INPUT_TEXT_COLOR, insertcolor=INPUT_TEXT_COLOR)
        s.map('TEntry', selectbackground=[('focus', HIGHLIGHT_BG)], selectforeground=[('focus', HIGHLIGHT_TEXT)])
        self.root.option_add('*Listbox*background', WIDGET_BG)
        self.root.option_add('*Listbox*foreground', TEXT_COLOR)
        s.configure('TNotebook', background=BG_COLOR, borderwidth=0)
        s.configure('TNotebook.Tab', background=HEADER_BG, foreground=HEADER_TEXT, padding=[10, 5], font=self.tab_label_font)
        s.map('TNotebook.Tab', background=[('selected', HEADER_ACTIVE_BG)], foreground=[('selected', HEADER_ACTIVE_TEXT)])
        s.configure('TProgressbar', thickness=20, background=STATUS_SUCCESS_FG, troughcolor=WIDGET_BG)
        s.configure('Vertical.TScrollbar', background=BUTTON_BG, troughcolor=WIDGET_BG)
        s.map('Vertical.TScrollbar', background=[('active', BUTTON_ACTIVE_BG)])
        s.configure('Treeview', background=WIDGET_BG, fieldbackground=WIDGET_BG, foreground=TEXT_COLOR)
        s.map('Treeview', background=[('selected', HIGHLIGHT_BG)], foreground=[('selected', HIGHLIGHT_TEXT)])
        s.configure('Treeview.Heading', background=HEADER_BG, foreground=HEADER_TEXT, font=self.bold_font, padding=5)
        s.map('Treeview.Heading', background=[('active', HEADER_ACTIVE_BG)])
        s.configure('TCheckbutton', background=BG_COLOR, foreground=TEXT_COLOR, padding=5)
        s.map('TCheckbutton', foreground=[('active', HIGHLIGHT_TEXT)], background=[('active', BG_COLOR)], indicatorcolor=[('selected', STATUS_SUCCESS_FG), ('!selected', WIDGET_BG)], indicatorrelief=[('pressed', tk.SUNKEN), ('!pressed', tk.FLAT)])
        s.configure('file_replaced', foreground='#FFA500', font=self.bold_font)

    def _create_dir_input(self, parent, label, row, var_name):
        ttk.Label(parent, text=label, style='Header.TLabel').grid(row=row, column=0, sticky='w', padx=5, pady=(10,2))
        frame = ttk.Frame(parent)
        frame.grid(row=row+1, column=0, sticky='w', padx=5, pady=(0,10))
        frame.grid_columnconfigure(0, weight=1)
        v = tk.StringVar()
        setattr(self, var_name, v)
        e = ttk.Entry(frame, textvariable=v, width=60)
        e.grid(row=0, column=0, sticky='ew', padx=(0,10))
        b = ttk.Button(frame, text="Browse...", command=lambda v_arg=v: self._select_directory(v_arg))
        b.grid(row=0, column=1)
        return v
    
    def _create_file_output_input(self, parent, label, row, var_name, original_arc_filepath_var):
        ttk.Label(parent, text=label, style='Header.TLabel').grid(row=row, column=0, sticky='w', padx=5, pady=(10,2))
        frame = ttk.Frame(parent)
        frame.grid(row=row+1, column=0, sticky='ew', padx=5, pady=(0,10))
        frame.grid_columnconfigure(0, weight=1)
        v = tk.StringVar()
        setattr(self, var_name, v)
        e = ttk.Entry(frame, textvariable=v, width=60)
        e.grid(row=0, column=0, sticky='ew', padx=(0,10))
        b = ttk.Button(frame, text="Browse...", command=lambda: self._select_save_file_path(v, original_arc_filepath_var))
        b.grid(row=0, column=1)
        return v
    
    def _select_directory(self, string_var):
        d = filedialog.askdirectory()
        if d: string_var.set(d)
    
    def _select_save_file_path(self, string_var_to_set, original_arc_filepath_var):
        orig_path = original_arc_filepath_var.get()
        init_dir = os.path.dirname(orig_path) if orig_path else os.getcwd()
        init_file = os.path.basename(orig_path) if orig_path else "rebuilt.arc"
        fp = filedialog.asksaveasfilename(initialdir=init_dir, initialfile=init_file, defaultextension=".arc", filetypes=[("ARC files", "*.arc"), ("All files", "*.*")])
        if fp: string_var_to_set.set(fp)

    def create_list_extract_widgets(self):
        frame = self.list_extract_frame
        frame.grid_columnconfigure(0, weight=1)
        frame.grid_rowconfigure(1, weight=1)
        ttk.Label(frame, text="Purpose: Extract the full contents of one or more .arc files.", style='Header.TLabel').grid(row=0, column=0, columnspan=3, sticky='w', pady=(5,0))
        ttk.Label(frame, text="Each ARC will be unpacked into its own subfolder (e.g., 'file.arc' -> 'file_arc/').", style='TLabel').grid(row=1, column=0, columnspan=3, sticky='w', padx=5, pady=(0,5))
        ttk.Label(frame, text="Input ARC Files:", style='Header.TLabel').grid(row=2, column=0, columnspan=3, sticky='w', pady=(10,5))
        lb_frame = ttk.Frame(frame)
        lb_frame.grid(row=3, column=0, columnspan=2, padx=5, pady=5, sticky='nsew')
        lb_frame.grid_rowconfigure(0, weight=1)
        lb_frame.grid_columnconfigure(0, weight=1)
        self.list_extract_listbox = tk.Listbox(lb_frame, width=80, height=10, selectmode=tk.EXTENDED)
        self.list_extract_listbox.grid(row=0, column=0, sticky='nsew')
        sb = ttk.Scrollbar(lb_frame, orient='vertical', command=self.list_extract_listbox.yview)
        sb.grid(row=0, column=1, sticky='nsw')
        self.list_extract_listbox.config(yscrollcommand=sb.set)
        bf = ttk.Frame(frame)
        bf.grid(row=4, column=0, columnspan=2, sticky='ew', padx=5, pady=5)
        ttk.Button(bf, text="Select Files", command=self.select_list_extract_files).pack(side=tk.LEFT, padx=(0,10))
        ttk.Button(bf, text="Clear List", command=lambda: self.list_extract_listbox.delete(0, tk.END)).pack(side=tk.LEFT)
        self.btn_extract_list = ttk.Button(frame, text="Start Extraction", command=self.start_list_extraction)
        self.btn_extract_list.grid(row=5, column=0, columnspan=3, pady=(10,10))
        frame.grid_rowconfigure(3, weight=1)

    def create_list_inject_widgets(self):
        frame = self.list_inject_frame
        frame.grid_columnconfigure(0, weight=1)
        frame.grid_rowconfigure(3, weight=1)
        ttk.Label(frame, text="Purpose: Create a brand new .arc file from a folder of assets.", style='Header.TLabel').grid(row=0, column=0, columnspan=3, sticky='w', pady=(5,0))
        ttk.Label(frame, text="This uses default settings and is NOT recommended for modding existing ARCs. Use Tab 2 instead.", style='TLabel').grid(row=1, column=0, columnspan=3, sticky='w', padx=5, pady=(0,5))
        ttk.Label(frame, text="Input Source Folders:", style='Header.TLabel').grid(row=2, column=0, columnspan=3, sticky='w', pady=(10,5))
        lb_frame = ttk.Frame(frame)
        lb_frame.grid(row=3, column=0, columnspan=2, padx=5, pady=5, sticky='nsew')
        lb_frame.grid_rowconfigure(0, weight=1)
        lb_frame.grid_columnconfigure(0, weight=1)
        self.list_inject_listbox = tk.Listbox(lb_frame, width=80, height=10, selectmode=tk.EXTENDED)
        self.list_inject_listbox.grid(row=0, column=0, sticky='nsew')
        sb = ttk.Scrollbar(lb_frame, orient='vertical', command=self.list_inject_listbox.yview)
        sb.grid(row=0, column=1, sticky='nsw')
        self.list_inject_listbox.config(yscrollcommand=sb.set)
        bf = ttk.Frame(frame)
        bf.grid(row=4, column=0, columnspan=2, sticky='ew', padx=5, pady=5)
        ttk.Button(bf, text="Add Folder", command=self.select_list_inject_folders).pack(side=tk.LEFT, padx=(0,10))
        ttk.Button(bf, text="Clear List", command=lambda: self.list_inject_listbox.delete(0, tk.END)).pack(side=tk.LEFT)
        self._create_dir_input(frame, "Output Directory for New ARCs:", 5, "list_inject_output_var")
        self.btn_inject_list = ttk.Button(frame, text="Build New ARC(s)", command=self.start_list_injection)
        self.btn_inject_list.grid(row=7, column=0, columnspan=3, pady=(10,10))

    def create_recursive_extract_widgets(self):
        frame = self.rec_extract_frame
        frame.grid_columnconfigure(0, weight=1)
        ttk.Label(frame, text="Purpose: Find and extract all .arc files within a directory and its subdirectories.", style='Header.TLabel').grid(row=0, column=0, sticky='w', pady=(5,5))
        self._create_dir_input(frame, "Source Directory to Scan (Recursive):", 1, "rec_extract_source_var")
        ttk.Label(frame, text="Output: For each ARC found, a corresponding '_arc' folder will be created next to it.", style='TLabel').grid(row=3, column=0, sticky='w', padx=5, pady=(10,5))
        self.btn_rec_extract = ttk.Button(frame, text="Start Recursive Batch Extraction", command=self.start_recursive_extraction)
        self.btn_rec_extract.grid(row=4, column=0, pady=(10,10))

    def create_folder_inject_widgets(self):
        frame = self.folder_inject_frame
        frame.grid_columnconfigure(0, weight=1)
        ttk.Label(frame, text="Purpose: Rebuild an ARC from its extracted folder to ensure a perfect, 1:1 copy.", style='Header.TLabel').grid(row=0, column=0, sticky='w', pady=(5,0))
        ttk.Label(frame, text="This is the recommended method for modding. It requires the original .arc file to be next to its folder.", style='TLabel').grid(row=1, column=0, sticky='w', padx=5, pady=(0,5))
        info_text = ("This tool will find all matching pairs (e.g., 'resident.arc' and 'resident_arc') in the selected directory.\nIt will rebuild each ARC using the contents of its folder, perfectly preserving all original parameters.")
        ttk.Label(frame, text=info_text, style='TLabel', justify=tk.LEFT).grid(row=2, column=0, sticky='w', padx=5, pady=(10,5))
        self.move_to_original_data_var = tk.BooleanVar(value=True)
        cb = ttk.Checkbutton(frame, text="On success, move original .arc backup and source _arc folder into a new 'original_data' subfolder.", variable=self.move_to_original_data_var, style='TCheckbutton')
        cb.grid(row=3, column=0, sticky='w', padx=5, pady=(10,0))
        self.delete_original_data_var = tk.BooleanVar(value=False)
        cb_del = ttk.Checkbutton(frame, text="On success, DELETE the 'original_data' subfolder (irreversible).", variable=self.delete_original_data_var, style='TCheckbutton')
        cb_del.grid(row=4, column=0, sticky='w', padx=5, pady=(5,0))
        self._create_dir_input(frame, "Select Directory Containing Both '.arc' and '_arc' Folders:", 5, "folder_inject_source_dir_var")
        self.btn_inject_folder = ttk.Button(frame, text="Start In-Place Rebuild", command=self.start_folder_injection)
        self.btn_inject_folder.grid(row=7, column=0, pady=(10,10))

    def create_recursive_inject_widgets(self):
        frame = self.rec_inject_frame
        frame.grid_columnconfigure(0, weight=1)
        ttk.Label(frame, text="Purpose: Recursively find and rebuild all ARCs from their extracted folders.", style='Header.TLabel').grid(row=0, column=0, sticky='w', pady=(5,0))
        info_text = ("This tool scans a directory and its subdirectories for matching pairs (e.g., 'resident.arc' and 'resident_arc').\nIt rebuilds each ARC using the high-fidelity 'in-place' method.")
        ttk.Label(frame, text=info_text, style='TLabel', justify=tk.LEFT).grid(row=1, column=0, sticky='w', padx=5, pady=(5,5))
        self.rec_inject_move_to_original_data_var = tk.BooleanVar(value=True)
        cb_move = ttk.Checkbutton(frame, text="On success, move original .arc backups and source _arc folders into 'original_data' subfolders.", variable=self.rec_inject_move_to_original_data_var, style='TCheckbutton')
        cb_move.grid(row=2, column=0, sticky='w', padx=5, pady=(10,0))
        self.rec_inject_delete_original_data_var = tk.BooleanVar(value=False)
        cb_del = ttk.Checkbutton(frame, text="On success, DELETE all 'original_data' subfolders (irreversible).", variable=self.rec_inject_delete_original_data_var, style='TCheckbutton')
        cb_del.grid(row=3, column=0, sticky='w', padx=5, pady=(5,0))
        self._create_dir_input(frame, "Select Root Directory to Scan for '.arc' and '_arc' Pairs:", 4, "rec_inject_source_dir_var")
        self.btn_rec_inject = ttk.Button(frame, text="Start Batch In-Place Rebuild", command=self.start_recursive_folder_injection)
        self.btn_rec_inject.grid(row=5, column=0, pady=(10,10))

    def create_flatten_extract_widgets(self):
        frame = self.flatten_extract_frame
        frame.grid_columnconfigure(0, weight=1)
        self._create_dir_input(frame, "Source ARC Directory (Recursive):", 0, "flatten_extract_source_var")
        self._create_dir_input(frame, "Output Directory (for all flattened files):", 2, "flatten_extract_output_var")
        ttk.Label(frame, text="Extracts all files from all ARCs into a single output directory.\nFilenames prefixed with ARC name (e.g., arc1_image.tex).", style='TLabel', justify=tk.LEFT).grid(row=4, column=0, sticky='w', padx=5, pady=(10,5))
        self.btn_flat_extract = ttk.Button(frame, text="Start Flattened Extraction", command=self.start_flatten_extraction)
        self.btn_flat_extract.grid(row=5, column=0, pady=(10,10))
    
    def create_internal_arc_extract_widgets(self):
        frame = self.internal_arc_extract_frame
        frame.grid_columnconfigure(0, weight=1)
        frame.grid_rowconfigure(1, weight=1)
        input_arc_frame = ttk.Frame(frame)
        input_arc_frame.grid(row=0, column=0, sticky='ew', padx=5, pady=(0,2))
        input_arc_frame.grid_columnconfigure(0, weight=1)
        ttk.Label(input_arc_frame, text="Select ARC File to Preview:", style='Header.TLabel').pack(side=tk.LEFT, anchor='w')
        self.internal_arc_filepath_var = tk.StringVar()
        ttk.Entry(input_arc_frame, textvariable=self.internal_arc_filepath_var, width=90).pack(side=tk.LEFT, expand=True, fill='x', padx=10)
        ttk.Button(input_arc_frame, text="Browse ARC...", command=self.select_internal_arc_file).pack(side=tk.LEFT)
        tree_frame = ttk.Frame(frame)
        tree_frame.grid(row=1, column=0, sticky='nsew', pady=(2,0))
        tree_frame.grid_rowconfigure(0, minsize=250, weight=1)
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
        output_frame = ttk.Frame(frame)
        output_frame.grid(row=2, column=0, sticky='ews', pady=(2,0))
        self._create_dir_input(output_frame, "Output Directory for Selected Items:", 0, "internal_extract_output_var")
        self.btn_internal_extract = ttk.Button(frame, text="Extract Selected Items", command=self.start_internal_arc_extraction)
        self.btn_internal_extract.grid(row=3, column=0, pady=(10,10), padx=5)

    def create_internal_arc_inject_widgets(self):
        frame = self.internal_arc_inject_frame
        frame.grid_columnconfigure(0, weight=1)
        frame.grid_rowconfigure(1, weight=1)
        input_arc_frame = ttk.Frame(frame)
        input_arc_frame.grid(row=0, column=0, sticky='ew', padx=5, pady=(0,2))
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
        buttons_frame = ttk.Frame(tree_and_buttons_frame)
        buttons_frame.grid(row=0, column=2, sticky='n', padx=(10,0))
        self.replace_file_button = ttk.Button(buttons_frame, text="Replace Selected File...", command=self.replace_selected_internal_file, state=tk.DISABLED)
        self.replace_file_button.pack(pady=(5,5), fill='x')
        self.clear_injection_map_button = ttk.Button(buttons_frame, text="Clear Replacements", command=self.clear_internal_inject_map)
        self.clear_injection_map_button.pack(pady=(5,5), fill='x')
        output_frame = ttk.Frame(frame)
        output_frame.grid(row=2, column=0, sticky='ews', pady=(2,0))
        self._create_file_output_input(output_frame, "Output Rebuilt ARC File (New Name/Location):", 0, "internal_inject_output_var", self.internal_inject_filepath_var)
        info_text = "Select an existing ARC, then pick files to replace. Retains original ARC structure and metadata."
        ttk.Label(frame, text=info_text, style='TLabel', justify=tk.LEFT).grid(row=3, column=0, sticky='w', padx=5, pady=(10,5))
        self.btn_internal_inject = ttk.Button(frame, text="Start Injection", command=self.start_internal_arc_injection)
        self.btn_internal_inject.grid(row=4, column=0, pady=(10,10), padx=5)

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
            self._run_task(run_batch_parallel, args_tuple=(_flatten_extract_worker, [dropped_arc_file_path], output_dir))
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
        files = filedialog.askopenfilenames(title="Select ARC Files", filetypes=[("MT ARC","*.arc"),("All Files","*.*")])
        if files:
            current_items = set(self.list_extract_listbox.get(0, tk.END))
            new_files_added = 0
            for f in files:
                if f not in current_items:
                    self.list_extract_listbox.insert(tk.END, f)
                    new_files_added += 1
            if new_files_added:
                self.add_status_message(f"Added {new_files_added} file(s) to extraction list.", STATUS_INFO)

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
        except ARCCSkippedError:
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
        except ARCCSkippedError:
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
        if not item_iid: return
        element_clicked = self.internal_arc_tree.identify_element(event.x, event.y)
        element_str_lower = str(element_clicked).lower()
        if "indicator" in element_str_lower or "expander" in element_str_lower or "arrow" in element_str_lower:
            return
        if item_iid not in self.tree_item_data: return
        current_data = self.tree_item_data[item_iid]
        new_state = not current_data['checked_state']
        self._set_tree_item_checked_state(item_iid, new_state, recursive=True, update_parent=True)

    def _set_tree_item_checked_state(self, item_iid, checked: bool, recursive: bool, update_parent: bool):
        if item_iid not in self.tree_item_data: return
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
        if not parent_iid or parent_iid not in self.tree_item_data: return
        children_iids = self.internal_arc_tree.get_children(parent_iid)
        parent_data = self.tree_item_data[parent_iid]
        current_parent_checked_state = parent_data['checked_state']
        if not children_iids: return
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
        if current_parent_checked_state != new_parent_checked_state:
            self._set_tree_item_checked_state(parent_iid, new_parent_checked_state, recursive=False, update_parent=True)

    def update_debug_buttons_text(self):
        global DEBUG_PER_FILE, DEBUG_VERIFY_HASH
        self.debug_per_file_button.config(text=f"Per-File Debug: {'ON' if DEBUG_PER_FILE else 'OFF'}")
        self.debug_verify_hash_button.config(text=f"Verify Hash: {'ON' if DEBUG_VERIFY_HASH else 'OFF'}")

    def toggle_debug_per_file(self):
        global DEBUG_PER_FILE
        DEBUG_PER_FILE = not DEBUG_PER_FILE
        self.update_debug_buttons_text()
        self.add_status_message(f"Per-file debug logging set to: {'ON' if DEBUG_PER_FILE else 'OFF'}", STATUS_INFO)

    def toggle_debug_verify_hash(self):
        global DEBUG_VERIFY_HASH
        DEBUG_VERIFY_HASH = not DEBUG_VERIFY_HASH
        self.update_debug_buttons_text()
        self.add_status_message(f"Repack hash verification set to: {'ON' if DEBUG_VERIFY_HASH else 'OFF'}", STATUS_INFO)

    def _run_task(self, target_func, args_tuple=(), kwargs_dict=None, finished_callback=None):
        final_kwargs = {}
        if kwargs_dict:
            final_kwargs.update(kwargs_dict)
        final_kwargs['progress_callback'] = self.update_progress
        final_kwargs['status_callback'] = self.queue_status
        final_kwargs['key1'] = None
        final_kwargs['key2'] = None
        self.progress_var.set(0)
        task_name = target_func.__name__.replace('_', ' ').title()
        self.add_status_message(f"Starting {task_name} task...", STATUS_INFO)
        
        def wrapper():
            target_func(*args_tuple, **final_kwargs)
            if finished_callback:
                # Schedule callback on main thread
                self.root.after(0, finished_callback)

        thread = threading.Thread(target=wrapper, daemon=True)
        thread.start()

    def _run_repack_and_cleanup_task(self, worker_func, item_list, output_dir, worker_kwargs_dict, delete_originals_flag, progress_callback, status_callback, key1, key2):
        results = run_batch_parallel(worker_func, item_list, output_dir, progress_callback, status_callback, key1, key2, **worker_kwargs_dict)
        all_successful = all(res[1] for res in results) if results else False
        move_flag = worker_kwargs_dict.get('move_originals', [False]*len(item_list))[0]
        if all_successful and delete_originals_flag and move_flag:
            status_callback("All repacks successful. Deleting 'original_data' folders...", STATUS_INFO)
            deleted_count = 0
            for source_folder_str in item_list:
                try:
                    source_folder_path = pathlib.Path(source_folder_str)
                    original_data_dir = source_folder_path.parent / "original_data"
                    if original_data_dir.is_dir():
                        shutil.rmtree(original_data_dir)
                        status_callback(f"Deleted '{original_data_dir}'.", STATUS_DEBUG)
                        deleted_count += 1
                except Exception as e:
                    status_callback(f"Error during cleanup of '{original_data_dir}': {e}", STATUS_ERROR)
            status_callback(f"Cleanup complete. Deleted {deleted_count} 'original_data' folder(s).", STATUS_SUCCESS)
        elif not all_successful and delete_originals_flag:
            status_callback("One or more repacks failed. Skipping deletion of 'original_data' folders.", STATUS_WARN)
        elif not move_flag and delete_originals_flag:
            status_callback("Cleanup skipped: 'Move originals' option was not enabled.", STATUS_INFO)

    def start_list_extraction(self):
        items = self.list_extract_listbox.get(0, tk.END)
        if not items: 
            messagebox.showwarning("Input Missing", "Please select ARC files.")
            return
        self.btn_extract_list.config(state='disabled')
        self._run_task(run_batch_parallel, (_list_extract_worker, items, None), finished_callback=lambda: self.btn_extract_list.config(state='normal'))

    def start_list_injection(self):
        items = self.list_inject_listbox.get(0, tk.END)
        output_dir = self.list_inject_output_var.get()
        if not items: 
            messagebox.showwarning("Input Missing", "Please add source folders.")
            return
        if not output_dir: 
            messagebox.showwarning("Output Missing", "Please select an output directory.")
            return
        self.btn_inject_list.config(state='disabled')
        self._run_task(run_batch_parallel, (_from_scratch_rebuild_worker, items, output_dir), finished_callback=lambda: self.btn_inject_list.config(state='normal'))

    def start_folder_injection(self):
        src_dir = self.folder_inject_source_dir_var.get()
        if not src_dir: 
            messagebox.showwarning("Input Missing", "Please select the source directory.")
            return
        self.btn_inject_folder.config(state='disabled')

        # Threaded Scanning
        def _scan_and_run():
            try:
                self.queue_status("Scanning for compatible folders...", STATUS_INFO)
                source_path = pathlib.Path(src_dir)
                task_folders = [
                    str(f) for f in source_path.glob('*_arc') 
                    if f.is_dir() and "original_data" not in f.parts and (source_path / (f.name[:-4] + ".arc")).is_file()
                ]
                if not task_folders:
                    self.queue_status("No valid folder/*.arc pairs found.", STATUS_WARN)
                    self.update_progress(100)
                    self.root.after(0, lambda: self.btn_inject_folder.config(state='normal'))
                    return

                self.queue_status(f"Found {len(task_folders)} folders. Starting rebuild...", STATUS_INFO)
                
                move_originals_flag = self.move_to_original_data_var.get()
                delete_originals_flag = self.delete_original_data_var.get()
                kwargs_for_worker = {'move_originals': [move_originals_flag] * len(task_folders)}
                args_for_task = (_in_place_rebuild_worker, task_folders, None, kwargs_for_worker, delete_originals_flag)
                
                self._run_task(self._run_repack_and_cleanup_task, args_tuple=args_for_task, finished_callback=lambda: self.btn_inject_folder.config(state='normal'))
            except Exception as e:
                self.queue_status(f"Scan Error: {e}", STATUS_ERROR)
                self.root.after(0, lambda: self.btn_inject_folder.config(state='normal'))

        threading.Thread(target=_scan_and_run, daemon=True).start()

    def start_recursive_folder_injection(self):
        src_dir = self.rec_inject_source_dir_var.get()
        if not src_dir: 
            messagebox.showwarning("Input Missing", "Please select the source directory.")
            return
        self.btn_rec_inject.config(state='disabled')

        # Threaded Scanning
        def _scan_and_run():
            try:
                self.queue_status("Recursively scanning for compatible folders...", STATUS_INFO)
                source_path = pathlib.Path(src_dir)
                task_folders = [
                    str(f) for f in source_path.rglob('*_arc') 
                    if f.is_dir() and "original_data" not in f.parts and (f.parent / (f.name[:-4] + ".arc")).is_file()
                ]
                if not task_folders:
                    self.queue_status("No valid folder/*.arc pairs found recursively.", STATUS_WARN)
                    self.update_progress(100)
                    self.root.after(0, lambda: self.btn_rec_inject.config(state='normal'))
                    return
                
                self.queue_status(f"Found {len(task_folders)} folders. Starting batch rebuild...", STATUS_INFO)
                
                move_originals_flag = self.rec_inject_move_to_original_data_var.get()
                delete_originals_flag = self.rec_inject_delete_original_data_var.get()
                kwargs_for_worker = {'move_originals': [move_originals_flag] * len(task_folders)}
                args_for_task = (_in_place_rebuild_worker, task_folders, None, kwargs_for_worker, delete_originals_flag)
                
                self._run_task(self._run_repack_and_cleanup_task, args_tuple=args_for_task, finished_callback=lambda: self.btn_rec_inject.config(state='normal'))
            except Exception as e:
                self.queue_status(f"Scan Error: {e}", STATUS_ERROR)
                self.root.after(0, lambda: self.btn_rec_inject.config(state='normal'))

        threading.Thread(target=_scan_and_run, daemon=True).start()

    def start_recursive_extraction(self):
        src = self.rec_extract_source_var.get()
        if not src: 
            messagebox.showwarning("Input Missing", "Please select a source directory.")
            return
        self.btn_rec_extract.config(state='disabled')
        self._run_task(recursive_batch_extract, (src, None), finished_callback=lambda: self.btn_rec_extract.config(state='normal'))

    def start_flatten_extraction(self):
        src_dir = self.flatten_extract_source_var.get()
        out_dir = self.flatten_extract_output_var.get()
        if not src_dir or not out_dir: 
            messagebox.showwarning("Input Missing", "Please select source and output directories.")
            return
        self.btn_flat_extract.config(state='disabled')
        self._run_task(recursive_flatten_extract, (src_dir, out_dir), finished_callback=lambda: self.btn_flat_extract.config(state='normal'))

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
        self.btn_internal_extract.config(state='disabled')
        self._run_task(self._perform_internal_arc_extraction_thread, args_tuple=(final_extraction_list, self.internal_arc_filepath_var.get()), finished_callback=lambda: self.btn_internal_extract.config(state='normal'))

    def _perform_internal_arc_extraction_thread(self, items_to_extract, arc_filepath_str, progress_callback, status_callback, key1, key2):
        arc_for_extraction = None
        try:
            if not self.current_arc_for_internal_view or self.current_arc_for_internal_view._raw_file_path != arc_filepath_str:
                status_callback(f"Re-opening ARC '{os.path.basename(arc_filepath_str)}' for extraction...", STATUS_DEBUG)
                arc_for_extraction = MTArc()
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
                    with open(get_safe_path_str(target_disk_path), 'wb') as out_f:
                        out_f.write(file_data)
                    processed_count += 1
                except Exception as e:
                    error_count += 1
                    status_callback(f"Error extracting '{file_info['full_filename']}' to '{target_disk_path}': {e}", STATUS_ERROR)
                    traceback.print_exc(file=sys.stderr)
                progress_callback((i + 1) / total_items * 100)
            final_msg = f"Internal ARC extraction complete. Extracted: {processed_count}, Errors: {error_count}."
            final_level = STATUS_SUCCESS if error_count == 0 and processed_count > 0 else (STATUS_WARN if processed_count > 0 else STATUS_ERROR)
            status_callback(final_msg, final_level)
        except ARCCSkippedError:
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
                "A timestamped backup will be created in an 'original_arc_backups' subfolder.\n\n"
                "Do you wish to proceed and overwrite the original file?"
            )
            if not response:
                self.add_status_message("Injection cancelled by user to prevent overwrite.", STATUS_INFO)
                return
            try:
                original_p = pathlib.Path(original_arc_path)
                backup_dir = original_p.parent / "original_arc_backups"
                backup_dir.mkdir(parents=True, exist_ok=True)
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                backup_path = backup_dir / f"{original_p.stem}_{timestamp}{original_p.suffix}"
                shutil.copy2(original_p, backup_path)
                self.add_status_message(f"Created backup of original file at '{backup_path}'.", STATUS_INFO)
            except Exception as e:
                messagebox.showerror("Backup Failed", f"Could not create a backup of the original ARC file.\n\nError: {e}\n\nAborting operation.")
                self.add_status_message(f"Backup failed for '{original_arc_path}': {e}", STATUS_ERROR)
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
        self.btn_internal_inject.config(state='disabled')
        self._run_task(self._perform_internal_arc_injection_thread, args_tuple=(original_arc_path, self.files_to_inject_map.copy(), output_arc_path), finished_callback=lambda: self.btn_internal_inject.config(state='normal'))

    def _perform_internal_arc_injection_thread(self, original_arc_filepath: str, files_to_inject_map: dict, output_arc_path: str, progress_callback, status_callback, key1, key2):
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
                target_entry_has_extended_names=arc_loader_for_read.entry_has_extended_names
            )
            status_callback(f"Successfully rebuilt ARC to '{os.path.basename(output_arc_path)}'.", STATUS_SUCCESS)
        except ARCCSkippedError:
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

    def update_progress(self, v):
        try:
            self.queue.put({'type': 'progress', 'value': max(0.0, min(100.0, float(v)))})
        except Exception as e:
            print(f"Error in update_progress: {e}", file=sys.stderr)

    def queue_status(self, m, l=STATUS_INFO):
        try:
            self.queue.put({'type': 'status', 'msg': m, 'level': l})
        except Exception as e:
            print(f"Error in queue_status putting message '{m}': {e}", file=sys.stderr)

    def check_queue(self):
        try:
            while True:
                try:
                    item = self.queue.get_nowait()
                    if item.get('type') == 'progress':
                        self.progress_var.set(item.get('value', 0.0))
                    elif item.get('type') == 'status':
                        msg_content = item.get('msg', '')
                        msg_level = item.get('level', STATUS_INFO)
                        self.add_status_message(msg_content, msg_level)
                except queue.Empty:
                    break
        except Exception as e:
            print(f"Error in GUI event loop: {e}", file=sys.stderr)
        finally:
            self.root.after(100, self.check_queue)

    def add_status_message(self, m, l=STATUS_INFO):
        try:
            if not isinstance(m, str): m = str(m)
            self.status_text.configure(state='normal')
            timestamp = datetime.now().strftime("[%H:%M:%S]")
            self.status_text.insert(tk.END, f"{timestamp} {m}\n", (l,))
            self.status_text.configure(state='disabled')
            self.status_text.see(tk.END)
        except Exception as e:
            print(f"[{datetime.now().strftime('%H:%M:%S')}] Error updating status GUI: {e}\nStatus message ({l}): {m}", file=sys.stderr)
            traceback.print_exc(file=sys.stderr)

    def show_help(self):
        help_text_content = """
        SaladSoftware MT Framework ARC Tool - Help
        ================================================

        This tool extracts and rebuilds MT Framework .arc files. The tabs are numbered 
        to guide you through a standard modding workflow.

        --- Standard Workflow ---

        Tab 1: Extract from ARC(s)
        --------------------------
        - Purpose: To unpack an original game archive (.arc) into a folder.
        - How: Select one or more .arc files. For each file (e.g., 'resident.arc'),
        a corresponding folder ('resident_arc') will be created next to it,
        containing all the extracted files.
        - This is the first step for creating a mod.

        Tab 2: Repack Folder (In-Place)
        -------------------------------
        - Purpose: To rebuild an edited folder back into a byte-perfect .arc file.
        - THIS IS THE RECOMMENDED METHOD FOR REPACKING MODS.
        - How: Select the main directory that contains both your original .arc file
        (e.g., 'resident.arc') and the folder you edited (e.g., 'resident_arc').
        The tool will automatically find these pairs.
        - It uses the original .arc to copy all parameters and unchanged files,
        ensuring the new ARC is as close to the original as possible.
        - Original .arc files are safely backed up. By default, the backup and the 
        source folder are moved into an 'original_data' subfolder to keep your
        workspace clean.

        --- Other Tools ---

        Tab 3: Build New ARC from Folder
        --------------------------------
        - Purpose: To create a completely new .arc file from a folder of assets.
        - WARNING: This is for advanced users creating an ARC from scratch. It uses
        default settings and will likely not match an existing game's format.
        For editing existing game files, always use Tab 2.

        Batch: Extract All in Folder
        ----------------------------
        - Purpose: A convenience tool to run the 'Extract' process on every single
        .arc file found inside a folder and all of its subfolders.

        Batch: Extract All (Single Folder)
        ----------------------------------
        - Purpose: To extract the contents of many .arc files into one single folder.
        - The internal folder structure of the ARCs is discarded ("flattened").
        - Filenames are prefixed with their source ARC name to avoid conflicts
        (e.g., 'resident_arc_font.tex'). Useful for quickly finding a specific file.

        Advanced: Partial Extract / Inject
        ----------------------------------
        - These tabs allow you to view the contents of an ARC and extract or replace
        individual files without unpacking the entire archive. This is useful for
        small, quick edits.
        """
        messagebox.showinfo("Help - SaladSoftware ARC Tool", help_text_content)

# --- CLI Support ---
def cli_status_callback(message, level=STATUS_INFO):
    timestamp = datetime.now().strftime("[%H:%M:%S]")
    print(f"{timestamp} [{level.upper()}] {message}", file=sys.stderr if level in [STATUS_ERROR, STATUS_WARN] else sys.stdout)

def cli_progress_callback(value):
    sys.stdout.write(f"\rProgress: {int(value):3}%")
    sys.stdout.flush()
    if value >= 100:
        sys.stdout.write("\n")
        sys.stdout.flush()

def handle_cli_extract(args):
    cli_status_callback(f"Starting List Extraction for: {', '.join(args.arc_files)}", STATUS_INFO)
    run_batch_parallel(_list_extract_worker, args.arc_files, None, cli_progress_callback, cli_status_callback, args.key1, args.key2)

def handle_cli_inject(args):
    cli_status_callback(f"Starting List Injection for folders: {', '.join(args.folders)}", STATUS_INFO)
    if not args.output_dir:
        cli_status_callback("Error: --output-dir is required for inject command.", STATUS_ERROR)
        return
    run_batch_parallel(_from_scratch_rebuild_worker, args.folders, args.output_dir, cli_progress_callback, cli_status_callback, args.key1, args.key2)

def handle_cli_extract_recursive(args):
    cli_status_callback(f"Starting Recursive Extraction from: {args.source_dir}", STATUS_INFO)
    recursive_batch_extract(args.source_dir, None, cli_progress_callback, cli_status_callback, args.key1, args.key2)

def handle_cli_inject_recursive(args):
    cli_status_callback(f"Starting Recursive In-Place Injection in: {args.source_dir}", STATUS_INFO)
    source_path = pathlib.Path(args.source_dir)
    task_folders = [
        str(f) for f in source_path.rglob('*_arc') 
        if f.is_dir() and "original_data" not in f.parts and (source_path / (f.name[:-4] + ".arc")).is_file()
    ]
    if not task_folders:
        cli_status_callback("No valid folder/*.arc pairs found to process for in-place rebuild.", STATUS_WARN)
        return
    kwargs = {'move_originals': [args.move_originals] * len(task_folders)}
    run_batch_parallel(_in_place_rebuild_worker, task_folders, None, cli_progress_callback, cli_status_callback, args.key1, args.key2, **kwargs)

def handle_cli_extract_flat(args):
    cli_status_callback(f"Starting Flattened Extraction from '{args.source_path}' to '{args.output_dir}'", STATUS_INFO)
    source_p = pathlib.Path(args.source_path)
    if not args.output_dir:
        cli_status_callback("Error: --output-dir is required for extract-flat command.", STATUS_ERROR)
        return
    if source_p.is_file() and source_p.suffix.lower() == '.arc':
        run_batch_parallel(_flatten_extract_worker, [str(source_p)], args.output_dir, cli_progress_callback, cli_status_callback, args.key1, args.key2)
    elif source_p.is_dir():
        recursive_flatten_extract(str(source_p), args.output_dir, cli_progress_callback, cli_status_callback, args.key1, args.key2)
    else:
        cli_status_callback(f"Error: Source path '{args.source_path}' is not a valid ARC file or directory.", STATUS_ERROR)

def install_context_menu():
    """Helper to add 'Extract ARC' and 'Rebuild ARC' to Windows right-click menu."""
    if sys.platform != 'win32':
        print("Context menu installation is only supported on Windows.")
        return

    try:
        import winreg
    except ImportError:
        print("winreg module not found.")
        return

    exe_path = os.path.abspath(sys.argv[0])
    # If running as python script, use python.exe
    if not exe_path.lower().endswith('.exe'):
        exe_path = f'"{sys.executable}" "{exe_path}"'
    else:
        exe_path = f'"{exe_path}"'

    def set_reg_key(key_path, value):
        try:
            key = winreg.CreateKey(winreg.HKEY_CURRENT_USER, key_path)
            winreg.SetValue(key, None, winreg.REG_SZ, value)
            winreg.CloseKey(key)
        except Exception as e:
            print(f"Error writing registry key {key_path}: {e}")

    print("Installing Context Menu items...")
    
    # 1. .arc files -> Extract
    base = r"Software\Classes\.arc"
    set_reg_key(base, "SaladSoftwareARC")
    set_reg_key(r"Software\Classes\SaladSoftwareARC\shell\open\command", f'{exe_path} "%1"') 
    set_reg_key(r"Software\Classes\SaladSoftwareARC\shell\extract", "Extract ARC (SaladSoftware)")
    set_reg_key(r"Software\Classes\SaladSoftwareARC\shell\extract\command", f'{exe_path} extract "%1"')
    
    # 2. Folders -> Rebuild (Inject)
    set_reg_key(r"Software\Classes\Directory\shell\SaladRebuild", "Rebuild ARC (SaladSoftware)")
    set_reg_key(r"Software\Classes\Directory\shell\SaladRebuild\command", f'{exe_path} inject "%1" --output-dir "%1_rebuilt"')

    print("Done. You should now see 'Extract ARC' when right-clicking .arc files,")
    print("and 'Rebuild ARC' when right-clicking folders.")
    input("Press Enter to exit...")

def _keep_window_open_on_error(func, args):
    """Runs the CLI command and keeps window open if an error occurs or operation finishes."""
    try:
        func(args)
    except Exception as e:
        print(f"\nERROR: {e}")
        traceback.print_exc()
    finally:
        if sys.stdout and sys.stdout.isatty():
            input("\nProcess finished. Press Enter to exit...")

if __name__ == "__main__":
    # 1. SMART ARG PARSING (Supports D&D and Double-Click)
    known_commands = ['extract', 'inject', 'extract-recursive', 'inject-recursive', 'extract-flat', 'install-menu']
    
    gui_startup_file = None # Flag to track if we should skip CLI and go to GUI

    # Check arguments before passing to argparse
    if len(sys.argv) > 1 and sys.argv[1] not in known_commands and not sys.argv[1].startswith('-'):
        target = pathlib.Path(sys.argv[1])
        inserted_cmd = None
        
        if target.is_file() and target.suffix.lower() == '.arc':
            # If a single .arc file is passed, we assume the user wants to VIEW it in the GUI
            # rather than automatically extracting it via CLI.
            gui_startup_file = str(target)
        elif target.is_dir():
            if target.name.endswith('_arc'):
                inserted_cmd = 'inject'
            else:
                inserted_cmd = 'extract-recursive'
        
        if inserted_cmd:
            print(f"Auto-detected mode: {inserted_cmd}")
            sys.argv.insert(1, inserted_cmd)
            
            if inserted_cmd == 'inject' and '--output-dir' not in sys.argv and '-o' not in sys.argv:
                default_out = str(target.parent)
                sys.argv.extend(['--output-dir', default_out])

    load_extension_map(resource_path(EXTENSION_MAP_FILE), resource_path(GAME_SPECIFIC_HASH_FILE))

    # If we detected a file for GUI opening, skip argparse CLI logic
    if gui_startup_file:
        if TkinterDnD: 
            root = TkinterDnD.Tk()
        else: 
            root = tk.Tk()
        # Pass the file to the App
        app = ArcToolApp(root, startup_file=gui_startup_file)
        root.mainloop()
    else:
        # 2. DEFINE PARSER (Standard CLI Logic)
        parser = argparse.ArgumentParser(description=f"Handburger's SaladSoftware MT Arc Tool - Version {VERSION}", formatter_class=argparse.RawTextHelpFormatter)
        parser.add_argument('--version', action='version', version=f'%(prog)s {VERSION}')
        subparsers = parser.add_subparsers(dest="command", title="Commands", help="Run a command with -h for more details")
        
        key_args = [(['-k1', '--key1'], {'type': str, 'default': None, 'help': 'Blowfish Key Part 1 (unused).'}), 
                    (['-k2', '--key2'], {'type': str, 'default': None, 'help': 'Blowfish Key Part 2 (unused).'})]
        
        p_extract = subparsers.add_parser('extract', help='Extract one or more ARC files.')
        p_extract.add_argument('arc_files', metavar='ARC_FILE', type=str, nargs='+', help='Path(s) to ARC file(s).')
        for a, kw in key_args: p_extract.add_argument(*a, **kw)
        p_extract.set_defaults(func=handle_cli_extract)
        
        p_inject = subparsers.add_parser('inject', help='Rebuild ARC files from folders.')
        p_inject.add_argument('folders', metavar='FOLDER', type=str, nargs='+', help='Path(s) to source folder(s).')
        p_inject.add_argument('--output-dir', '-o', type=str, required=True, help='Directory for rebuilt ARCs.')
        for a, kw in key_args: p_inject.add_argument(*a, **kw)
        p_inject.set_defaults(func=handle_cli_inject)
        
        p_extract_rec = subparsers.add_parser('extract-recursive', help='Recursively extract ARCs.')
        p_extract_rec.add_argument('source_dir', type=str, help='Root directory to scan.')
        for a, kw in key_args: p_extract_rec.add_argument(*a, **kw)
        p_extract_rec.set_defaults(func=handle_cli_extract_recursive)
        
        p_inject_rec = subparsers.add_parser('inject-recursive', help='Recursively rebuild ARCs in-place.')
        p_inject_rec.add_argument('source_dir', type=str, help='Root directory with ARCs and *_arc folders.')
        p_inject_rec.add_argument('--move-originals', action='store_true', help='Move original ARC backup to "original_data".')
        for a, kw in key_args: p_inject_rec.add_argument(*a, **kw)
        p_inject_rec.set_defaults(func=handle_cli_inject_recursive)
        
        p_extract_flat = subparsers.add_parser('extract-flat', help='Extract all files from ARC(s) into one flat directory.')
        p_extract_flat.add_argument('source_path', type=str, help='Path to an ARC file or a directory to scan.')
        p_extract_flat.add_argument('--output-dir', '-o', type=str, required=True, help='Directory for all extracted files.')
        for a, kw in key_args: p_extract_flat.add_argument(*a, **kw)
        p_extract_flat.set_defaults(func=handle_cli_extract_flat)
        
        p_install = subparsers.add_parser('install-menu', help='Install Windows Context Menu items.')
        p_install.set_defaults(func=lambda x: install_context_menu())

        args = parser.parse_args()
        
        if hasattr(args, 'func'):
            _keep_window_open_on_error(args.func, args)
        else:
            if TkinterDnD: 
                root = TkinterDnD.Tk()
            else: 
                root = tk.Tk()
            app = ArcToolApp(root)
            root.mainloop()