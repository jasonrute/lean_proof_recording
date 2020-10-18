import collections
import pandas as pd
from pprint import pprint
import sys
import json
from pathlib import Path

from tokenize_lean_files import LeanFile

def extract_trace_blocks(stdout_file):
    trace_blocks = []
    other_blocks = []
    for line in stdout_file:
        if line:
            s = line
            d = json.loads(s)
            if d['severity'] == 'information' and d['caption'] == "trace output":
                trace_blocks.append(d)
            else:
                other_blocks.append(d)

    return trace_blocks, other_blocks

def read_path_map(data_dir):
    with open(data_dir+"path_map.json", 'r') as f:
        for line in f:
            return json.loads(line)

def read_trace_blocks(data_dir):
    with open(data_dir+"lean_stdout.log", 'r') as f:
        return extract_trace_blocks(f)

def file_suffix(path_map, filename):
    for p in path_map:
        if filename.startswith(p):
            return path_map[p]+filename[len(p):]

def extract_tables(trace_blocks, path_map):
    data_tables = {}
    for info_block in trace_blocks:
        file_name = file_suffix(path_map, info_block['file_name'])
        pos_line = info_block['pos_line'] # lean 1-indexes rows
        pos_column = info_block['pos_col'] + 1 # lean 0-indexes columns (but we 1-index)
        # TODO: Add different tables which can be read from the json traces
        table_name = "tactic_trace"
        for line in info_block['text'].split("\n"):
            if line.startswith('<PR>'):
                _, json_string = line.split(" ", 1)
                d = json.loads(json_string)
                d['filename'] = file_name
                d['pos_line'] = pos_line
                d['pos_column'] = pos_column
                
                # TODO: Make this more general.  
                # Maybe traces should be of the form: {'table_name': ..., 'key': ..., 'column1': ..., 'column2': ...}
                key = hash((file_name, d['line'], d['column'], d['depth'], d['index']))
                
                if table_name not in data_tables:
                    data_tables[table_name] = {}

                if key not in data_tables[table_name]:
                    data_tables[table_name][key] = collections.defaultdict(lambda: None)

                data_tables[table_name][key].update(d)
        
    return data_tables

def save_tables(data_tables, cache_file):
    with open(cache_file, 'w') as f:
        for table_name, table in data_tables.items():
            for key, row in table.items():
                row['key'] = key
                row['table_name'] = table_name
                s = json.dumps(row)
                f.write(s+"\n")

def load_tables(cache_file):
    data_tables = {}
    with open(cache_file, 'r') as f:
        for line in f:
            if line != "\n":
                d = json.loads(line)
                table_name = d['table_name']
                key = d['key']

                if table_name not in data_tables:
                    data_tables[table_name] = {}

                if key not in data_tables[table_name]:
                    data_tables[table_name][key] = collections.defaultdict(lambda: None)

                data_tables[table_name][key].update(d)
    return data_tables


def extract_lean_file_list(trace_blocks, path_map):
    file_list = set()
    for info_block in trace_blocks:
        file_name = file_suffix(path_map, info_block['file_name'])
        file_list.add(file_name)
    return list(sorted(file_list))

def extract_tokenized_lean_files(data_dir, file_list):
    lean_files = {}
    for file in file_list:
        file_path = data_dir + "lean_files/" + file
        lean_files[file] = LeanFile(file_path)
    return lean_files

def extract_data(data_dir):
    path_map = read_path_map(data_dir)
    trace_blocks, other_blocks = read_trace_blocks(data_dir)

    for o in other_blocks:
        print("Unexpected output:")
        pprint(o)

    if Path(data_dir+"_record_cache.json").exists():
        data_tables = load_tables(data_dir+"_record_cache.json")
    else:
        data_tables = extract_tables(trace_blocks, path_map)
        save_tables(data_tables, data_dir+"_record_cache.json")

    # would be better to store a file list in the data directory
    # or just get all files from the data directory.
    # for now we will hack it using the trace_blocks
    file_list = extract_lean_file_list(trace_blocks, path_map)
    lean_files = extract_tokenized_lean_files(data_dir, file_list)

    return (data_tables, lean_files)

def main():
    assert len(sys.argv) == 2
    data_dir = sys.argv[1]
    assert data_dir.endswith("/")
    
    data_tables, lean_files = extract_data(data_dir)

    # just as a previous, print using pandas
    for table_name in data_tables:
        print(table_name)
        print(pd.DataFrame(list(data_tables[table_name].values())))

    # also print the first line of the tokenized files
    for name, lean_file in lean_files.items():
        print(name)
        print(lean_file.lines[0])
        break

if __name__ == "__main__":
    main()