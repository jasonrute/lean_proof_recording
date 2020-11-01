import collections
import json
from pathlib import Path
import sys
import traceback
from typing import Any, Dict, List, Tuple

from parse_lean import AST, LeanParser
from tokenize_lean_files import LeanFile, TokenType

def get_traced_data(data_dir: Path, table: str) -> List[Dict[str, Any]]:
    with open(data_dir / "raw_traced_data" /(table + ".json"), "r") as f:
        return json.load(f)

def save_data(data_dir: Path, table: List[Dict[str, Any]], filename: str) -> None:
    dir = data_dir/"extracted_data"
    dir.mkdir(exist_ok=True)
    with open(dir /(filename + ".json"), "w") as f:
        return json.dump(table, f)

def remove_index_from_key(key: str) -> str:
    """The key is of the form <line>:<col>:<depth>:<index>"""
    return ":".join(key.split(":")[:3])

def build_tactic_pos_data(tactic_instance_data: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    tactic_pos_data = {}
    for tactic_instance in tactic_instance_data:
        tactic_pos = {}
        tactic_pos['filename'] = tactic_instance['filename']
        tactic_pos["key"] = remove_index_from_key(tactic_instance["key"])
        tactic_pos["trace_pos_line"] = tactic_instance["trace_pos_line"]
        tactic_pos["trace_pos_column"] = tactic_instance["trace_pos_column"]
        tactic_pos["line"] = tactic_instance["line"]
        tactic_pos["column"] = tactic_instance["column"]
        tactic_pos["depth"] = tactic_instance["depth"]
        tactic_pos["proof"] = remove_index_from_key(tactic_instance["proof"])
        tactic_pos["block"] = remove_index_from_key(tactic_instance["block"])
        tactic_pos["parent"] = remove_index_from_key(tactic_instance["parent"])

        tactic_pos_data[tactic_pos['filename'], tactic_pos["key"]] = tactic_pos

    return list(tactic_pos_data.values())

def filter_data(filename: str, tactic_params_pos_data: List[Dict['str', Any]], tactic_pos_data: List[Dict['str', Any]]) -> Tuple[List[Dict['str', Any]], List[Dict['str', Any]]]:
    tactic_params_pos_data = [row for row in tactic_params_pos_data if row['filename'] == filename]
    tactic_pos_data = [row for row in tactic_pos_data if row['filename'] == filename]
    return tactic_params_pos_data, tactic_pos_data

def build_tactic_symbol_data(lean_file: LeanFile, tactic_pos_data: List[Dict['str', Any]]) -> List[Dict['str', Any]]:
    tactic_symbol_data: Dict[str, Dict[str, Any]] = {}
    for tac in sorted(tactic_pos_data, key=lambda tac: tac['depth']):
        # Tactics inside any `[...] block will show up here
        # even if they are in another file.  It is best to remove
        # the.  They can be filtered out by checking if the
        # line, column from istep is the same as the traced line
        # and column.
        if (tac['trace_pos_line'], tac['trace_pos_column']) != (tac['line'], tac['column']):
            continue
        data = {}
        data['filename'] = tac['filename']
        data['key'] = tac['key']
        data['parent'] = tac['parent']
        data['depth'] = tac['depth']
        symbol = lean_file.get_token(tac['line']-1, tac['column']-1).string

        if symbol == ";":
            data['type'] = "semicolon"
            # this info will be filled in when processing children later
            data['line'] = float('inf')
            data['column'] = float('inf')
            data['semicolon_reverse_depth'] = None
            data['preceeding_symbol'] = None
            data['preceeding_line'] = None
            data['preceeding_column'] = None
        else:
            if symbol == '}':
                left = lean_file.find_left_bracket(['{'], ['}'], tac['line']-1, tac['column']-1)
                data['type'] = "begin_end"
                data['line'] = left.line+1
                data['column'] = left.column+1
            elif symbol == 'end':
                left = lean_file.find_left_bracket(['begin', 'match'], ['end'], tac['line']-1, tac['column']-1)
                data['type'] = "begin_end"
                data['line'] = left.line+1
                data['column'] = left.column+1
            else:
                data['type'] = "named"
                data['line'] = tac['line']
                data['column'] = tac['column']

            # get previous token
            preceeding_token = lean_file.get_prev_matching_pattern(data['line']-1, data['column']-1, [TokenType.SYMBOL, TokenType.ALPHANUMERIC])

            data['semicolon_reverse_depth'] = 0
            data['preceeding_symbol'] = preceeding_token.string
            data['preceeding_line'] = preceeding_token.line+1
            data['preceeding_column'] = preceeding_token.column+1

            current_data = data
            rev_depth = 0
            while current_data['parent'] in tactic_symbol_data:
                current_data = tactic_symbol_data[current_data['parent']]
                if current_data['type'] != "semicolon":
                    break

                rev_depth += 1

                if (data['line'], data['column']) < (current_data['line'], current_data['column']):
                    current_data['line'] = data['line']
                    current_data['column'] = data['column']
                    current_data['semicolon_reverse_depth'] = rev_depth
                    current_data['preceeding_symbol'] = data['preceeding_symbol']
                    current_data['preceeding_line'] = data['preceeding_line']
                    current_data['preceeding_column'] = data['preceeding_column']

        tactic_symbol_data[data['key']] = data

    return list(tactic_symbol_data.values())

def build_ast_data(ast: AST.ASTData, depth: int, ast_data: List[Dict[str, Any]]):
    # each row of the table is one node in the ast for a proof
    node = {}
    node['line'] = ast.line + 1
    node['column'] = ast.column + 1
    node['end_line'] = ast.end_line + 1
    node['end_column'] = ast.end_column + 1
    node['depth'] = depth
    node['key'] = str(node['line']) + ":" + str(node['column']) + ":" + str(node['depth'])
    pos = (node['line'], node['column'])

    if isinstance(ast, AST.ByProof):
        node['type'] = "by_proof"
        node['class'] = "proof"
        ast_data.append(node)
        tactic = ast.tactic
        build_ast_data(tactic, depth+1, ast_data)
    elif isinstance(ast, AST.BeginProof):
        node['type'] = "begin_proof"
        node['class'] = "proof"
        ast_data.append(node)
        for tactic in ast.tactics:
            build_ast_data(tactic, depth+1, ast_data)
    elif isinstance(ast, AST.SemicolonListTactic):
        node['type'] = "semicolon_list_tactic"
        node['class'] = "tactic"
        ast_data.append(node)
        build_ast_data(ast.tactic1, depth+1, ast_data)
        for tactic in ast.tactic_list:
            build_ast_data(tactic, depth+1, ast_data)
    elif isinstance(ast, AST.SemicolonTactic):
        node['type'] = "semicolon_tactic"
        node['class'] = "tactic"
        ast_data.append(node)
        build_ast_data(ast.tactic1, depth+1, ast_data)
        build_ast_data(ast.tactic2, depth+1, ast_data)
    elif isinstance(ast, AST.AlternativeTactic):
        node['type'] = "alternative_tactic"
        node['class'] = "tactic"
        ast_data.append(node)
        build_ast_data(ast.tactic1, depth+1, ast_data)
        build_ast_data(ast.tactic2, depth+1, ast_data)
    elif isinstance(ast, AST.Solve1Tactic):
        node['type'] = "solve1_tactic"
        node['class'] = "tactic"
        ast_data.append(node)
        for tactic in ast.tactics:
            build_ast_data(tactic, depth+1, ast_data)
    elif isinstance(ast, AST.NamedTactic):
        node['type'] = "named_tactic"
        node['class'] = "tactic"
        ast_data.append(node)
        for param in ast.args:
            build_ast_data(param, depth+1, ast_data)
    elif isinstance(ast, AST.ITactic):
        node['type'] = "itactic"
        node['class'] = "tactic"
        ast_data.append(node)
        for tactic in ast.tactics:
            build_ast_data(tactic, depth+1, ast_data)
    elif isinstance(ast, AST.CalcTactic):
        node['type'] = "calc_tactic"
        node['class'] = "tactic"
        ast_data.append(node)
    elif isinstance(ast, AST.TacticParam):
        node['type'] = "param"
        node['class'] = "param"
        ast_data.append(node)
    else:
        raise Exception(ast)

def parse_ast_data(lean_file: LeanFile, relative_filename: str, tactic_params_pos_data: List[Dict['str', Any]], tactic_symbol_data: List[Dict['str', Any]]) -> List[Dict['str', Any]]:
    tactic_symbol_data.sort(key=lambda tac: (tac['line'], tac['column']))
    tactic_params_pos_data.sort(key=lambda param: (param['line'], param['column']))

    parameter_positions = collections.defaultdict(list)
    for param in tactic_params_pos_data:
        # empty parameters start and end at same position
        parameter_positions[param["line"]-1, param["column"]-1].append((param["end_line"]-1, param["end_column"]-1))

    evaluated_positions = collections.Counter()

    ast_data = []
    for tac in tactic_symbol_data:
        try:
            line = tac["line"] - 1
            column = tac["column"] - 1

            if (line, column) in evaluated_positions:
                continue

            parser = LeanParser(lean_file, tac['preceeding_line']-1, tac['preceeding_column']-1, parameter_positions=parameter_positions)
            if tac['preceeding_symbol'] == "by":
                ast = parser.read_by()
            elif tac['preceeding_symbol'] == "begin":
                ast = parser.read_begin()
            elif tac['preceeding_symbol'] == "{":
                ast = parser.read_itactic()
            else:
                raise Exception(tac)

            new_ast_data = []
            build_ast_data(ast, 0, new_ast_data)

            for node in new_ast_data:
                node['filename'] = relative_filename
                node['string'] = lean_file.slice_string(node['line']-1, node['column']-1, node['end_line']-1, node['end_column']-1)
                evaluated_positions[node["line"]-1, node["column"]-1] += 1
            
            ast_data.extend(new_ast_data)

        except Exception as e:
            # print(e)
            print(lean_file.filename)
            traceback.print_exc()

    return ast_data
    
def main():
    assert len(sys.argv) == 2
    data_dir = Path(sys.argv[1])
    assert data_dir.exists(), data_dir
    assert data_dir.is_dir(), data_dir

    tactic_instance_data = get_traced_data(data_dir, "tactic_instances")
    tactic_params_pos_data = get_traced_data(data_dir, "tactic_param_pos")

    # information about just the tactic positions
    tactic_pos_data = build_tactic_pos_data(tactic_instance_data)

    files = sorted({row['filename'] for row in tactic_pos_data})

    ast_data = []
    tactic_symbol_data = []
    for relative_file_path in files:
        file_path = Path(data_dir) / "lean_files" / relative_file_path
        # print(file_path)
        try:
            file_tactic_params_pos_data, file_tactic_pos_data = filter_data(relative_file_path, tactic_params_pos_data, tactic_pos_data)
            lean_file = LeanFile(str(file_path))
            file_tactic_symbol_data = build_tactic_symbol_data(lean_file, file_tactic_pos_data)
            tactic_symbol_data.extend(file_tactic_symbol_data)
            file_ast_data = parse_ast_data(lean_file, relative_file_path, file_tactic_params_pos_data, file_tactic_symbol_data)
            ast_data.extend(file_ast_data)
        except Exception:
            print(file_path)
            traceback.print_exc()

    save_data(data_dir, tactic_pos_data, "tactic_pos")
    save_data(data_dir, tactic_symbol_data, "tactic_symbol")
    save_data(data_dir, ast_data, "ast")

if __name__ == "__main__":
    main()