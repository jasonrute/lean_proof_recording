import collections
import json
from pathlib import Path
import sys
import traceback
from typing import Any, Dict, List, Set, Tuple, Optional

from parse_lean import AST, LeanParser
from tokenize_lean_files import LeanFile, TokenType

def get_traced_data(data_dir: Path, table: str) -> List[Dict[str, Any]]:
    with open(data_dir / "raw_traced_data" /(table + ".json"), "r") as f:
        return json.load(f)

def save_data_tables(data_tables: Dict[str, List[Dict[str, Any]]], data_dir: Path):
    dir = data_dir/"extracted_proof_data"
    dir.mkdir()
    for table_name, table in data_tables.items():
        # save each table to a file
        filename = table_name + ".json"
        with open(dir/filename, 'w') as outfile:
            json.dump(table, outfile)

class ProofExtractor:
    # inputs
    lean_file: LeanFile
    relative_file_path: Path
    tactic_instance_data: List[Dict[str, Any]]
    tactic_position_data: List[Dict[str, Any]]
    # intermediate data sets
    tactic_pos_data: List[Dict[str, Any]] = []
    file_tactic_symbol_data: List[Dict[str, Any]] = []
    # hints for parsing the proofs
    parameter_positions: Dict[Tuple[int, int], List[Tuple[int, int]]]
    tactic_block_positions: Set[Tuple[int, int]]
    evaluated_positions: Set[Tuple[int, int]]
    # end results
    proof_trees: List[Dict[str, Any]] = []
    proof_table: List[Dict[str, Any]] = []
    tactic_table: List[Dict[str, Any]] = []
    arg_table: List[Dict[str, Any]] = []

    def __init__(
        self, 
        lean_file: LeanFile, 
        relative_file_path: Path, 
        tactic_instance_data: List[Dict[str, Any]], 
        tactic_params_pos_data: List[Dict[str, Any]]
    ):
        self.lean_file = lean_file
        self.relative_file_path = relative_file_path
        self.tactic_instance_data = tactic_instance_data
        self.tactic_params_pos_data = tactic_params_pos_data
    
    @staticmethod
    def remove_index_from_key(key: str) -> str:
        """The key is of the form <line>:<col>:<depth>:<index>"""
        return ":".join(key.split(":")[:3])

    def build_tactic_pos_data(self) -> None:
        tactic_pos_data = {}
        for tactic_instance in self.tactic_instance_data:
            tactic_pos = {}
            tactic_pos['filename'] = tactic_instance['filename']
            tactic_pos["key"] = self.remove_index_from_key(tactic_instance["key"])
            tactic_pos["trace_pos_line"] = tactic_instance["trace_pos_line"]
            tactic_pos["trace_pos_column"] = tactic_instance["trace_pos_column"]
            tactic_pos["line"] = tactic_instance["line"]
            tactic_pos["column"] = tactic_instance["column"]
            tactic_pos["depth"] = tactic_instance["depth"]
            tactic_pos["proof"] = self.remove_index_from_key(tactic_instance["proof"])
            tactic_pos["block"] = self.remove_index_from_key(tactic_instance["block"])
            tactic_pos["parent"] = self.remove_index_from_key(tactic_instance["parent"])

            tactic_pos_data[tactic_pos['filename'], tactic_pos["key"]] = tactic_pos

        self.tactic_pos_data = list(tactic_pos_data.values())

    def build_tactic_symbol_data(self) -> None:
        tactic_symbol_data: Dict[str, Dict[str, Any]] = {}
        for tac in sorted(self.tactic_pos_data, key=lambda tac: tac['depth']):
            # Tactics inside any `[...] block show up in the dataset
            # even if they are in another file.  We will remove
            # them.  They can be filtered out by checking if the
            # line and column from istep is the same as the traced 
            # line and column.
            if (tac['trace_pos_line'], tac['trace_pos_column']) != (tac['line'], tac['column']):
                continue
            data = {}
            data['filename'] = tac['filename']
            data['key'] = tac['key']
            data['parent'] = tac['parent']
            data['depth'] = tac['depth']
            symbol = self.lean_file.get_token(tac['line']-1, tac['column']-1).string

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
                    left = self.lean_file.find_left_bracket(['{'], ['}'], tac['line']-1, tac['column']-1)
                    data['type'] = "begin_end"
                    data['line'] = left.line+1
                    data['column'] = left.column+1
                elif symbol == 'end':
                    left = self.lean_file.find_left_bracket(['begin', 'match'], ['end'], tac['line']-1, tac['column']-1)
                    data['type'] = "begin_end"
                    data['line'] = left.line+1
                    data['column'] = left.column+1
                else:
                    data['type'] = "named"
                    data['line'] = tac['line']
                    data['column'] = tac['column']

                # get previous token
                preceeding_token = self.lean_file.get_prev_matching_pattern(data['line']-1, data['column']-1, [TokenType.SYMBOL, TokenType.ALPHANUMERIC])

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

        self.tactic_symbol_data = list(tactic_symbol_data.values())

    def build_parser_hints(self) -> None:
        self.tactic_symbol_data.sort(key=lambda tac: (tac['line'], tac['column']))
        self.tactic_params_pos_data.sort(key=lambda param: (param['line'], param['column']))

        self.parameter_positions = collections.defaultdict(list)
        for param in self.tactic_params_pos_data:
            # empty parameters start and end at same position
            self.parameter_positions[param["line"]-1, param["column"]-1].append((param["end_line"]-1, param["end_column"]-1))
        self.tactic_block_positions = set()
        for tac in self.tactic_symbol_data:
            if tac['preceeding_symbol'] in ('by', 'begin', '{'):
                self.tactic_block_positions.add((tac['preceeding_line']-1, tac['preceeding_column']-1))

        self.evaluated_positions = set()

    def extract_ast(self, ast: AST.ASTData, proof_key: Optional[str] = None) -> Dict[str, Any]:
        # each ast node will be converted into the output ast as well as added to a table
        node = {}

        row = {}
        row['filename'] = self.relative_file_path
        row['start_line'] = ast.line + 1
        row['start_column'] = ast.column + 1
        row['end_line'] = ast.end_line + 1
        row['end_column'] = ast.end_column + 1
        row['code'] = self.lean_file.slice_string(ast.line, ast.column, ast.end_line, ast.end_column, clean=True)

        if proof_key is not None:
            row['proof_key'] = proof_key
        
        # Uniquely identify the node by the position of its symbol.
        # Most nodes this is the position of the leading character,
        # but forsemicolon and alternate tactics this will be updated below
        # to the position of the infix operator
        row['line'] = ast.line + 1
        row['column'] = ast.column + 1
        
        if isinstance(ast, AST.ByProof):
            node['node_type'] = "proof"
            node['node_subtype'] = "by"
            node['tactic'] = self.extract_ast(ast.tactic, proof_key)
            
            row['first_tactic_key'] = node['tactic']['key']
        elif isinstance(ast, AST.BeginProof):
            node['node_type'] = "proof"
            node['node_subtype'] = "begin"
            node['tactics'] = []
            for tactic in ast.tactics:
                node['tactics'].append(self.extract_ast(tactic, proof_key))
            
            row['first_tactic_key'] = node['tactics'][0]['key']
        elif isinstance(ast, AST.SemicolonListTactic):
            node['node_type'] = "tactic"
            node['node_subtype'] = "semicolon_list"
            node['tactic1'] = self.extract_ast(ast.tactic1, proof_key)
            node['tactics2'] = []
            for tactic in ast.tactic_list:
                node['tactics2'].append(self.extract_ast(tactic,  proof_key))
            
            row['line'] = ast.semicolon_line + 1
            row['column'] = ast.semicolon_column + 1
        elif isinstance(ast, AST.SemicolonTactic):
            node['node_type'] = "tactic"
            node['node_subtype'] = "semicolon"
            node['tactic1'] = self.extract_ast(ast.tactic1, proof_key)
            node['tactic2'] = self.extract_ast(ast.tactic2, proof_key)
            
            row['line'] = ast.semicolon_line + 1
            row['column'] = ast.semicolon_column + 1
        elif isinstance(ast, AST.AlternativeTactic):
            node['node_type'] = "tactic"
            node['node_subtype'] = "alternative"
            node['tactic1'] = self.extract_ast(ast.tactic1, proof_key)
            node['tactic2'] = self.extract_ast(ast.tactic2, proof_key)
            
            row['line'] = ast.alternative_line + 1
            row['column'] = ast.alternative_column + 1
        elif isinstance(ast, AST.Solve1Tactic):
            node['node_type'] = "tactic"
            node['node_subtype'] = "solve1"
            node['tactics'] = []
            for tactic in ast.tactics:
                node['tactics'].append(self.extract_ast(tactic, proof_key))
        elif isinstance(ast, AST.NamedTactic):
            node['node_type'] = "tactic"
            node['node_subtype'] = "named"
            node['args'] = []
            for arg in ast.args:
                node['args'].append(self.extract_ast(arg, proof_key))
        elif isinstance(ast, AST.ITactic):
            node['node_type'] = "tactic"
            node['node_subtype'] = "itactic"
            node['tactics'] = []
            for tactic in ast.tactics:
                node['tactics'].append(self.extract_ast(tactic, proof_key))
        elif isinstance(ast, AST.CalcTactic):
            node['node_type'] = "tactic"
            node['node_subtype'] = "calc"
            # for now we don't store much special about calc tactics 
            # which are fairly rare
        elif isinstance(ast, AST.ITacticTacticParam):
            node['node_type'] = "tactic_arg"
            node['node_subtype'] = "itactic"
        elif isinstance(ast, AST.TacticParam): # TODO: Change parser here to return a subtype
            node['node_type'] = "tactic_arg"
            node['node_subtype'] = "expression"
        else:
            raise Exception(ast)
        
        node['key'] = row['key'] = f"{row['filename']}:{row['line']}:{row['column']}"
        row['class'] = node['node_subtype']
        if node['node_type'] == "proof":
            self.proof_table.append(row)
        elif node['node_type'] == "tactic":
            self.tactic_table.append(row)
            self.evaluated_positions.add((ast.line, ast.column))
        elif node['node_type'] == "tactic_arg":
            self.arg_table.append(row)
        
        return node

    def run(self):
        self.build_tactic_pos_data()
        self.build_tactic_symbol_data()
        self.build_parser_hints()

        for tac in self.tactic_symbol_data:
            try:
                if (tac["line"]-1, tac["column"]-1) in self.evaluated_positions:
                    continue

                parser = LeanParser(
                    self.lean_file, 
                    tac['preceeding_line']-1, 
                    tac['preceeding_column']-1, 
                    parameter_positions=self.parameter_positions, 
                    tactic_block_positions=self.tactic_block_positions
                )
                if tac['preceeding_symbol'] == "by":
                    parser_ast = parser.read_by()
                elif tac['preceeding_symbol'] == "begin":
                    parser_ast = parser.read_begin()
                else:
                    raise Exception(f"This tactic should already have been processed: {tac}")

                # besides returning a proof tree
                # this method also add each node to the output tables and
                # to the evaluated_positions set
                proof_tree = self.extract_ast(parser_ast)
                self.proof_trees.append(proof_tree)
                
            except Exception as e:
                # print(e)
                print(self.lean_file.filename)
                traceback.print_exc()


def main():
    assert len(sys.argv) == 2
    data_dir = Path(sys.argv[1])
    assert data_dir.exists(), data_dir
    assert data_dir.is_dir(), data_dir

    data_tables = collections.defaultdict(list)

    tactic_instance_data = get_traced_data(data_dir, "tactic_instances")
    tactic_params_pos_data = get_traced_data(data_dir, "tactic_param_pos")

    files = sorted({row['filename'] for row in tactic_instance_data})
    for relative_file_path in files:
        file_path = Path(data_dir) / "lean_files" / relative_file_path
        # print(file_path)
        try:
            lean_file = LeanFile(str(file_path))

            tactic_instance_data = [row for row in tactic_instance_data if row['filename'] == relative_file_path]
            tactic_params_pos_data = [row for row in tactic_params_pos_data if row['filename'] == relative_file_path]
            
            proof_extractor = ProofExtractor(
                lean_file=lean_file, 
                relative_file_path=relative_file_path,
                tactic_instance_data=tactic_instance_data,
                tactic_params_pos_data=tactic_params_pos_data
            )
            proof_extractor.run()

            data_tables["proof_trees"].extend(proof_extractor.proof_trees)
            data_tables["proofs"].extend(proof_extractor.proof_table)
            data_tables["tactics"].extend(proof_extractor.tactic_table)
            data_tables["args"].extend(proof_extractor.arg_table)

        except Exception:
            print(file_path)
            traceback.print_exc()

    save_data_tables(data_tables, data_dir)

if __name__ == "__main__":
    main()