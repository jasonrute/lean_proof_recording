/- This is a staging area for code which will be inserted
into a Lean file. 

The code to be inserted is between the line comments
`PR BEGIN MODIFICATION` and `PR END MODIFICATION`

It will be inserted by `insert_proof_recording_code.py`.

Insert info:
  - file: `_target/lean/library/init/meta/tactic.lean`
  - location: end of file

Most of this code is carefully written, but
any code labeled "BEGIN/END CUSTOMIZABLE CODE"
encourages customization to change what
is being recorded
-/

prelude
import init.meta.tactic

universes u v


--PR BEGIN MODIFICATION

-- proof recording code
namespace pr  

/-- Trace data as JSON preceeded by a `<PR>` flag.
This makes it easy to filter out all the traced data. -/
meta def trace_data (table : string) (key : string) (field : string) (data : string) : tactic unit :=
  tactic.trace $ "<PR> {" 
    ++ "\"table\": " ++ (repr table) ++ ", "
    ++ "\"key\": " ++ (repr key) ++ ", "
    ++ "\"" ++ field ++ "\": " ++ data
    ++ "}"

meta def trace_data_string (table : string) (key : string) (field : string) (str_data : string) : tactic unit :=
  trace_data table key field (repr str_data)

meta def trace_data_num (table : string) (key : string) (field : string) (num_data : nat) : tactic unit :=
  trace_data table key field (repr num_data)

meta def trace_data_bool (table : string) (key : string) (field : string) (bool_data : bool) : tactic unit :=
  trace_data table key field (if bool_data then "true" else "false")

end pr

--PR END MODIFICATION
