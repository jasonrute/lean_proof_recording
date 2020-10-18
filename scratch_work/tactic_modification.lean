-- START CUSTOM CODE
/-- Each tactic application within a given proof can be keyed by four
numbers.  Combinators allow a tactic to be called more than once, and
some nested tactics use the same line and column position, so
we also include depth to capture nesting and index to capture exectuted
order.  A proof can be uniquely keyed by its first tactic (at depth 1, index 1).
-/
structure tactic_address :=
  -- the line and column of the tactic instance
  -- using 1-indexing like editors do even though lean uses a mix of 0 and 1-indexing
  (line : nat) (column : nat)
  -- depth of tactic block (tactic inside a tactic)
  (depth : nat) 
  -- index indicating the order of execution
  (index : nat)

def newline := "\n"

/-- Trace data as JSON preceeded by a `<PR>` flag.
This makes it easy to filter out all the traced data. -/
meta def trace_data (addr : tactic_address) (field : string) (data : string) : tactic unit :=
  tactic.trace $ newline 
    ++ "<PR> {" 
    ++ "\"line\": " ++ (repr addr.line) ++ ", "
    ++ "\"column\": " ++ (repr addr.column) ++ ", "
    ++ "\"depth\": " ++ (repr addr.depth) ++ ", "
    ++ "\"index\": " ++ (repr addr.index) ++ ", "
    ++ "\"" ++ field ++ "\": " ++ data
    ++ "}" ++ newline

meta def trace_data_string (addr : tactic_address) (field : string) (str_data : string) : tactic unit :=
  trace_data addr field (repr str_data)

meta def trace_data_num (addr : tactic_address) (field : string) (num_data : nat) : tactic unit :=
  trace_data addr field (repr num_data)

meta def trace_data_bool (addr : tactic_address) (field : string) (bool_data : bool) : tactic unit :=
  trace_data addr field (if bool_data then "true" else "false")

meta def trace_data_addr (addr : tactic_address) (field : string) (addr_data : tactic_address) : tactic unit := do
  trace_data_num addr (field ++ "_line") addr_data.line,
  trace_data_num addr (field ++ "_column") addr_data.column,
  trace_data_num addr (field ++ "_depth") addr_data.depth,
  trace_data_num addr (field ++ "_index") addr_data.index

meta def get_tactic_address (o : options) (nm : name) : tactic_address := 
  { tactic_address .
    line   := o.get_nat (name.mk_string "line" nm) 0,
    column := o.get_nat (name.mk_string "column" nm) 0,
    depth  := o.get_nat (name.mk_string "depth" nm) 0,
    index  := o.get_nat (name.mk_string "index" nm) 0,
  }

meta def set_tactic_address (o : options) (nm : name) (addr : tactic_address) : options :=
  let o := o.set_nat (name.mk_string "line" nm) addr.line in
  let o := o.set_nat (name.mk_string "column" nm) addr.column in
  let o := o.set_nat (name.mk_string "depth" nm) addr.depth in
  let o := o.set_nat (name.mk_string "index" nm) addr.index in
  o

def is_same (a b : tactic_address) : bool := (
  a.line = b.line ∧
  a.column = b.column ∧
  a.depth = b.depth ∧
  a.index = b.index
)

meta def store_info_in_tactic_state (finished : bool) (line col : ℕ) : tactic unit := do
let column := col + 1, -- use 1-indexed columns for convience

-- get stored proof trace information
o <- tactic.get_options,
-- pop from the top of the stack
let depth := o.get_nat `proof_rec.depth 0,
let prev_open_addr := get_tactic_address o (mk_num_name `proof_rec.open depth),
let block_addr := get_tactic_address o (mk_num_name `proof_rec.block (depth+1)),
-- find the previous tactic
let prev_addr := get_tactic_address o `proof_rec.prev,
-- find the start of the proof
let proof_addr := get_tactic_address o `proof_rec.proof,

-- there are three cases.  Handle each seperately
match (finished, is_same prev_addr prev_open_addr) with
| ⟨ ff, tt ⟩ := do
  -- starting a new tactic block

  -- calculate address
  let new_depth := depth + 1,
  let new_addr := { tactic_address .
    line   := line,
    column := column,
    depth  := new_depth,
    index  := 1,
  },
  let new_block_addr := new_addr,
  let new_proof_addr := if new_depth = 1 then new_addr else proof_addr,

  -- trace data to stdout
  trace_data_bool new_addr "executed" tt,
  trace_data_addr new_addr "proof" new_proof_addr,
  trace_data_addr new_addr "block" new_block_addr,
  trace_data_addr new_addr "parent" prev_open_addr, -- will be ⟨0,0,0,0⟩ if no parent
  -- TODO: Should I just use the previous tactic.  It might be of interest to know previous tactic completed in this tactic state
  trace_data_addr new_addr "prev" ⟨0,0,0,0⟩, -- no previous tactic at same depth
  
  -- TODO: This is ambiguous:  Remove and handle in python
  -- trace_data_addr prev_open_addr "first_child" new_addr,
  
  -- update proof trace information
  o <- tactic.get_options,
  let o := o.set_nat `proof_rec.depth new_depth,
  let o := set_tactic_address o (mk_num_name `proof_rec.open new_depth) new_addr,
  let o := set_tactic_address o (mk_num_name `proof_rec.block new_depth) new_block_addr,
  let o := set_tactic_address o `proof_rec.proof new_proof_addr,
  let o := set_tactic_address o `proof_rec.prev new_addr,
  tactic.set_options o,

  return ()
| ⟨ ff, ff ⟩ := do
  -- starting new tactic at same depth as previous tactic
  
  -- calculate address
  assert $ (prev_addr.depth = depth + 1),
  assert $ (block_addr.depth = depth + 1),
  let new_depth := prev_addr.depth,
  let new_addr := { tactic_address .
    line   := line,
    column := column,
    depth  := new_depth,
    index  := prev_addr.index + 1,
  },

  -- trace data to stdout
  trace_data_bool new_addr "executed" tt,
  trace_data_addr new_addr "proof" proof_addr,
  trace_data_addr new_addr "block" block_addr,
  trace_data_addr new_addr "parent" prev_open_addr, -- will be ⟨0,0,0,0⟩ if no parent
  trace_data_addr new_addr "prev" prev_addr,
  -- TODO: ambiguous.  Remove and handle in python.
  --trace_data_addr prev_addr "next" new_addr,
  
  -- update proof trace information (only information which changes)
  o <- tactic.get_options,
  let o := o.set_nat `proof_rec.depth new_depth,
  let o := set_tactic_address o (mk_num_name `proof_rec.open new_depth) new_addr,
  let o := set_tactic_address o `proof_rec.prev new_addr,
  tactic.set_options o,

  return ()
| ⟨ tt, _ ⟩ := do
  -- tactic completed successfully

  -- calculate address
  assert $ (line = prev_open_addr.line) ∧ (column = prev_open_addr.column) ∧ (depth = prev_open_addr.depth),
  let new_addr := prev_open_addr,
  
  -- trace data to stdout
  trace_data_bool prev_open_addr "succeeded" tt,
  
  -- update proof trace information (only information which changes)
  o <- tactic.get_options,
  let o := o.set_nat `proof_rec.depth (depth - 1),
  let o := set_tactic_address o `proof_rec.prev new_addr,
  tactic.set_options o,

  return ()
end

meta def step_and_record {α : Type u} (line col : ℕ) (t : tactic α) : tactic unit := do
-- only record if the pp.colors flag is set true
-- we can't make our own system option, so re-using
-- one built in.

o <- get_options,
if (o.get_bool `pp.colors ff) then do
  store_info_in_tactic_state ff line col, -- before
  step t,
  store_info_in_tactic_state tt line col  -- after
else step t

meta def istep {α : Type u} (line0 col0 : ℕ) (line col : ℕ) (t : tactic α) : tactic unit :=
λ s, (@scope_trace _ line col (λ _, step_and_record line col t s)).clamp_pos line0 line col

-- END CUSTOM CODE
