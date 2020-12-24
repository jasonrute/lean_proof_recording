/- This is a staging area for code which will be inserted
into a Lean file. 

The code to be inserted is between the line comments
`PR BEGIN MODIFICATION` and `PR END MODIFICATION`

It will be inserted by `insert_proof_recording_code.py`.

Insert info:
  - file: `_target/deps/lean/library/init/meta/interactive.lean`
  - location: after the imports before any other code

Most of this code is carefully written, but
any code labeled "BEGIN/END CUSTOMIZABLE CODE"
encourages customization to change what
is being recorded
-/

prelude
import init.meta.tactic init.meta.type_context init.meta.rewrite_tactic init.meta.simp_tactic
import init.meta.smt.congruence_closure init.control.combinators
import init.meta.interactive_base init.meta.derive init.meta.match_tactic
import init.meta.congr_tactic init.meta.case_tag
import .interactive_base_modifications

--PR BEGIN MODIFICATION





---------------------------
-- tools and help functions
---------------------------

--def option.mmap {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (f : α → m β) : option α → m (option β)
--| none       := return none
--| (some x) := do x' ← f x, return (some x')
--end option

--def list.last_option {α : Type u}: list α → option α
--| []        := none
--| [a]       := some a
--| (a::b::l) := list.last_option (b::l)

namespace expr

meta def local_uniq_name_option : expr → option name
| (expr.local_const n m bi t) := some n
| e                      := none

meta def mvar_uniq_name_option : expr → option name
| (expr.mvar n ppn t) := some n
| e                   := none

end expr

-- set the tactic state
meta def set_state (new_state: tactic_state): tactic unit :=
  -- this is in mathlib but easier to recreate
  λ _, interaction_monad.result.success () new_state




-----------------------
-- json2
-----------------------

-- This is a copy of the json2 structure, but removing anything that is
-- not available already in interactive.lean
meta inductive json2 : Type
| of_string : string → json2
| of_nat : nat → json2
| of_bool : bool → json2
| null : json2
| object : list (string × json2) → json2
| array : list json2 → json2

namespace json2

meta instance string_coe : has_coe string json2 := ⟨json2.of_string⟩
meta instance int_coe : has_coe nat json2 := ⟨json2.of_nat⟩
meta instance bool_coe : has_coe bool json2 := ⟨json2.of_bool⟩
meta instance array_coe : has_coe (list json2) json2 := ⟨json2.array⟩
meta instance : inhabited json2 := ⟨json2.null⟩

meta def to_format : json2 → format
| (of_string s) := string.quote s
| (of_nat i) := to_string i
| (of_bool tt) := "true"
| (of_bool ff) := "false"
| (null) := "null"
| (object kvs) := "{ " ++ (format.group $ format.nest 2 $ format.join $ list.intersperse (", " ++ format.line) $ kvs.map $ λ ⟨k,v⟩, string.quote k ++ ":" ++ to_format v) ++ "}"
| (array js) := list.to_format $ js.map to_format

meta instance : has_to_format json2 := ⟨to_format⟩

end json2









-------------------------
-- Tactic state serialization
-------------------------
section tactic_state_serialization
open tactic.unsafe

universes u v w

-- types for encoding tactic state information

meta structure mvar_decl :=
(unique_name : name)
(pp_name : name)
(expr_type : expr)
(local_cxt : list expr)
(type : option expr)
(assignment : option expr)

/- There already is a local_decl type, but 
this is some more informtion for understanding 
the type better.-/
meta structure local_decl2 :=
(unique_name : name)
(pp_name : name)
(expr_type : expr)
(bi : binder_info)
(type : option expr)
(prev : option name)
(frozen : bool)
(ld : option local_decl)

meta structure univ_mvar_decl :=
(unique_name : name)
(assignment : option level)

meta inductive context.decl
| mvar_decl (mv : mvar_decl) : context.decl
| univ_mvar_decl (mv : univ_mvar_decl) : context.decl
| local_decl (loc : local_decl2) : context.decl

meta structure context :=
-- in order of dependecies
(decls : list context.decl)
(names : name_set)

meta structure tactic_state_data :=
(decls : list context.decl)
(goals : list (name × tactic.tag))

-- convience functions and instances

meta instance mvar_decl_has_to_string : has_to_format mvar_decl := 
⟨ λ d, format! "{{mvar_decl .\nunique_name := {d.unique_name},\npp_name := {d.pp_name},\nexpr_type := {d.expr_type},\nlocal_cxt := {d.local_cxt},\ntype := {d.type},\nassignment := {d.assignment},\n}" ⟩ 

meta instance univ_mvar_decl_has_to_string : has_to_format univ_mvar_decl := 
⟨ λ d, format! "{{univ_mvar_decl .\nunique_name := {d.unique_name},\nassignment := {d.assignment},\n}" ⟩ 

meta instance local_decl_has_to_string : has_to_format local_decl := 
⟨ λ d, format! "{{local_decl .\nunique_name := {d.unique_name},\npp_name := {d.pp_name},\ntype := {d.type},\nvalue := {d.value},\nbi := {repr d.bi},\nidx := {d.idx},\n}" ⟩ 

meta instance local_decl2_has_to_string : has_to_format local_decl2 := 
⟨ λ d, format! "{{local_decl2 .\nunique_name := {d.unique_name},\npp_name := {d.pp_name},\nexpr_type := {d.expr_type},\nbi := {repr d.bi},\ntype := {d.type},\nprev := {d.prev}\n},\nfrozen := {d.frozen},\nld := {d.ld}" ⟩ 

meta def context.decl.unique_name : context.decl -> name
| (context.decl.mvar_decl d) := d.unique_name
| (context.decl.univ_mvar_decl d) := d.unique_name
| (context.decl.local_decl d) := d.unique_name

meta instance context_decl_has_to_string : has_to_format context.decl := 
⟨ λ d, match d with
| context.decl.mvar_decl d := format! "{d}"
| context.decl.univ_mvar_decl d := format! "{d}"
| context.decl.local_decl d := format! "{d}"
end ⟩

meta instance context_has_to_string : has_to_format context := 
⟨ λ cxt, format! "{cxt.decls}" ⟩


-- constructors

meta def context.empty : context := 
{ decls := [], names := mk_name_set }

meta def context.mk1 (d : context.decl) : context :=
{ decls := [d], names := name_set.of_list [d.unique_name]}

meta def context.append (cxt1 : context) (cxt2 : context) : context :=
{ decls := cxt1.decls ++ (cxt2.decls.filter (λ d, ¬ (cxt1.names.contains d.unique_name))),
  names := cxt1.names.fold cxt2.names $ λ n ns, ns.insert n
}

meta instance context.has_append : has_append context := ⟨ context.append ⟩

/- Get univ metavariables level expression tree.-/
meta def context.process_level : level -> tactic context
| level.zero := return context.empty
| (level.succ lvl) := context.process_level lvl
| (level.max lvl1 lvl2) := do
  cxt1 <- context.process_level lvl1,
  cxt2 <- context.process_level lvl2,
  return (cxt1 ++ cxt2)
| (level.imax lvl1 lvl2) := do
  cxt1 <- context.process_level lvl1,
  cxt2 <- context.process_level lvl2,
  return (cxt1 ++ cxt2)
| (level.param _) := return context.empty
| lvl@(level.mvar nm) := do
  ass <- optional (tactic.get_univ_assignment lvl),
  let univ_decl := context.decl.univ_mvar_decl {
    unique_name := nm,
    assignment := ass
  },
  return (context.mk1 univ_decl)

def find_prev {α : Type} [decidable_eq α] (a : α) : list α -> option α
| [] := none
| [b] := none
| (b :: c :: ls) := if c = a then some b else find_prev (c :: ls)

/- Get metavariables and local constants inside an expression tree, follow recursively. -/
meta def context.process_expr : expr -> local_context -> tactic context
| (expr.var _) _ := return context.empty
| (expr.sort lvl) _ := context.process_level lvl
| (expr.const _ lvls) _ := do
  cxts <- lvls.mmap context.process_level,
  let cxt := cxts.foldl context.append context.empty,
  return cxt
| mv@(expr.mvar unique_nm pp_nm tp) _ := do
  lcxt <- type_context.run $ type_context.get_context mv,
  let local_cxt := lcxt.to_list,
  cxts <- local_cxt.mmap (λ e, context.process_expr e lcxt),
  let cxt := cxts.foldl context.append context.empty,
  tp_cxt <- context.process_expr tp lcxt,
  mv_type <- optional (tactic.infer_type mv),
  tp_cxt2 <- match mv_type with
  | (some e) := context.process_expr e lcxt
  | none := return context.empty
  end,
  assignment <- optional (tactic.get_assignment mv),
  ass_cxt <- match assignment with
  | (some e) := context.process_expr e lcxt
  | none := return context.empty
  end,
  let mv_dec := context.decl.mvar_decl {
    unique_name := unique_nm,
    pp_name := pp_nm,
    expr_type := tp,
    local_cxt := local_cxt,
    type := mv_type,
    assignment := assignment
  },
  return $ cxt ++ tp_cxt ++ tp_cxt2 ++ ass_cxt ++ (context.mk1 mv_dec)
| lconst@(expr.local_const unique_nm pp_nm bi tp) lcxt := do
  tp_cxt <- context.process_expr tp lcxt,
  loc_type <- optional (tactic.infer_type lconst),
  tp_cxt2 <- match loc_type with
  | (some e) := context.process_expr e lcxt
  | none := return context.empty
  end,
  let ld := lcxt.get_local_decl unique_nm,
  tp_cxt3 <- match ld with
  | (some ld) := context.process_expr ld.type lcxt
  | none := return context.empty
  end,
  value_cxt <- match ld with
  | (some ld) := match ld.value with
    | (some e) := context.process_expr e lcxt
    | none := return context.empty
    end
  | none := return context.empty
  end,
  let (prev : option expr) := find_prev lconst lcxt.to_list,
  let prev_id := match prev with
  | some (expr.local_const id _ _ _) := some id
  | _ := none
  end,
  frozen_instances_opt <- tactic.frozen_local_instances,
  let frozen := match frozen_instances_opt with
  | none := ff
  | some frozen_instances := frozen_instances.any (λ e, e.local_uniq_name_option = some unique_nm)
  end,
  let loc_dec := context.decl.local_decl {
    unique_name := unique_nm,
    pp_name := pp_nm,
    expr_type := tp,
    bi := bi,
    type := loc_type,
    prev := prev_id,
    frozen := frozen,
    ld := lcxt.get_local_decl unique_nm,
  },
  return $ tp_cxt ++ tp_cxt2 ++ tp_cxt3 ++ value_cxt ++ (context.mk1 loc_dec)
| (expr.app expr1 expr2) lcxt := do
  cxt1 <- context.process_expr expr1 lcxt,
  cxt2 <- context.process_expr expr2 lcxt,
  return (cxt1 ++ cxt2)
| (expr.lam _ _ expr1 expr2) lcxt := do
  cxt1 <- context.process_expr expr1 lcxt,
  cxt2 <- context.process_expr expr2 lcxt,
  return (cxt1 ++ cxt2)
| (expr.pi _ _ expr1 expr2) lcxt := do
  cxt1 <- context.process_expr expr1 lcxt,
  cxt2 <- context.process_expr expr2 lcxt,
  return (cxt1 ++ cxt2)
| (expr.elet _ expr1 expr2 expr3) lcxt := do
  cxt1 <- context.process_expr expr1 lcxt,
  cxt2 <- context.process_expr expr2 lcxt,
  cxt3 <- context.process_expr expr3 lcxt,
  return (cxt1 ++ cxt2 ++ cxt3)
| (expr.macro _ _) _ := tactic.fail "Can't handle macros yet"

meta def context.get : tactic context := do
  lcxt <- type_context.run $ type_context.get_local_context,
  mvs <- tactic.get_goals,
  cxts <- mvs.mmap (λ e, context.process_expr e lcxt),
  let cxt := cxts.foldl context.append context.empty,
  return cxt

meta def tactic_state_data.get : tactic tactic_state_data := do
  cxt <- context.get,
  gs <- tactic.get_goals,
  goals <- gs.mmap $ λ g, do {
    nm <- g.mvar_uniq_name_option,
    tag <- tactic.get_tag g,
    return (nm, tag)
  },
  return { 
    decls := cxt.decls,
    goals := goals
  }

end tactic_state_serialization




-----------------------
-- serialization for tactic_state_data
-----------------------

-- fill in this function
meta def serialize_tactic_state_data (tsd : tactic_state_data) : tactic string := do
sorry







-----------------------
-- proof recording code
-----------------------
namespace pr  
universes u v w

-- tactic recording

/-- Each tactic application within a given file can be keyed by four
numbers.  Combinators allow a tactic to be called more than once, and
some nested tactics use the same line and column position, so
we also include depth to capture nesting and index to capture exectuted
order.  (A proof can be uniquely keyed by its first tactic 
at depth 1, index 1.) -/
structure tactic_address :=
  -- the line and column of the tactic instance
  -- using 1-indexing like editors do even though lean uses a mix of 0 and 1-indexing
  (line : nat) (column : nat)
  -- depth of tactic block (tactic inside a tactic)
  (depth : nat) 
  -- index indicating the order of execution
  (index : nat)

meta def addr_key (addr : tactic_address) : string :=
  (repr addr.line) 
    ++ ":" ++ (repr addr.column)
    ++ ":" ++ (repr addr.depth)
    ++ ":" ++ (repr addr.index)

meta def trace_tactic_data_string (addr : tactic_address) (field : string) (str_data : string) : tactic unit :=
  trace_data_string "tactic_instances" (addr_key addr) field str_data

meta def trace_tactic_data_num (addr : tactic_address) (field : string) (num_data : nat) : tactic unit :=
  trace_data_num "tactic_instances" (addr_key addr) field num_data

meta def trace_tactic_data_bool (addr : tactic_address) (field : string) (bool_data : bool) : tactic unit :=
  trace_data_bool "tactic_instances" (addr_key addr) field bool_data

meta def trace_tactic_data_addr (addr : tactic_address) (field : string) (addr_data : tactic_address) : tactic unit :=
  trace_data_string "tactic_instances" (addr_key addr) field (addr_key addr_data)

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

meta def trace_tactic_state_data (addr: tactic_address) (finished : bool) := do
-- BEGIN CUSTOMIZABLE CODE
-- customize as needed to record different
-- parts of the tactic state in different formats

-- position data
let t_key := (addr_key addr),
let temporal := if finished then "after" else "before",
let ts_key := t_key ++ ":" ++ temporal,
trace_data_string "tactic_state" ts_key "tactic_instance" t_key,
trace_data_string "tactic_state" ts_key "before_after" temporal,

-- environment (just store fingerprints)
env <- tactic.get_env,
-- store fingerprint as a string to prevent large values errors
trace_data_string "tactic_state" ts_key "env_fingerprint" (repr env.fingerprint),

-- declaration
decl <- tactic.decl_name,
trace_data_string "tactic_state" ts_key "decl_name" (repr decl),

-- goal stack information
goals <- tactic.get_goals,
trace_data_num "tactic_state" ts_key "goal_count" goals.length,

-- tactic state serialization
result <- tactic.capture $ do {
  ts_data <- tactic_state_data.get,
  ts_str <- serialize_tactic_state_data ts_data,
  return ts_str
},
match result with
| (interaction_monad.result.success ts_str _) := do {
  trace_data_string "tactic_state" ts_key "tactic_state_serialization" ts_str,
  trace_data_string "tactic_state" ts_key "tactic_state_serialization_error" ""
}
| (interaction_monad.result.exception none _ _) := do {
  trace_data_string "tactic_state" ts_key "tactic_state_serialization" "",
  trace_data_string "tactic_state" ts_key "tactic_state_serialization_error" "<error: no message>"
}
| (interaction_monad.result.exception (some fmt) _ _) := do{
  trace_data_string "tactic_state" ts_key "tactic_state_serialization" "",
  trace_data_string "tactic_state" ts_key "tactic_state_serialization_error" (fmt ()).to_string
}
end,


-- individual goal information
goals.enum.mmap' $ λ ⟨n, g⟩, (do
  let g_key := ts_key ++ ":" ++ (repr n),
  trace_data_string "tactic_state_goal" g_key "tactic_state" ts_key,
  trace_data_num "tactic_state_goal" g_key "ix" n,
  -- store hash of goal metavariable to know if goal changed
  trace_data_num "tactic_state_goal" g_key "goal_hash" g.hash,
  -- pretty print the goal by temporarily making it the only goal
  saved_ts <- tactic.read, -- copy tactic state
  tactic.set_goals [g],
  ts <- tactic.read, -- temporary tactic state
  trace_data_string "tactic_state_goal" g_key "goal_pp" ts.to_format.to_string,
  set_state saved_ts -- put tactic state back to way it was
),
return ()
-- END CUSTOMIZABLE CODE

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
  trace_tactic_data_bool new_addr "executed" tt,
  trace_tactic_data_num new_addr "line" new_addr.line,
  trace_tactic_data_num new_addr "column" new_addr.column,
  trace_tactic_data_num new_addr "depth" new_addr.depth,
  trace_tactic_data_num new_addr "index" new_addr.index,
  trace_tactic_data_addr new_addr "proof" new_proof_addr,
  trace_tactic_data_addr new_addr "block" new_block_addr,
  trace_tactic_data_addr new_addr "parent" prev_open_addr, -- will be ⟨0,0,0,0⟩ if no parent
  trace_tactic_data_addr new_addr "prev" prev_addr,  -- previous completed tactic (not same depth)
  
  -- trace data about the state beforehand
  trace_tactic_state_data new_addr ff,

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
  trace_tactic_data_bool new_addr "executed" tt,
  trace_tactic_data_num new_addr "line" new_addr.line,
  trace_tactic_data_num new_addr "column" new_addr.column,
  trace_tactic_data_num new_addr "depth" new_addr.depth,
  trace_tactic_data_num new_addr "index" new_addr.index,
  trace_tactic_data_addr new_addr "proof" proof_addr,
  trace_tactic_data_addr new_addr "block" block_addr,
  trace_tactic_data_addr new_addr "parent" prev_open_addr, -- will be ⟨0,0,0,0⟩ if no parent
  trace_tactic_data_addr new_addr "prev" prev_addr,

  -- trace data about the state beforehand
  trace_tactic_state_data new_addr ff,

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
  trace_tactic_data_bool prev_open_addr "succeeded" tt,
  
  -- trace data about the state afterward
  trace_tactic_state_data new_addr tt,

  -- update proof trace information (only information which changes)
  o <- tactic.get_options,
  let o := o.set_nat `proof_rec.depth (depth - 1),
  let o := set_tactic_address o `proof_rec.prev new_addr,
  tactic.set_options o,

  return ()
end

meta def step_and_record {α : Type u} (line col : ℕ) (t : tactic α) : tactic unit := do
-- only record if the pp.colors flag is set to false
-- we can't make our own system option, so re-using
-- one built in.  (Even thought we are setting it to
-- the default, we can still check that it is set.)

o <- tactic.get_options,
if bnot (o.get_bool `pp.colors tt) then do
  store_info_in_tactic_state ff line col, -- before
  tactic.step t,
  store_info_in_tactic_state tt line col  -- after
else tactic.step t

end pr




-------------------
-- new istep
-------------------

namespace tactic
universe u
-- redefined istep to do proof recording
meta def istep {α : Type u} (line0 col0 : ℕ) (line col : ℕ) (t : tactic α) : tactic unit :=
λ s, (@scope_trace _ line col (λ _, pr.step_and_record line col t s)).clamp_pos line0 line col
end tactic


















--PR END MODIFICATION