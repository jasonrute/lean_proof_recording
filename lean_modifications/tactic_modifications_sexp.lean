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

section sexp
inductive sexp (α : Type u) : Type u
| atom : α → sexp
| list : (list sexp) → sexp

meta def sexp.to_format {α : Type u} [has_to_format α] : sexp α → format
| (sexp.atom val) := has_to_format.to_format val
| (sexp.list ses) := format.of_string $ "(" ++ (" ".intercalate (ses.map $ format.to_string ∘ sexp.to_format)) ++ ")"

meta instance sexp_has_to_format {α} [has_to_format α] : has_to_format (sexp α) :=
⟨sexp.to_format⟩

end sexp

section open_binders
open expr
open tactic
@[simp] 
private def option.elim {α β} : option α → β → (α → β) → β
| (some x) y f := f x
| none     y f := y

private meta def match_lam {elab} : expr elab →
  option (name × binder_info × expr elab × expr elab)
| (lam var_name bi type body) := some (var_name, bi, type, body)
| _ := none

private meta def match_pi {elab} : expr elab →
  option (name × binder_info × expr elab × expr elab)
| (pi var_name bi type body) := some (var_name, bi, type, body)
| _ := none

private meta structure binder :=
  (name : name)
  (info : binder_info)
  (type : expr)

private meta def mk_binder_replacement (local_or_meta : bool) (b : binder) :
  tactic expr :=
if local_or_meta then mk_local' b.name b.info b.type else mk_meta_var b.type

@[inline] meta def get_binder (do_whnf : option (transparency × bool))
  (pi_or_lambda : bool) (e : expr) :
  tactic (option (name × binder_info × expr × expr)) := do
  e ← option.elim do_whnf (pure e) (λ p, whnf e p.1 p.2),
  pure $ if pi_or_lambda then match_pi e else match_lam e

private meta def open_n_binders (do_whnf : option (transparency × bool))
  (pis_or_lambdas : bool) (locals_or_metas : bool) :
  expr → ℕ → tactic (list expr × expr)
| e 0 := pure ([], e)
| e (d + 1) := do
  some (name, bi, type, body) ← get_binder do_whnf pis_or_lambdas e | failed,
  replacement ← mk_binder_replacement locals_or_metas ⟨name, bi, type⟩,
  (rs, rest) ← open_n_binders (body.instantiate_var replacement) d,
  pure (replacement :: rs, rest)

private meta def open_n_pis : expr → ℕ → tactic (list expr × expr) :=
open_n_binders none tt tt

private meta def open_n_lambdas : expr → ℕ → tactic (list expr × expr) :=
open_n_binders none ff tt


section sexp_of_expr
open expr

/-- head-reduce a single let expression -/
private meta def tmp_reduce_let : expr → expr
| (elet _ _ v b) := b.instantiate_var v
| e              := e

meta def sexp.concat {m} [monad m] [monad_fail m] {α} : (sexp α) → (sexp α) → m (sexp α)
| (sexp.list xs) (sexp.list ys) := pure (sexp.list $ xs ++ ys)
| _ _ := monad_fail.fail "sexp.concat failed"

local infix `<+>`:50 := sexp.concat -- TODO(jesse): just write an applicative instance, don't want to think about `seq` now though

meta def sexp.map {α β : Type*} (f : α → β) : sexp α → sexp β
| (sexp.atom x) := (sexp.atom $ f x)
| (sexp.list xs) := (sexp.list $ list.map sexp.map xs)

meta instance : functor sexp :=
{map := λ α β f, sexp.map f}

def mk_type_ascription : sexp string → sexp string → sexp string := λ s₁ s₂, sexp.list [(sexp.atom ":"), s₁, s₂]

-- TODO(jesse): supply version with even more type annotations
meta def sexp_of_expr : (option ℕ) → expr → tactic (sexp string) := λ fuel ex, do {
  match fuel with
  | none := pure ()
  | (some x) := when (x = 0) $ tactic.fail "sexp_of_expr fuel exhausted"
  end,
  match ex with
  | e@(var k) := (sexp.list [sexp.atom "var"]) <+> (sexp.list [sexp.atom (to_string k)])
  | e@(sort l) := (sexp.list [sexp.atom "sort"]) <+> (sexp.list [sexp.atom (to_string l)])
  | e@(const nm ls) := pure $ sexp.atom nm.to_string
  | e@(mvar un pt tp) := do tp_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) tp, pure $ mk_type_ascription (sexp.atom pt.to_string) tp_sexp
  | e@(local_const un pt binder_info tp) := do {
    tp_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) tp,
    -- pure $ flip mk_type_ascription tp_sexp $ sexp.list [sexp.atom pt.to_string] -- note: drop binder info for now
   pure (sexp.atom pt.to_string)
  }
  | e@(app e₁ e₂) := (λ s₁ s₂, sexp.list [s₁, s₂]) <$> sexp_of_expr ((flip nat.sub 1) <$> fuel) e₁ <*> sexp_of_expr ((flip nat.sub 1) <$> fuel) e₂
  -- | e@(app e₁ e₂) := sexp.list <$> ((::) <$> (sexp_of_expr ((flip nat.sub 1) <$> fuel) $ get_app_fn e) <*> (get_app_args e).mmap (sexp_of_expr ((flip nat.sub 1) <$> fuel)))
  | e@(lam var_name b_info var_type body) := do {
    ⟨[b], e'⟩ ← open_n_lambdas e 1,
    sexp.list <$> do {
      b_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) b,
      b_tp_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) var_type,
      body_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) e',
      pure $ [sexp.atom "LAMBDA", mk_type_ascription (b_sexp) b_tp_sexp, body_sexp]
    }
  }
  | e@(pi var_name b_info var_type body) := do {
    ⟨[b], e'⟩ ← open_n_pis e 1,
    sexp.list <$> do {
      b_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) b,
      b_tp_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) var_type,
      body_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) e',
      pure $ [sexp.atom "PI", mk_type_ascription (b_sexp) b_tp_sexp, body_sexp]
    }
  }
  -- reduce let expressions before sexpr serialization
  | e@(elet var_name var_type var_assignment body) := sexp_of_expr ((flip nat.sub 1) <$> fuel) (tmp_reduce_let e)
  | e@(macro md deps) := 
    sexp.list <$> do {
      deps_sexp_list ← sexp.list <$> (deps.mmap $ sexp_of_expr (((flip nat.sub 1) <$> fuel))),
      let deps_sexp := sexp.list [sexp.atom "MACRO_DEPS", deps_sexp_list],
      pure $ [sexp.atom "MACRO", sexp.atom (expr.macro_def_name md).to_string, deps_sexp]
    }
  end
}


end sexp_of_expr
end open_binders

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

-- set the tactic state
meta def set_state (new_state: tactic_state): tactic unit :=
  -- this is in mathlib but easier to recreate
  λ _, interaction_monad.result.success () new_state

meta def tactic_state.to_sexp (ts : tactic_state) : tactic (sexp string) := do
  tactic.write ts,
  do { gs ← tactic.get_goals, guard (gs.length = 1) },
  hyps ← tactic.local_context,
  annotated_hyps ← hyps.mmap (λ h, prod.mk h <$> tactic.infer_type h),
  hyps_sexp ← do {
    hyps_sexps ← annotated_hyps.mmap $ function.uncurry $ λ hc ht, mk_type_ascription <$> sexp_of_expr none hc <*> sexp_of_expr none hc,
    pure $ sexp.list $ [sexp.atom "HYPS"] ++ hyps_sexps
  },
  goal_sexp ← tactic.target >>= sexp_of_expr none,
  pure $ sexp.list [sexp.atom "TACTIC_STATE", hyps_sexp, goal_sexp]
  

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

-- goal stack information
goals <- tactic.get_goals,
trace_data_num "tactic_state" ts_key "goal_count" goals.length,

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
  tactic_state_string ← ((format.to_string ∘ format.flatten ∘ sexp.to_format) <$> tactic_state.to_sexp ts),
  trace_data_string "tactic_state_goal" g_key "goal_pp" tactic_state_string,
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

-- redefined istep to do proof recording
meta def tactic.istep {α : Type u} (line0 col0 : ℕ) (line col : ℕ) (t : tactic α) : tactic unit :=
λ s, (@scope_trace _ line col (λ _, pr.step_and_record line col t s)).clamp_pos line0 line col
--PR END MODIFICATION
