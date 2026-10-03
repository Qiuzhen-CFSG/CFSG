module

public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Proof-producing coset enumeration

This is a small checker for expanded Todd–Coxeter certificates. A fact `(i,w,j)`
means `rep i * eval w = h * rep j` for some `h` in the subgroup. Representatives
are immutable words, with representative zero the empty word. The untrusted
enumerator may use any union-find implementation: a merger is an empty-word
fact, transferring an edge is composition, and conflicting edges give a merger
by prefix cancellation. Thus no union-find invariant is assumed by the checker.

Relator loops may be inverted and cyclically rotated. A two-ended scan expands
into composition, reversal and prefix cancellation. Each rule refers only to
previous checked facts. `run_sound` also accepts an already certified database,
so large certificates can be checked in separate chunks. `certified_edge`
exports the actual subgroup-witness equation, not merely a permutation model.

The calculus is the usual right-coset form of the Todd–Coxeter method
(Todd and Coxeter, *A practical method for enumerating cosets of a finite
abstract group*, Proc. Edinburgh Math. Soc. 5 (1936), 26–34).
-/

@[expose] public section

namespace Theory.GroupTheory.CosetEnumeration

abbrev Letter (α : Type*) := α × Bool
abbrev Word (α : Type*) := List (Letter α)

def flip {α : Type*} (a : Letter α) : Letter α := (a.1, !a.2)

def inverse {α : Type*} (w : Word α) : Word α := (w.map flip).reverse

def letterValue {α G : Type*} [Group G] (g : α → G) (a : Letter α) : G :=
  if a.2 then g a.1 else (g a.1)⁻¹

def eval {α G : Type*} [Group G] (g : α → G) (w : Word α) : G :=
  (w.map (letterValue g)).prod

@[simp] theorem eval_nil {α G : Type*} [Group G] (g : α → G) : eval g [] = 1 := rfl

@[simp] theorem eval_singleton {α G : Type*} [Group G] (g : α → G) (a : Letter α) :
    eval g [a] = letterValue g a := by simp [eval]

@[simp] theorem eval_append {α G : Type*} [Group G] (g : α → G) (u v : Word α) :
    eval g (u ++ v) = eval g u * eval g v := by simp [eval]

@[simp] theorem letterValue_flip {α G : Type*} [Group G] (g : α → G) (a : Letter α) :
    letterValue g (flip a) = (letterValue g a)⁻¹ := by
  rcases a with ⟨a, b⟩
  cases b <;> simp [letterValue, flip]

@[simp] theorem eval_inverse {α G : Type*} [Group G] (g : α → G) (w : Word α) :
    eval g (inverse w) = (eval g w)⁻¹ := by
  simp [inverse, eval, List.map_reverse, List.map_map, List.prod_inv_reverse,
    Function.comp_def]

def variant {α : Type*} (w : Word α) (inv : Bool) (offset : Nat) : Word α :=
  (if inv then inverse w else w).rotate offset

theorem eval_variant {α G : Type*} [Group G] (g : α → G) (w : Word α)
    (hw : eval g w = 1) (inv : Bool) (offset : Nat) :
    eval g (variant w inv offset) = 1 := by
  have h : eval g (if inv then inverse w else w) = 1 := by
    cases inv <;> simp [hw]
  simpa [eval, variant, List.map_rotate] using
    List.prod_rotate_eq_one_of_prod_eq_one h offset

/-- Immutable input data. Generator labels need not be consecutive integers. -/
structure Input (α : Type*) where
  reps : Array (Word α)
  relators : Array (Word α)
  subgroup : List (Letter α)
  deriving DecidableEq, Repr

def representative {α G : Type*} [Group G] (g : α → G) (input : Input α) (i : Nat) : G :=
  eval g (input.reps.getD i [])

/-- The mathematical hypotheses of a certificate; there are no recognition or
permutation-action assumptions. -/
structure Models {α G : Type*} [Group G] (g : α → G) (H : Subgroup G)
    (input : Input α) : Prop where
  zero : input.reps.getD 0 [] = []
  relators : ∀ w ∈ input.relators, eval g w = 1
  subgroup : ∀ a ∈ input.subgroup, letterValue g a ∈ H

structure Fact (α : Type*) where
  start : Nat
  word : Word α
  stop : Nat
  deriving DecidableEq, Repr

def Related {G : Type*} [Group G] (H : Subgroup G) (x y : G) : Prop :=
  ∃ h ∈ H, x = h * y

theorem Related.refl {G : Type*} [Group G] (H : Subgroup G) (x : G) : Related H x x :=
  ⟨1, H.one_mem, (one_mul x).symm⟩

theorem Related.symm {G : Type*} [Group G] {H : Subgroup G} {x y : G}
    (h : Related H x y) : Related H y x := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a⁻¹, H.inv_mem ha, by simp⟩

theorem Related.trans {G : Type*} [Group G] {H : Subgroup G} {x y z : G}
    (h : Related H x y) (k : Related H y z) : Related H x z := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := k
  exact ⟨a * b, H.mul_mem ha hb, (mul_assoc _ _ _).symm⟩

theorem Related.mul_right {G : Type*} [Group G] {H : Subgroup G} {x y : G}
    (h : Related H x y) (z : G) : Related H (x * z) (y * z) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, ha, mul_assoc _ _ _⟩

def Fact.Valid {α G : Type*} [Group G] (g : α → G) (H : Subgroup G)
    (input : Input α) (f : Fact α) : Prop :=
  Related H (representative g input f.start * eval g f.word)
    (representative g input f.stop)

theorem Fact.valid_refl {α G : Type*} [Group G] (g : α → G) (H : Subgroup G)
    (input : Input α) (i : Nat) : (Fact.mk i [] i).Valid g H input := by
  simpa [Fact.Valid] using Related.refl H (representative g input i)

/-- A fresh representative is justified by its literal defining word. This
interface also permits direct proof-DAG emission instead of reducing `run`. -/
theorem Fact.valid_define {α G : Type*} [Group G] (g : α → G) (H : Subgroup G)
    (input : Input α) (i : Nat) (a : Letter α) (j : Nat)
    (definition : input.reps.getD i [] ++ [a] = input.reps.getD j []) :
    (Fact.mk i [a] j).Valid g H input := by
  change Related H (eval g (input.reps.getD i []) * eval g [a])
    (eval g (input.reps.getD j []))
  rw [← eval_append, definition]
  exact Related.refl H _

theorem Fact.valid_subgroup {α G : Type*} [Group G] {g : α → G} {H : Subgroup G}
    {input : Input α} (model : Models g H input) (a : Letter α)
    (ha : a ∈ input.subgroup) : (Fact.mk 0 [a] 0).Valid g H input := by
  refine ⟨letterValue g a, model.subgroup a ha, ?_⟩
  simp [representative, model.zero]

theorem Fact.valid_relator {α G : Type*} [Group G] {g : α → G} {H : Subgroup G}
    {input : Input α} (model : Models g H input) (i : Nat) (w : Word α)
    (hw : w ∈ input.relators) (inv : Bool) (offset : Nat) :
    (Fact.mk i (variant w inv offset) i).Valid g H input := by
  have he := eval_variant g w (model.relators w hw) inv offset
  simpa [Fact.Valid, he] using Related.refl H (representative g input i)

theorem Fact.valid_reverse {α G : Type*} [Group G] {g : α → G} {H : Subgroup G}
    {input : Input α} {f : Fact α} (h : f.Valid g H input) :
    (Fact.mk f.stop (inverse f.word) f.start).Valid g H input := by
  have := (h.mul_right (eval g f.word)⁻¹).symm
  simpa [Fact.Valid, mul_assoc] using this

theorem Fact.valid_trans {α G : Type*} [Group G] {g : α → G} {H : Subgroup G}
    {input : Input α} {f k : Fact α} (h : f.Valid g H input) (hk : k.Valid g H input)
    (he : f.stop = k.start) :
    (Fact.mk f.start (f.word ++ k.word) k.stop).Valid g H input := by
  have hh := h.mul_right (eval g k.word)
  rw [he] at hh
  simpa [Fact.Valid, mul_assoc] using hh.trans hk

/-- Cancelling a known prefix is the scan inference and the conflict inference.
In particular, equal labelled edges from one vertex identify their endpoints. -/
theorem Fact.valid_cancel {α G : Type*} [Group G] {g : α → G} {H : Subgroup G}
    {input : Input α} {f k : Fact α} (h : f.Valid g H input) (hk : k.Valid g H input)
    (hs : f.start = k.start) (v : Word α) (hw : f.word ++ v = k.word) :
    (Fact.mk f.stop v k.stop).Valid g H input := by
  have hh := h.symm.mul_right (eval g v)
  rw [hs, mul_assoc, ← eval_append, hw] at hh
  exact hh.trans hk

/-- All references are zero-based indices into the previous fact database.
The `define` rule checks literal representative words, so a fabricated `new`
event cannot introduce an assumption. `cancel p q v` checks `p.word ++ v = q.word`.
-/
inductive Rule (α : Type*) where
  | refl (i : Nat)
  | define (i : Nat) (a : Letter α) (j : Nat)
  | subgroup (a : Letter α)
  | relator (i r : Nat) (inv : Bool) (offset : Nat)
  | reverse (p : Nat)
  | trans (p q : Nat)
  | cancel (p q : Nat) (v : Word α)
  deriving DecidableEq, Repr

/-- Executable local checker. Failed references and failed side conditions reject. -/
def derive {α : Type*} [DecidableEq α] (input : Input α) (db : Array (Fact α)) :
    Rule α → Option (Fact α)
  | .refl i => some ⟨i, [], i⟩
  | .define i a j =>
      input.reps[i]?.bind fun u =>
      input.reps[j]?.bind fun v =>
      if u ++ [a] = v then some ⟨i, [a], j⟩ else none
  | .subgroup a => if a ∈ input.subgroup then some ⟨0, [a], 0⟩ else none
  | .relator i r inv offset =>
      input.relators[r]?.bind fun w =>
      some ⟨i, variant w inv offset, i⟩
  | .reverse p =>
      db[p]?.bind fun f =>
      some ⟨f.stop, inverse f.word, f.start⟩
  | .trans p q =>
      db[p]?.bind fun f =>
      db[q]?.bind fun k =>
      if f.stop = k.start then some ⟨f.start, f.word ++ k.word, k.stop⟩ else none
  | .cancel p q v =>
      db[p]?.bind fun f =>
      db[q]?.bind fun k =>
      if f.start = k.start ∧ f.word ++ v = k.word then some ⟨f.stop, v, k.stop⟩ else none

def ValidDB {α G : Type*} [Group G] (g : α → G) (H : Subgroup G)
    (input : Input α) (db : Array (Fact α)) : Prop :=
  ∀ f ∈ db, f.Valid g H input

theorem derive_sound {α G : Type*} [DecidableEq α] [Group G]
    {g : α → G} {H : Subgroup G} {input : Input α} (model : Models g H input)
    {db : Array (Fact α)} (valid : ValidDB g H input db)
    {rule : Rule α} {f : Fact α} (checked : derive input db rule = some f) :
    f.Valid g H input := by
  cases rule with
  | refl i =>
      simp only [derive, Option.some.injEq] at checked
      subst f
      exact Fact.valid_refl g H input i
  | define i a j =>
      simp only [derive, Option.bind_eq_some_iff] at checked
      obtain ⟨u, hu, v, hv, h⟩ := checked
      split at h
      next he =>
        simp only [Option.some.injEq] at h
        subst f
        have ui : input.reps.getD i [] = u := by simp [Array.getD_eq_getD_getElem?, hu]
        have vj : input.reps.getD j [] = v := by simp [Array.getD_eq_getD_getElem?, hv]
        exact Fact.valid_define g H input i a j (by rw [ui, vj, he])
      next => simp at h
  | subgroup a =>
      simp only [derive] at checked
      split at checked
      next ha =>
        simp only [Option.some.injEq] at checked
        subst f
        exact Fact.valid_subgroup model a ha
      next => simp at checked
  | relator i r inv offset =>
      simp only [derive, Option.bind_eq_some_iff, Option.some.injEq] at checked
      obtain ⟨w, hw, rfl⟩ := checked
      exact Fact.valid_relator model i w (Array.mem_of_getElem? hw) inv offset
  | reverse p =>
      simp only [derive, Option.bind_eq_some_iff, Option.some.injEq] at checked
      obtain ⟨k, hk, rfl⟩ := checked
      exact Fact.valid_reverse (valid k (Array.mem_of_getElem? hk))
  | trans p q =>
      simp only [derive, Option.bind_eq_some_iff] at checked
      obtain ⟨k, hk, l, hl, h⟩ := checked
      split at h
      next he =>
        simp only [Option.some.injEq] at h
        subst f
        exact Fact.valid_trans (valid k (Array.mem_of_getElem? hk))
          (valid l (Array.mem_of_getElem? hl)) he
      next => simp at h
  | cancel p q v =>
      simp only [derive, Option.bind_eq_some_iff] at checked
      obtain ⟨k, hk, l, hl, h⟩ := checked
      split at h
      next he =>
        simp only [Option.some.injEq] at h
        subst f
        exact Fact.valid_cancel (valid k (Array.mem_of_getElem? hk))
          (valid l (Array.mem_of_getElem? hl)) he.1 v he.2
      next => simp at h

/-- Replay a chunk, appending each justified fact. The empty database is `#[]`. -/
def run {α : Type*} [DecidableEq α] (input : Input α) :
    List (Rule α) → Array (Fact α) → Option (Array (Fact α))
  | [], db => some db
  | r :: rs, db =>
      (derive input db r).bind fun f =>
      run input rs (db.push f)

theorem run_sound {α G : Type*} [DecidableEq α] [Group G]
    {g : α → G} {H : Subgroup G} {input : Input α} (model : Models g H input)
    (rules : List (Rule α)) {db out : Array (Fact α)}
    (valid : ValidDB g H input db) (checked : run input rules db = some out) :
    ValidDB g H input out := by
  induction rules generalizing db with
  | nil =>
      simp only [run, Option.some.injEq] at checked
      subst out
      exact valid
  | cons r rs ih =>
      simp only [run, Option.bind_eq_some_iff] at checked
      obtain ⟨f, hf, hrun⟩ := checked
      apply ih (db := db.push f) _ hrun
      intro k hk
      rcases Array.mem_push.mp hk with hk | rfl
      · exact valid k hk
      · exact derive_sound model valid hf

theorem empty_valid {α G : Type*} [Group G] (g : α → G) (H : Subgroup G)
    (input : Input α) : ValidDB g H input #[] := by
  simp [ValidDB]

theorem ValidDB.edge {α G : Type*} [Group G] {g : α → G} {H : Subgroup G}
    {input : Input α} {db : Array (Fact α)} (valid : ValidDB g H input db)
    {n i j : Nat} {a : Letter α} (edge : db[n]? = some ⟨i, [a], j⟩) :
    ∃ h ∈ H, representative g input i * letterValue g a = h * representative g input j := by
  simpa [Fact.Valid, Related] using valid _ (Array.mem_of_getElem? edge)

/-- Read a certified final edge as an equation in the actual group. -/
theorem certified_edge {α G : Type*} [DecidableEq α] [Group G]
    {g : α → G} {H : Subgroup G} {input : Input α} (model : Models g H input)
    (rules : List (Rule α)) {out : Array (Fact α)}
    (checked : run input rules #[] = some out) {n i j : Nat} {a : Letter α}
    (edge : out[n]? = some ⟨i, [a], j⟩) :
    ∃ h ∈ H, representative g input i * letterValue g a = h * representative g input j := by
  exact (run_sound model rules (empty_valid g H input) checked).edge edge

@[simp] theorem flip_flip {α : Type*} (a : Letter α) : flip (flip a) = a := by
  rcases a with ⟨a, b⟩
  cases b <;> rfl

/-- A complete table with inverse columns gives generator permutations.
This construction is independent of soundness: use certified edges as well
when identifying these permutations with right multiplication on actual cosets. -/
def tablePermutation {α X : Type*} (table : X → Letter α → X)
    (inverseTable : ∀ i a, table (table i a) (flip a) = i) (a : Letter α) : Equiv.Perm X where
  toFun i := table i a
  invFun i := table i (flip a)
  left_inv i := inverseTable i a
  right_inv i := by simpa using inverseTable i (flip a)

end Theory.GroupTheory.CosetEnumeration
