module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison.Rules

/-!
# Checked replay with central binary tails

Each fact asserts `eval lhs = eval rhs * tail mask`. Every operation checks
both its literal words and its tail. References must precede the current row;
substitution counts both signs of the replaced generator. The soundness proof
uses the central-involution rules and does not assume any mask evaluates to one.

Adapted from the existing M₁ Tietze replay. Source of the words: John Bray,
ATLAS `HeG1-P1.M`, retained in `Held/Model/Source/`.
-/

@[expose] public section

open Theory.GroupTheory.CosetEnumeration
open Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer
namespace Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison.Replay

structure Fact where
  lhs : Word Nat
  rhs : Word Nat
  mask : Mask
  deriving DecidableEq
abbrev Database := Nat → Fact

def Holds {G : Type*} [Group G] (t : Tails G) (g : Nat → G) (f : Fact) : Prop :=
  eval g f.lhs = eval g f.rhs * t.val f.mask

def ValidBefore {G : Type*} [Group G] (t : Tails G) (g : Nat → G) (db : Database) (n : Nat) : Prop :=
  ∀ i, i < n → Holds t g (db i)

inductive Expr where
  | fact (i : Nat) (rev : Bool := false)
  | same (w : Word Nat)
  | symm (r : Expr)
  | norm (r : Expr) (inv : Bool) (offset : Nat)
  | denorm (w : Word Nat) (inv : Bool) (offset : Nat) (r : Expr)
  | trans (r s : Expr)
  | append (r s : Expr)
  | eqrel (u v : Word Nat) (r : Expr)
  | congr (rs : List Expr)
  | subst (a : Nat) (r eqn : Expr)
  | variant (r : Expr) (inv : Bool) (offset : Nat)

mutual
def derive (db : Database) (n : Nat) : Expr → Option Fact
  | .fact i rev => if i < n then some (if rev then ⟨(db i).rhs, (db i).lhs, (db i).mask⟩ else db i) else none
  | .same w => some ⟨w, w, 0⟩
  | .symm r => (derive db n r).map fun f => ⟨f.rhs, f.lhs, f.mask⟩
  | .norm r inv off => do
      let f ← derive db n r
      if f.rhs == [] then some ⟨normalize f.lhs inv off, [], f.mask⟩ else none
  | .denorm w inv off r => do
      let f ← derive db n r
      if f.rhs == [] && normalize w inv off == f.lhs then some ⟨w, [], f.mask⟩ else none
  | .trans r s => do
      let f ← derive db n r
      let e ← derive db n s
      if f.rhs == e.lhs then some ⟨f.lhs, e.rhs, mxor f.mask e.mask⟩ else none
  | .append r s => do
      let f ← derive db n r
      let e ← derive db n s
      some ⟨f.lhs ++ e.lhs, f.rhs ++ e.rhs, mxor f.mask e.mask⟩
  | .eqrel u v r => do
      let f ← derive db n r
      if f.rhs == [] && f.lhs == u ++ inverse v then some ⟨u, v, f.mask⟩ else none
  | .congr rs => join db n rs
  | .subst a r eqn => do
      let f ← derive db n r
      let e ← derive db n eqn
      if e.lhs == [(a, true)] then some ⟨substitute a e.rhs f.lhs, f.rhs, mxor (substMask a e.mask f.lhs) f.mask⟩ else none
  | .variant r inv off => do
      let f ← derive db n r
      if f.rhs == [] then some ⟨variant f.lhs inv off, [], f.mask⟩ else none

def join (db : Database) (n : Nat) : List Expr → Option Fact
  | [] => some ⟨[], [], 0⟩
  | r :: rs => do
      let f ← derive db n r
      let fs ← join db n rs
      return ⟨f.lhs ++ fs.lhs, f.rhs ++ fs.rhs, mxor f.mask fs.mask⟩

end

mutual
theorem derive_sound {G : Type*} [Group G] {t : Tails G} {g : Nat → G} {db : Database} {n : Nat}
    (h : ValidBefore t g db n) (s : Expr) {f : Fact} (hf : derive db n s = some f) :
    Holds t g f := by
  cases s with
  | same w => cases hf; exact (mul_one _).symm.trans (congrArg (eval g w * ·) t.zero.symm)
  | symm r =>
    simp only [derive, Option.map_eq_some_iff] at hf
    obtain ⟨x, hx, rfl⟩ := hf
    exact tail_symm t (derive_sound h r hx)
  | fact i rev =>
    simp only [derive] at hf
    split at hf
    · rename_i hi
      cases rev <;> simp only [Bool.false_eq_true, ↓reduceIte] at hf <;> cases hf
      · exact h i hi
      · exact tail_symm t (h i hi)
    · contradiction
  | norm r inv off =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, hf⟩ := hf
    split at hf <;> try contradiction
    rename_i hc
    have hc' : x.rhs = [] := by simpa using hc
    cases hf
    simp only [Holds, eval_nil, one_mul]
    apply (normalize_tail_iff t g _ _ _ _).mpr
    simpa only [Holds, hc', eval_nil, one_mul] using derive_sound h r hx
  | denorm w inv off r =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, hf⟩ := hf
    split at hf <;> try contradiction
    rename_i hc
    have hc' : x.rhs = [] ∧ normalize w inv off = x.lhs := by simpa using hc
    cases hf
    simp only [Holds, eval_nil, one_mul]
    apply (normalize_tail_iff t g _ _ _ _).mp
    rw [hc'.2]
    simpa only [Holds, hc'.1, eval_nil, one_mul] using derive_sound h r hx
  | trans r s =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, y, hy, hf⟩ := hf
    split at hf <;> try contradiction
    rename_i hc
    have hc' : x.rhs = y.lhs := by simpa using hc
    cases hf
    exact tail_trans t (derive_sound h r hx) (hc' ▸ derive_sound h s hy)
  | append r s =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, y, hy, hf⟩ := hf
    cases hf
    simpa only [Holds, eval_append] using tail_append t (derive_sound h r hx) (derive_sound h s hy)
  | eqrel u v r =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, hf⟩ := hf
    split at hf <;> try contradiction
    rename_i hc
    have hc' : x.rhs = [] ∧ x.lhs = u ++ inverse v := by simpa using hc
    cases hf
    apply eqrel_tail t g u v
    simpa only [Holds, hc'.1, hc'.2, eval_nil, one_mul] using derive_sound h r hx
  | congr rs => exact join_sound h rs hf
  | subst a r eqn =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, y, hy, hf⟩ := hf
    split at hf <;> try contradiction
    rename_i hc
    have hc' : y.lhs = [(a, true)] := by simpa using hc
    cases hf
    have he : g a = eval g y.rhs * t.val y.mask := by
      simpa only [Holds, hc', eval_singleton, letterValue, if_true] using derive_sound h eqn hy
    exact tail_trans t (substitute_tail t g a y.rhs x.lhs y.mask he) (derive_sound h r hx)
  | variant r inv off =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, hf⟩ := hf
    split at hf <;> try contradiction
    rename_i hc
    have hc' : x.rhs = [] := by simpa using hc
    cases hf
    simp only [Holds, eval_nil, one_mul]
    apply (variant_tail_iff t g _ _ _ _).mpr
    simpa only [Holds, hc', eval_nil, one_mul] using derive_sound h r hx

termination_by sizeOf s

theorem join_sound {G : Type*} [Group G] {t : Tails G} {g : Nat → G} {db : Database} {n : Nat}
    (h : ValidBefore t g db n) (rs : List Expr) {f : Fact} (hf : join db n rs = some f) :
    Holds t g f := by
  cases rs with
  | nil => cases hf; simp [Holds, t.zero]
  | cons r rs =>
    simp only [join, Bind.bind, Option.bind_eq_some_iff, Option.pure_def] at hf
    obtain ⟨x, hx, y, hy, hf⟩ := hf
    cases hf
    simpa only [Holds, eval_append] using tail_append t (derive_sound h r hx) (join_sound h rs hy)

termination_by sizeOf rs
end

def check (db : Database) (n : Nat) (s : Expr) : Bool :=
  derive db n s == some (db n)

theorem check_sound {G : Type*} [Group G] {t : Tails G} {g : Nat → G} {db : Database} {n : Nat}
    (h : ValidBefore t g db n) (s : Expr) (hc : check db n s = true) : Holds t g (db n) :=
  derive_sound h s (by simpa only [check, beq_iff_eq] using hc)

def verify (db : Database) : Nat → List Expr → Bool
  | _, [] => true
  | n, s :: ss => check db n s && verify db (n + 1) ss

theorem verify_sound {G : Type*} [Group G] {t : Tails G} {g : Nat → G} {db : Database} {n : Nat}
    (h : ValidBefore t g db n) (ss : List Expr) (hc : verify db n ss = true) :
    ValidBefore t g db (n + ss.length) := by
  induction ss generalizing n with
  | nil => simpa using h
  | cons s ss ih =>
    have hc' : check db n s = true ∧ verify db (n + 1) ss = true := by simpa [verify] using hc
    have hn : ValidBefore t g db (n + 1) := by
      intro i hi
      by_cases hin : i < n
      · exact h i hin
      · have he : i = n := by omega
        subst i
        exact check_sound h s hc'.1
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih hn hc'.2

/-- Check literal inputs, including their central masks, against a source table. -/
def verifyInputs {α : Type*} (db : Database) (input : α → Fact) :
    Nat → List α → Bool
  | _, [] => true
  | n, r :: rs => (db n == input r) && verifyInputs db input (n + 1) rs

theorem verifyInputs_sound {α G : Type*} [Group G] {t : Tails G} {g : Nat → G} {db : Database}
    {input : α → Fact} (hi : ∀ r, Holds t g (input r)) {n : Nat}
    (h : ValidBefore t g db n) (rs : List α) (hc : verifyInputs db input n rs = true) :
    ValidBefore t g db (n + rs.length) := by
  induction rs generalizing n with
  | nil => simpa using h
  | cons r rs ih =>
    have hc' : db n = input r ∧ verifyInputs db input (n + 1) rs = true := by
      simpa only [verifyInputs, Bool.and_eq_true, beq_iff_eq] using hc
    have hn : ValidBefore t g db (n + 1) := by
      intro i hi'
      by_cases hin : i < n
      · exact h i hin
      · have he : i = n := by omega
        subst i
        simpa only [hc'.1] using hi r
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih hn hc'.2

end Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison.Replay
