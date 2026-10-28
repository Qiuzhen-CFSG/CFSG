module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Rules

/-!
# Compact replay of group-word equalities

Each database entry is an actual equality of group words. Expressions compose
normalization in both directions, cyclic variants, products, substitution and
congruence. A reference is accepted only when its index precedes the current
entry. Single-use intermediate expressions need no stored word table.

`verify_sound` proves soundness of a checked block from a certified prefix.
`verifyInputs_sound` connects the literal input words to their presentation.
All computation checks syntax; the group meaning is proved using `Rules`.
This calculus checks the selected Held M₁ Tietze trace. See `source/README.md`
for provenance and John Bray's retained ATLAS source.
-/

@[expose] public section

open Theory.GroupTheory.CosetEnumeration
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Replay

abbrev Fact := Word Nat × Word Nat
abbrev Database := Nat → Fact

def Holds {G : Type*} [Group G] (g : Nat → G) (f : Fact) : Prop :=
  eval g f.1 = eval g f.2

def ValidBefore {G : Type*} [Group G] (g : Nat → G) (db : Database) (n : Nat) : Prop :=
  ∀ i, i < n → Holds g (db i)

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
  | .fact i rev => if i < n then some (if rev then ((db i).2, (db i).1) else db i) else none
  | .same w => some (w, w)
  | .symm r => (derive db n r).map fun f => (f.2, f.1)
  | .norm r inv off => do
      let f ← derive db n r
      if f.2 == [] then some (normalize f.1 inv off, []) else none
  | .denorm w inv off r => do
      let f ← derive db n r
      if f.2 == [] && normalize w inv off == f.1 then some (w, []) else none
  | .trans r s => do
      let f ← derive db n r
      let e ← derive db n s
      if f.2 == e.1 then some (f.1, e.2) else none
  | .append r s => do
      let f ← derive db n r
      let e ← derive db n s
      some (f.1 ++ e.1, f.2 ++ e.2)
  | .eqrel u v r => do
      let f ← derive db n r
      if f.2 == [] && f.1 == u ++ inverse v then some (u, v) else none
  | .congr rs => join db n rs
  | .subst a r eqn => do
      let f ← derive db n r
      let e ← derive db n eqn
      if e.1 == [(a, true)] then some (substitute a e.2 f.1, f.2) else none
  | .variant r inv off => do
      let f ← derive db n r
      if f.2 == [] then some (variant f.1 inv off, []) else none

def join (db : Database) (n : Nat) : List Expr → Option Fact
  | [] => some ([], [])
  | r :: rs => do
      let f ← derive db n r
      let fs ← join db n rs
      return (f.1 ++ fs.1, f.2 ++ fs.2)

end

mutual
theorem derive_sound {G : Type*} [Group G] {g : Nat → G} {db : Database} {n : Nat}
    (h : ValidBefore g db n) (s : Expr) {f : Fact} (hf : derive db n s = some f) :
    Holds g f := by
  cases s with
  | same w => cases hf; rfl
  | symm r =>
    simp only [derive, Option.map_eq_some_iff] at hf
    obtain ⟨x, hx, rfl⟩ := hf
    exact (derive_sound h r hx).symm
  | fact i rev =>
    simp only [derive] at hf
    split at hf
    · rename_i hi
      cases rev <;> simp only [Bool.false_eq_true, ↓reduceIte] at hf <;> cases hf
      · exact h i hi
      · exact (h i hi).symm
    · contradiction
  | norm r inv off =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, hf⟩ := hf
    split at hf <;> try contradiction
    rename_i hc
    have hc' : x.2 = [] := by simpa using hc
    cases hf
    apply normalize_sound g
    simpa only [Holds, hc', eval_nil] using derive_sound h r hx
  | denorm w inv off r =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, hf⟩ := hf
    split at hf <;> try contradiction
    rename_i hc
    have hc' : x.2 = [] ∧ normalize w inv off = x.1 := by simpa using hc
    cases hf
    apply relation_of_denormalize g inv off hc'.2
    simpa only [Holds, hc'.1, eval_nil] using derive_sound h r hx
  | trans r s =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, y, hy, hf⟩ := hf
    split at hf <;> try contradiction
    rename_i hc
    have hc' : x.2 = y.1 := by simpa using hc
    cases hf
    exact (derive_sound h r hx).trans (hc' ▸ derive_sound h s hy)
  | append r s =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, y, hy, hf⟩ := hf
    cases hf
    exact eval_congr_append g (derive_sound h r hx) (derive_sound h s hy)
  | eqrel u v r =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, hf⟩ := hf
    split at hf <;> try contradiction
    rename_i hc
    have hc' : x.2 = [] ∧ x.1 = u ++ inverse v := by simpa using hc
    cases hf
    apply equality_of_relation g u v
    simpa only [Holds, hc'.1, hc'.2, eval_nil] using derive_sound h r hx
  | congr rs => exact join_sound h rs hf
  | subst a r eqn =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, y, hy, hf⟩ := hf
    split at hf <;> try contradiction
    rename_i hc
    have hc' : y.1 = [(a, true)] := by simpa using hc
    cases hf
    have he : g a = eval g y.2 := by
      simpa only [Holds, hc', eval_singleton, letterValue, if_true] using derive_sound h eqn hy
    exact (substitute_sound g a y.2 x.1 he).trans (derive_sound h r hx)
  | variant r inv off =>
    simp only [derive, Bind.bind, Option.bind_eq_some_iff] at hf
    obtain ⟨x, hx, hf⟩ := hf
    split at hf <;> try contradiction
    rename_i hc
    have hc' : x.2 = [] := by simpa using hc
    cases hf
    apply eval_variant g
    simpa only [Holds, hc', eval_nil] using derive_sound h r hx

termination_by sizeOf s

theorem join_sound {G : Type*} [Group G] {g : Nat → G} {db : Database} {n : Nat}
    (h : ValidBefore g db n) (rs : List Expr) {f : Fact} (hf : join db n rs = some f) :
    Holds g f := by
  cases rs with
  | nil => cases hf; rfl
  | cons r rs =>
    simp only [join, Bind.bind, Option.bind_eq_some_iff, Option.pure_def] at hf
    obtain ⟨x, hx, y, hy, hf⟩ := hf
    cases hf
    exact eval_congr_append g (derive_sound h r hx) (join_sound h rs hy)

termination_by sizeOf rs
end

def check (db : Database) (n : Nat) (s : Expr) : Bool :=
  derive db n s == some (db n)

theorem check_sound {G : Type*} [Group G] {g : Nat → G} {db : Database} {n : Nat}
    (h : ValidBefore g db n) (s : Expr) (hc : check db n s = true) : Holds g (db n) :=
  derive_sound h s (by simpa only [check, beq_iff_eq] using hc)

def verify (db : Database) : Nat → List Expr → Bool
  | _, [] => true
  | n, s :: ss => check db n s && verify db (n + 1) ss

theorem verify_sound {G : Type*} [Group G] {g : Nat → G} {db : Database} {n : Nat}
    (h : ValidBefore g db n) (ss : List Expr) (hc : verify db n ss = true) :
    ValidBefore g db (n + ss.length) := by
  induction ss generalizing n with
  | nil => simpa using h
  | cons s ss ih =>
    have hc' : check db n s = true ∧ verify db (n + 1) ss = true := by simpa [verify] using hc
    have hn : ValidBefore g db (n + 1) := by
      intro i hi
      by_cases hin : i < n
      · exact h i hin
      · have he : i = n := by omega
        subst i
        exact check_sound h s hc'.1
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih hn hc'.2

/-- Check the literal initial word table against the supplied presentation. -/
def verifyInputs {α : Type*} (db : Database) (input : α → Word Nat) :
    Nat → List α → Bool
  | _, [] => true
  | n, r :: rs => (db n == (input r, [])) && verifyInputs db input (n + 1) rs

theorem verifyInputs_sound {α G : Type*} [Group G] {g : Nat → G} {db : Database}
    {input : α → Word Nat} (hi : ∀ r, eval g (input r) = 1) {n : Nat}
    (h : ValidBefore g db n) (rs : List α) (hc : verifyInputs db input n rs = true) :
    ValidBefore g db (n + rs.length) := by
  induction rs generalizing n with
  | nil => simpa using h
  | cons r rs ih =>
    have hc' : db n = (input r, []) ∧ verifyInputs db input (n + 1) rs = true := by
      simpa only [verifyInputs, Bool.and_eq_true, beq_iff_eq] using hc
    have hn : ValidBefore g db (n + 1) := by
      intro i hi'
      by_cases hin : i < n
      · exact h i hin
      · have he : i = n := by omega
        subst i
        simpa only [hc'.1, Holds, eval_nil] using hi r
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih hn hc'.2

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Replay
