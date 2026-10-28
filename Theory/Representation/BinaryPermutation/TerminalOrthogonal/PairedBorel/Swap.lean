module
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# The group obtained by interchanging two factors

The binary cyclic group acts on A × A by the literal interchange. These
semidirect-product coordinates retain the base inclusion and its conjugation
by the swapping involution. They are used for the paired A₅ orthogonal model
in Aschbacher–Smith, G.11.2(12), printed p.364 (1 March 2004 manuscript).
-/

@[expose] public section
namespace BinaryPermutation.TerminalOrthogonal.PairedBorel
abbrev C2 := Multiplicative (ZMod 2)

def switch (A : Type*) [Group A] : C2 →* MulAut (A × A) where
  toFun c := if c = 1 then 1 else MulEquiv.prodComm
  map_one' := by simp
  map_mul' c d := by
    change ZMod 2 at c d
    fin_cases c <;> fin_cases d <;>
      ext x <;> simp <;> rfl

@[simp] lemma switch_one (A : Type*) [Group A] : switch A 1 = 1 := map_one _
@[simp] lemma switch_other (A : Type*) [Group A] :
    switch A (Multiplicative.ofAdd 1) = MulEquiv.prodComm := by
  simp [switch]

abbrev Swapped (A : Type*) [Group A] := (A × A) ⋊[switch A] C2

instance (A : Type*) [Group A] [Finite A] : Finite (Swapped A) :=
  Finite.of_equiv ((A × A) × C2) SemidirectProduct.equivProd.symm

def base {A : Type*} [Group A] : (A × A) →* Swapped A := SemidirectProduct.inl
def interchange {A : Type*} [Group A] : Swapped A :=
  SemidirectProduct.inr (Multiplicative.ofAdd 1)

@[simp] lemma interchange_sq {A : Type*} [Group A] :
    (interchange : Swapped A) ^ 2 = 1 := by
  rw [interchange, ← map_pow]
  have h : (Multiplicative.ofAdd 1 : C2) ^ 2 = 1 := by decide
  rw [h, map_one]

@[simp] lemma interchange_conj {A : Type*} [Group A] (a b : A) :
    (interchange : Swapped A) * base (a,b) * interchange⁻¹ = base (b,a) := by
  rw [interchange, base, ← map_inv, ← SemidirectProduct.inl_aut, switch_other]
  rfl
def swappedMap {A B : Type*} [Group A] [Group B] (f : A →* B) :
    Swapped A →* Swapped B :=
  SemidirectProduct.map (f.prodMap f) (MonoidHom.id C2) (by
    intro c
    apply MonoidHom.ext
    intro x
    by_cases h : c = 1 <;> simp [switch, h]
    rfl)

@[simp] lemma swappedMap_left {A B : Type*} [Group A] [Group B]
    (f : A →* B) (g : Swapped A) :
    (swappedMap f g).left = (f g.left.1, f g.left.2) := rfl

@[simp] lemma swappedMap_right {A B : Type*} [Group A] [Group B]
    (f : A →* B) (g : Swapped A) : (swappedMap f g).right = g.right := rfl

end BinaryPermutation.TerminalOrthogonal.PairedBorel
