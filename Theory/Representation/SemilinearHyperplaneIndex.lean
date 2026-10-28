module

public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Card

/-!
# Fixed indices on subspaces of semilinear binary modules

A nontrivial semilinear action over the field of four elements has fixed
index at least four on every field-subspace of dimension at least two on
which it acts nontrivially. The subspace need not be invariant: its fixed
vectors are defined by pulling back the ambient fixed space.

If every actor is field-linear, this pullback is a proper field-subspace.
Otherwise a scalar moved by a field twist embeds two copies of the fixed
space into the original subspace, forcing the square of the fixed index
to be at least its cardinality.

Source application: the hyperplane restriction in the reciprocal critical
seed comparison of MS93 (3.3)--(3.4), printed pp. 867--868.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender

namespace Representation
variable {G F V : Type*} [Group G] [Field F]
  [Algebra (ZMod 2) F] [AddCommGroup V] [Module F V]
  [Module (ZMod 2) V] [IsScalarTower (ZMod 2) F V] [Finite V]

/-- Nontrivial semilinear movement on a field-subspace of dimension at least
two forces fixed index at least four. No invariance of the subspace is needed. -/
theorem four_le_submodule_fixed_quotient_card_of_semilinear
    (hF : Nat.card F = 4) (ρ : Representation (ZMod 2) G V)
    (A : Subgroup G) (P : Submodule F V) (hdim : 2 ≤ Module.finrank F P)
    (hsemi : ∀ a ∈ A, ∃ σ : F ≃+* F,
      ∀ c v, ρ a (c • v) = σ c • ρ a v)
    (hmove : ∃ a ∈ A, ∃ v : P, ρ a (v : V) ≠ (v : V)) :
    4 ≤ Nat.card (P ⧸ (fixedSpace ρ A).comap (P.restrictScalars (ZMod 2)).subtype) := by
  classical
  let D := (fixedSpace ρ A).comap (P.restrictScalars (ZMod 2)).subtype
  change 4 ≤ Nat.card (P ⧸ D)
  by_cases hlin : ∀ a ∈ A, ∀ (c : F) v, ρ a (c • v) = c • ρ a v
  · let C : Submodule F P :=
      { carrier := fun v : P => v ∈ D
        zero_mem' := D.zero_mem
        add_mem' := D.add_mem
        smul_mem' := by
          intro c v hv a
          change ρ a.val (c • (v : V)) = c • (v : V)
          rw [hlin a.val a.property]
          exact congrArg (c • ·) (hv a) }
    have hC : D = C.restrictScalars (ZMod 2) := rfl
    have hproper : C ≠ ⊤ := by
      intro he
      obtain ⟨a, ha, v, hv⟩ := hmove
      have hvC : v ∈ C := by rw [he]; trivial
      exact hv (hvC ⟨a, ha⟩)
    have hpositive : 1 ≤ Module.finrank F (P ⧸ C) := by
      have := Submodule.finrank_lt hproper
      have := C.finrank_quotient_add_finrank
      omega
    have hcard : Nat.card (P ⧸ D) = Nat.card (P ⧸ C) := by
      rw [hC]
      exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) C).toEquiv
    rw [hcard, Module.natCard_eq_pow_finrank (K := F), hF]
    exact Nat.pow_le_pow_right (by decide : 0 < 4) hpositive
  · push Not at hlin
    obtain ⟨a, ha, c, v, hcv⟩ := hlin
    obtain ⟨σ, hσ⟩ := hsemi a ha
    have hc : σ c ≠ c := by
      intro he
      exact hcv (by rw [hσ, he])
    let f : D × D → P := fun p => p.1.val + c • p.2.val
    have hi : Function.Injective f := by
      rintro ⟨v, w⟩ ⟨v', w'⟩ he
      have heV := congrArg (fun x : P => (x : V)) he
      change (v.val : V) + c • (w.val : V) = (v'.val : V) + c • (w'.val : V) at heV
      have hh : c • ((w.val : V) - (w'.val : V)) = (v'.val : V) - (v.val : V) := by
        rw [smul_sub]
        exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa only [add_comm] using heV)
      have hh' := congrArg (ρ a) hh
      have hv : ρ a (v.val : V) = (v.val : V) := v.property ⟨a, ha⟩
      have hv' : ρ a (v'.val : V) = (v'.val : V) := v'.property ⟨a, ha⟩
      have hw : ρ a (w.val : V) = (w.val : V) := w.property ⟨a, ha⟩
      have hw' : ρ a (w'.val : V) = (w'.val : V) := w'.property ⟨a, ha⟩
      rw [hσ, map_sub, map_sub, hv, hv', hw, hw', ← hh] at hh'
      have hz : (σ c - c) • ((w.val : V) - (w'.val : V)) = 0 := by
        rw [sub_smul, hh', sub_self]
      have hww : w = w' := Subtype.ext (Subtype.ext (sub_eq_zero.mp
        ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc))))
      have hvv : v = v' := by
        change v.val + c • w.val = v'.val + c • w'.val at he
        rw [hww] at he
        exact Subtype.ext (add_right_cancel he)
      exact Prod.ext hvv hww
    have hsq : Nat.card D ^ 2 ≤ Nat.card P := by
      simpa only [Nat.card_prod, pow_two] using Nat.card_le_card_of_injective f hi
    have hmul : Nat.card D * Nat.card (P ⧸ D) = Nat.card P := by
      exact (Submodule.card_eq_card_quotient_mul_card D).symm
    have hfixpos : 0 < Nat.card D := Nat.card_pos
    have hle : Nat.card D ≤ Nat.card (P ⧸ D) := by
      rw [← hmul, pow_two] at hsq
      exact Nat.le_of_mul_le_mul_left hsq hfixpos
    have hlarge : 16 ≤ Nat.card P := by
      rw [Module.natCard_eq_pow_finrank (K := F), hF]
      exact Nat.pow_le_pow_right (by decide : 0 < 4) hdim
    have hbound := Nat.mul_le_mul_right (Nat.card (P ⧸ D)) hle
    rw [hmul] at hbound
    nlinarith
end Representation
