module

public import BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.CharP.Frobenius

/-!
# The fixed matrix model U₆(2)

We take the image of SU₆ in PGL over GF(4), preserving the identity
Hermitian matrix with conjugation x ↦ x². Thus the parameter 2 denotes
the fixed field, and this is the projective group, not its central cover.
Finiteness follows from the surjection from the finite matrix group.

This fixes the target for the Fischer involution-centralizer sections in
GLS3, Tables 5.3t--v (`refs/KGroup/GLS3/Chapter5(sec3-).tex`). No simplicity,
rank, or centralizer identification is asserted by this construction.
-/

@[expose] public section

namespace Theory.SpecificGroups.U6Two

open BenderSuzuki.MatrixGroups

/-- The matrix field has order four. -/
abbrev Field := GaloisField 2 2

theorem field_card : Nat.card Field = 4 := by
  simpa using GaloisField.card 2 2 (by decide)

/-- The nontrivial field involution. -/
noncomputable def conjugation : Field ≃+* Field := frobeniusEquiv Field 2

theorem conjugation_apply (x : Field) : conjugation x = x ^ 2 := rfl

theorem conjugation_involutive : Function.Involutive conjugation := by
  intro x
  let := Fintype.ofFinite Field
  rw [conjugation_apply, conjugation_apply, ← pow_mul]
  have hc : Fintype.card Field = 4 := by
    simpa only [Nat.card_eq_fintype_card] using field_card
  simpa only [hc] using FiniteField.pow_card x

/-- The standard nondegenerate six-dimensional Hermitian form over GF(4). -/
noncomputable def form : HermitianForm 6 Field where
  conj := conjugation
  conj_involutive := conjugation_involutive
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

/-- The actual projective special unitary matrix group U₆(2). -/
noncomputable abbrev Carrier : Type := ProjectiveSpecialUnitaryMatrixGroup form

/-- The canonical map from the special unitary group to its projective image. -/
noncomputable def project : form.specialSubgroup →* Carrier :=
  (Matrix.ProjGenLinGroup.mk.comp form.specialSubgroup.subtype).codRestrict _
    (fun a => ⟨a.val, a.property, rfl⟩)

theorem project_surjective : Function.Surjective project := by
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

instance carrierFinite : Finite Carrier := by
  let : Finite (GL (Fin 6) Field) := Finite.of_injective Units.val Units.val_injective
  exact Finite.of_surjective project project_surjective

end Theory.SpecificGroups.U6Two
