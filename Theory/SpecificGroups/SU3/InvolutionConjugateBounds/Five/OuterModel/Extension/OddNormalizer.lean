module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.Extension.OddNormalizer.Realization
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.Extension.OddNormalizer.Transport

/-!
# The projective odd Frobenius normalizer in PSU₃(5)

The existing Suzuki matrices realize A₇ in the projective special-unitary
image over the explicit quadratic field of order 25. A checked basis change
and a checked unitary matrix make Frobenius invert every Suzuki generator,
which is precisely the action of the odd permutation `(0 1)`. Coefficient
transport carries both the embedding and that unitary matrix to the literal
`concreteForm`, while intertwining its specified entrywise automorphism.

The construction proves `ProjectiveOddNormalizer` with no additional
premises. Its consumer is
`OuterModel.Extension.concrete_extension_of_projective_odd_normalizer`.
Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11.
-/

public noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer
open Equiv OddNormalizer
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A unitary Frobenius twist realizes an odd permutation on an actual A₇
subgroup of the specified projective matrix group. -/
theorem projective_odd_normalizer : ProjectiveOddNormalizer := by
  intro _ _
  obtain ⟨f, hf, hact⟩ := exists_field_intertwining
  let : Fintype (GaloisField 5 (2 * 1)) := Fintype.ofFinite _
  let e : Embedding.F25 ≃+* GaloisField 5 (2 * 1) := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Embedding.F25.card]
    exact (GaloisField.card 5 (2 * 1) (by decide)).symm)
  have hc (x : Embedding.F25) : e (fieldForm.conj x) = concreteForm.conj (e x) := by
    change e (Embedding.F25.conjugation x) = _
    rw [Embedding.F25.conjugation_eq_fifth, concreteForm_conj, map_pow]
  have hform : fieldForm.form.map e = concreteForm.form := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fieldForm, concreteForm, OddPrimeSylow.NormalizedOuter.FormTransport.standardForm]
  let c := coefficientEquiv e fieldForm concreteForm hc hform
  let u := coefficientUnitary e fieldForm concreteForm hc hform intertwiner
  have hγ : MulAut.congr c fieldActor = concreteActor :=
    IsEntrywiseConjugation.unique concreteForm
      (coefficientEquiv_entrywise e fieldForm concreteForm hc hform fieldActor fieldActor_entrywise)
      concreteActor_entrywise
  have htwist : MulAut.congr c fieldTwist = concreteForm.unitaryConj u * concreteActor := by
    change MulAut.congr c (fieldForm.unitaryConj intertwiner * fieldActor) = _
    rw [map_mul, coefficientEquiv_unitaryConj, hγ]
  refine ⟨c.toMonoidHom.comp f, u, swap 0 1, c.injective.comp hf, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup]
    decide
  · intro q
    rw [← htwist]
    change c (fieldTwist (c.symm (c (f q)))) = c (f ((MulAut.conjNormal (swap 0 1)) q))
    rw [MulEquiv.symm_apply_apply, hact]

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer
