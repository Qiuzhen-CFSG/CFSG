module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import BenderSuzuki.FinalTheorem

/-!
# Three classical generation values in E.1.14(1)

For an SQTK-group with simple generalized Fitting subgroup L and G = LT,
the binary PSL₂, PSU₃ and PSL₃ alternatives have generation parameter
equal to their field exponent. The established upper bounds include the
ambient outer two-extensions, and the actual lower obstructions exclude
every smaller positive value.

The model witnesses retain arbitrary finite coefficient fields and, for
PSU₃, arbitrary nondegenerate Hermitian forms. Explicit field and form
equivalences connect them to the canonical upper-bound models; the unitary
parameter is the fixed-field order. The final source application uses the
original named subgroup L = F*(G). The other E.1.14 families remain separate.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
E.1.14(1), printed p.214 of refs/quasithin.pdf; see the imported upper-bound
and lower-obstruction modules for their local calculations.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical
variable {G : Type*} [Group G] [Finite G]

/-- The PSL₂ value, with the standard simple-group parameter range. -/
theorem generationParameter_eq_of_isPSL2 {K : GroupClass} (hG : IsSQTK K G)
    [IsSimpleGroup (generalizedFitting G)] {f : ℕ} (hf : 2 ≤ f)
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hm : ClassicalGroup.IsPSL (generalizedFitting G) 2 (2 ^ f)) :
    generationParameter G = f := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite (GaloisField 2 f)
  have hg : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let ef : F ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hc.trans hg.symm)
  exact parameter_eq_of_upper_and_predecessor (by omega)
    (not_odd_card_of_isPSL2 _ hf ⟨F, inferInstance, inferInstance, hc, ⟨e⟩⟩)
    (RankOneUpper.isEGenerated_of_psl2 hG hf T hgen (e.trans (Atlas.fieldEquivPSL 2 ef)))
    (fun _ => not_isEGenerated_of_psl2 hf hc e)

/-- The PSU₃ value, retaining the arbitrary Hermitian model and its fixed field. -/
theorem generationParameter_eq_of_isPSU3 {K : GroupClass} (hG : IsSQTK K G)
    [IsSimpleGroup (generalizedFitting G)] {f : ℕ} (hf : 2 ≤ f)
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hm : ClassicalGroup.IsPSU (generalizedFitting G) 3 (2 ^ f)) :
    generationParameter G = f := by
  obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := hm
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 f (by omega) hc hconj
  let J' := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨e1⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2 ^ f) hc hfixed
  obtain ⟨e2⟩ := projectiveSpecialUnitary_equiv_psu3Model J' f hf rfl hc hfixed
  have hm' : ClassicalGroup.IsPSU (generalizedFitting G) 3 (2 ^ f) :=
    ⟨F, inferInstance, inferInstance, J, hc, hconj, ⟨e⟩⟩
  exact parameter_eq_of_upper_and_predecessor (by omega)
    (not_odd_card_of_isPSU3 _ (by omega) hm')
    (RankOneUpper.isEGenerated_of_psu3 hG hf T hgen (e.trans (e1.trans e2)))
    (fun _ => not_isEGenerated_of_isPSU3 T hf hm')

/-- The PSL₃ value, including the binary endpoint and graph extensions. -/
theorem generationParameter_eq_of_isPSL3 {K : GroupClass} (hG : IsSQTK K G)
    [IsSimpleGroup (generalizedFitting G)] {f : ℕ} (hf : 0 < f)
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hm : ClassicalGroup.IsPSL (generalizedFitting G) 3 (2 ^ f)) :
    generationParameter G = f := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hm
  exact parameter_eq_of_upper_and_predecessor hf
    (not_odd_card_of_isPSL3 _ hf ⟨F, inferInstance, inferInstance, hc, ⟨e⟩⟩)
    (RankTwoUpper.LinearThree.isEGenerated_of_source hG e T hf hc hgen)
    (fun hh => not_isEGenerated_of_psl3 hh hc e)
/-- Application to the original E.1.14 source subgroup and all three marked
classical alternatives. No generation, field-identification or outer-action
premise remains. -/
theorem source_classical_value {K : GroupClass} (hG : IsSQTK K G)
    (L : Subgroup G) (hL : L = generalizedFitting G) [IsSimpleGroup L]
    (T : Sylow 2 G) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    {f : ℕ}
    (hm : (2 ≤ f ∧ ClassicalGroup.IsPSL L 2 (2 ^ f)) ∨
      (2 ≤ f ∧ ClassicalGroup.IsPSU L 3 (2 ^ f)) ∨
      (0 < f ∧ ClassicalGroup.IsPSL L 3 (2 ^ f))) :
    generationParameter G = f := by
  subst L
  rcases hm with ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩
  · exact generationParameter_eq_of_isPSL2 hG hf T hgen hm
  · exact generationParameter_eq_of_isPSU3 hG hf T hgen hm
  · exact generationParameter_eq_of_isPSL3 hG hf T hgen hm

end CFSG.Quasithin.ChapterE.ValuesEvenClassical
