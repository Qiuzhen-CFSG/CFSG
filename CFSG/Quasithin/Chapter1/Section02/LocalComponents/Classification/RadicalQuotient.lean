module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison

/-!
# The actual radical quotient of a nonquasisimple local component

The two nonquasisimple A.3.6 alternatives give SL₂(p), p>3, above the
Fitting subgroup. Its solvable radical is its center because it is
quasisimple. The radical quotient is consequently PSL₂(p). The equivalence
through a solvable kernel retains the original group quotient, including
the initial quotient by O₂ in local-component applications.

Source: Aschbacher--Smith 13.1.4(3) and the model step of 13.1.8(1),
pp.867--869, from A.3.6, pp.43--45.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
open LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem psl_of_fitting_sl (hc : A36Common G) {p : ℕ}
    (hm : IsSL (G ⧸ fittingSubgroup G) 2 p) :
    ClassicalGroup.IsPSL (G ⧸ solvableRadical G) 2 p := by
  let Q := G ⧸ fittingSubgroup G
  let : IsQuasisimple Q := hc.2.1
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  let : Group.IsSolvable (center Q) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
  have hr : solvableRadical Q = center Q := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical (center Q) inferInstance inferInstance)
  let f := QuotientGroup.mk' (fittingSubgroup G)
  let : Group.IsSolvable f.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let e : (G ⧸ solvableRadical G) ≃* (Q ⧸ center Q) :=
    (solvableRadicalQuotientEquiv f (QuotientGroup.mk'_surjective _)).trans
      (QuotientGroup.quotientMulEquivOfEq hr)
  obtain ⟨F,hF,hfin,hcard,⟨eSL⟩⟩ := hm
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := eSL.injective.nontrivial
  exact ⟨F,hF,hfin,hcard,⟨e.trans
    (IsQuasisimple.centralQuotientEquiv eSL.toMonoidHom eSL.surjective)⟩⟩

/-- The exact radical-quotient model forced by the nonquasisimple A.3.6
alternatives, including the prime bound. -/
theorem radical_quotient_pslTwo_of_a36 {E : Type*} [Group E] [Finite E]
    {C : Subgroup E} (hc : A36Conclusion C) (hn : ¬ IsQuasisimple C) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ClassicalGroup.IsPSL (C ⧸ solvableRadical C) 2 p := by
  have hcases : A36Natural C ∨ A36Nilpotent C := by
    cases hc.1 with
    | simple hC _ _ => exact (hn hC.2).elim
    | cover hC _ _ => exact (hn hC.2).elim
    | natural h => exact Or.inl h
    | nilpotent h => exact Or.inr h
  rcases hcases with hnat | hnil
  · obtain ⟨p,hp,hlarge,F,hF,hfin,hcard,v,e,hact⟩ := hnat.2
    have hm : IsSL (C ⧸ fittingSubgroup C) 2 p :=
      ⟨F,hF,hfin,hcard,⟨(QuotientGroup.quotientMulEquivOfEq hnat.1).symm.trans e⟩⟩
    exact ⟨p,hp,hlarge,psl_of_fitting_sl hc.2 hm⟩
  · have hm : IsSL (C ⧸ fittingSubgroup C) 2 5 := by
      obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hnil.2.2.1
      exact ⟨F,hF,hfin,hcard,⟨(QuotientGroup.quotientMulEquivOfEq hnil.1).symm.trans e⟩⟩
    exact ⟨5,by decide,by decide,psl_of_fitting_sl hc.2 hm⟩

/-- Transport to the original local component, across its actual O₂ quotient
and the actual quotient component inclusion. -/
theorem radical_quotient_pslTwo_of_a36_image {E : Type*} [Group E] [Finite E]
    (L : Subgroup G) {C : Subgroup E} (e : (L ⧸ pCore 2 L) ≃* C)
    (hc : A36Conclusion C) (hn : ¬ IsQuasisimple ((L ⧸ pCore 2 L))) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ClassicalGroup.IsPSL (L ⧸ solvableRadical L) 2 p := by
  have hnC : ¬ IsQuasisimple C := fun h => hn (h.of_mulEquiv e.symm)
  obtain ⟨p,hp,hlarge,hm⟩ := radical_quotient_pslTwo_of_a36 hc hnC
  let f := QuotientGroup.mk' (pCore 2 L)
  let : Group.IsSolvable f.ker := by
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
    infer_instance
  let er : (L ⧸ solvableRadical L) ≃* (C ⧸ solvableRadical C) :=
    (solvableRadicalQuotientEquiv f (QuotientGroup.mk'_surjective _)).trans
      (QuotientGroup.congr _ _ e (map_solvableRadical_equiv e))
  exact ⟨p,hp,hlarge,hm.of_mulEquiv er⟩

end CFSG.Quasithin.Chapter1.Section02
