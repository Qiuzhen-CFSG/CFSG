module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFactorAction

/-!
# Generic special-unitary covers from the original regular factor

The original factor quotient is identified with the canonical root actor by
the regular whole-cover comparison. For an SU3 quotient its inverse gives
a surjective SU3 map; for a PSU3 quotient compose that inverse with the
actual scalar projection. The factor-action comparison proves the literal
projective square in both cases. No perfectness or restriction q > 2 is
used, so this constructs the cover also at the nonperfect binary parameter.

QuadrangleStructure.UnitaryFactor uses this map to discharge the cover
premise of the all-fields (6A)(c) structure theorem. RegularUnitaryApplications
applies it to the literal Chapter 12 pair. The (2B) containment remains a
premise here; global exclusion of the affine exception is separate.
Source: Fong--Seitz I (5B)--(5C), (6A)(c); AS F.1.1--3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 0 < n) (hE : Nat.card E = (2^n)^2)
  (hconj : ∀ x, J.conj x = x^(2^n))
  (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)

include e h hn hE hconj hV in
/-- The original special-or-projective quotient constructs the actual SU3
cover, including the nonperfect binary case and the literal projective square. -/
theorem regular_unitary_cover_of_factor
    (hfactor : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ ν : localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      ∃ π : J.specialSubgroup →* rankOne Q split i,
        Function.Surjective π ∧
        ∀ a, ν (RootLocalCover.projection Q split i (π a)) = J.specialToProjective a := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  rcases hfactor with hs | hp
  · obtain ⟨f⟩ := hs
    have hs := specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hE hconj f
    let a := (regularFactorRootEquiv Q e h split i T hT hV hs).trans f
    let b := specialUnitaryFactorLocalEquiv Q e h split i T hT J hn hE hconj hV f
    refine ⟨b,a.symm.toMonoidHom,a.symm.surjective,?_⟩
    intro x
    have he := factorQuotientLocalMap_regularRoot Q e h split i T hT hV hs (a.symm x)
    simp only [MulEquiv.coe_toMonoidHom]
    rw [←he]
    change specialUnitaryFactorLocalEquiv Q e h split i T hT J hn hE hconj hV f _ = _
    rw [specialUnitaryFactorLocalEquiv_factor]
    change J.specialToProjective (a (a.symm x)) = _
    rw [a.apply_symm_apply]
  · obtain ⟨f⟩ := hp
    have hs := projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hE hconj f
    let a := (regularFactorRootEquiv Q e h split i T hT hV hs).trans f
    let b := projectiveUnitaryFactorLocalEquiv Q e h split i T hT J hn hE hconj hV f
    refine ⟨b,a.symm.toMonoidHom.comp J.specialToProjective,
      a.symm.surjective.comp J.specialToProjective_surjective,?_⟩
    intro x
    have he := factorQuotientLocalMap_regularRoot Q e h split i T hT hV hs
      (a.symm (J.specialToProjective x))
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
    rw [←he]
    change projectiveUnitaryFactorLocalEquiv Q e h split i T hT J hn hE hconj hV f _ = _
    rw [projectiveUnitaryFactorLocalEquiv_factor]
    exact a.apply_symm_apply _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
