module
public import Theory.Representation.SU3.ProjectiveBinaryDegree
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryScalarDerived
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryScalarDerived
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryDerived
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.SmallSpecialUnitary
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.SmallProjectiveUnitary

/-!
# Projective bounds for scalar-fixed crossed root sections

A scalar-fixed invariant section containing a nonidentity element of the
crossed unitary root is moved by the unitary reflection. Source effectiveness
then gives a faithful action of the literal PSU3 panel quotient on its
Frattini section. The odd-degree projective bound gives order at least
2^(8b). At b=1 the nine-point panel argument gives the same bound for both
the special and projective full actors.

This extends the scalar-derived argument to the actual center used in
Fong--Seitz I (6F), printed p.47. The internal import-all edges reuse the
checked reflection and degree-one arguments without changing their APIs.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The actual scalar-fixed crossed section has the projective eight-b bound,
including the nonperfect degree-one actors. -/
theorem unitary_scalar_crossed_section_card_bound
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hodd : Odd b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hroot : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (hsmall : b=1 → Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
      Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (d : RootSection Q split j) (hden : d.denominator=⊥)
    (hd : d.numerator ≤ centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D)))
    (a : rootAt Q split j (Q.simple i)) (ha : a ≠ 1)
    (hax : (a : X ⧸ Q.D) ∈ d.numerator) :
    2^(8*b) ≤ Nat.card d.EffectiveCarrier := by
  have hmove := cross_root_moves_section Q split hm i j hij
    (UnitarySource.actorReflection Q split j) d hden a a.property hax
      (fun he => ha (Subtype.ext he))
  by_cases he : b=1
  · have hc : Nat.card F=4 := by simpa only [he,pow_one,Nat.reducePow] using hcard
    have hj : ∀ x,J.conj x=x^2 := by simpa only [he,pow_one] using hconj
    have hr : Nat.card (simpleRoot Q split j)=8 := by
      simpa only [he,pow_one,Nat.reducePow] using hroot
    have hp : Nat.card (Panel Q j)=9 := by
      have he := singleton_parabolic_root_index Q split j
      change Nat.card (Panel Q j)=1+Nat.card (simpleRoot Q split j) at he
      omega
    have hbound : 256 ≤ Nat.card d.EffectiveCarrier := by
      rcases hsmall he with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
      · obtain ⟨hT,hcenter⟩ := small_special_cartan Q split j J hc hj hKj ν hr
        have hR : Nat.card (rankOne Q split j)=216 := (Nat.card_congr ν.toEquiv).trans
          (HermitianForm.SmallThreeCore.special_group_card J hc hj)
        obtain ⟨hsol,hc,hfree⟩ := central_nine_panel_structure Q split j hKj hR hcenter hr
        let := hsol
        exact (small_scalar_section_kernel_and_bound Q split j hKj d hd hp hc hfree
          (small_special_section_not_two Q split j hT.le hcenter hr hm i hij
            (UnitarySource.actorReflection Q split j) d hden a ha hax)).2
      · let := HermitianForm.FixedFieldTwo.projective_isSolvable J hc hj
        let : Group.IsSolvable (rankOne Q split j) :=
          Group.isSolvable_of_surjective (f:=ν.symm.toMonoidHom) ν.symm.surjective
        have hR : Nat.card (rankOne Q split j)=72 := (Nat.card_congr ν.toEquiv).trans
          (HermitianForm.FixedFieldTwo.card_projective J hc hj)
        obtain ⟨hsol,hc,hfree⟩ := nine_actor_structure Q split j hR hr
        let := hsol
        exact (small_scalar_section_kernel_and_bound Q split j hKj d hd hp hc hfree
          (nine_section_action_not_two Q split j hR hr hm i hij
            (UnitarySource.actorReflection Q split j) d hden a ha hax)).2
    simpa only [he,mul_one,Nat.reducePow] using hbound
  · have hk : d.effectiveAction.ker=(RootLocalCover.projection Q split j).ker := by
      apply le_antisymm
      · rw [RootLocalCover.projection_ker]
        exact unitary_section_effective Q split j J (by omega) hcard hconj σ hσ hKj μ d hmove
      · intro r hr
        have hz := RootLocalCover.projection_ker_central Q split j hr
        have hn : d.numeratorAction r=1 := scalar_section_kernel Q split j d hd hz
        ext z
        induction z using QuotientGroup.induction_on with
        | H z => rw [d.effectiveAction_mk,hn]; rfl
    let π := μ.toMonoidHom.comp (RootLocalCover.projection Q split j)
    have hπ : Function.Surjective π := μ.surjective.comp
      (RootLocalCover.central_odd_cover Q split j hKj).1
    have hkπ : π.ker=d.effectiveAction.ker := by
      rw [hk]
      ext r
      exact μ.map_eq_one_iff
    let γ : ProjectiveSpecialUnitaryMatrixGroup J →* MulAut d.EffectiveCarrier :=
      π.liftOfSurjective hπ ⟨d.effectiveAction,hkπ.le⟩
    have hg (r) : γ (π r)=d.effectiveAction r := MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
    have hγ : Function.Injective γ := by
      apply γ.ker_eq_bot_iff.mp
      apply eq_bot_iff.mpr
      intro z hz
      obtain ⟨r,rfl⟩ := hπ z
      exact hkπ.symm.le (show d.effectiveAction r=1 from (hg r).symm.trans hz)
    let ρ := Representation.FrattiniAction.ofAutomorphismHom γ
    have hρ : Function.Injective ρ := by
      intro r t he
      apply hγ
      ext x
      exact Additive.ofMul.injective (congrArg
        (fun a : Module.End (ZMod 2) (Additive d.EffectiveCarrier) => a (Additive.ofMul x)) he)
    have hdim := Representation.SU3.ProjectiveBinaryDegree.finrank_ge
      J (by omega) hodd hcard hconj ρ hρ
    have hsize := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive d.EffectiveCarrier)
    simp only [Nat.card_zmod] at hsize
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hdim).trans_eq hsize.symm

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
