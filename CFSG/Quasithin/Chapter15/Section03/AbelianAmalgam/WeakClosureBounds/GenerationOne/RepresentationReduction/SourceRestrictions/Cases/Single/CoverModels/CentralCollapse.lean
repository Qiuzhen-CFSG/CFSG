module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.LocalSetup
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CentralComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CoverModels.RankOne
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CoverModels.Kernel
public import Theory.SpecificGroups.PSL3.UniversalProjection
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.LargePrimary.Complete
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even

/-!
# Collapse of all single-component central covers

The literal perfect cover from A=KO₂(H)/O₂(H) to its E.2.2 model has kernel
Z(A). The unitary large-prime theorem excludes every prime above three from
this kernel. Preparation excludes two using O₂(A)=1 and excludes the entire
three-part using the original three-prime overlap M∩H. Thus no unitary
three-center survives, without changing PSU₃ to SU₃ or the coefficient field.

For PSL₃ at odd exponent f>1, the actual SL₃ projection is injective and its
proved lifting property dominates the supplied perfect cover. Its kernel
therefore has order one. For Sp₄, the proved trivial universal kernel gives
injectivity of the supplied cover. RankOne already handles PSL₂ and Suzuki,
including the possible Suzuki two-cover. The E.2.2 case split now gives
Z(A)=1 and J=O₂(H) from LocalInput alone.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.2.2,
printed pp.215--216; I.1.1--4, pp.407--408; and 15.3.65, p.1152.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
open BorelReduction SourceCases FFExclusions.ModelRigidity
namespace CoverModels
universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {H M K T Z ZS : Subgroup G} {f : ℕ}
variable [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
variable {a : LocalQuotientAction H (conjugateSpanBy ZS H) Z}
variable {I : Submodule (ZMod 2)
  (Additive ((conjugateSpanBy ZS H) ⧸ Z.subgroupOf (conjugateSpanBy ZS H)))}
variable (h : LocalInput 𝒦 H M K T Z ZS f a I)
include h

/-- The large-prime bound is applied to the literal modelCover, whose kernel
is the actor center. The original overlap hypothesis excludes its whole three-part. -/
theorem psu3_center_eq_bot {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hF : Nat.card F = (2 ^ f) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ f))
    (e : sourceImage H M K ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    center (actorImage H K) = ⊥ := by
  apply center_eq_bot_of_prime_support h
  intro p hp hd
  by_contra hn
  have hp3 : 3 < p := by have := hp.two_le; omega
  have hn := HermitianForm.UniversalCover.EvenKernelBound.LargePrimary.not_dvd_cover_kernel
    J h.source.exponent_gt_one hp hp3 hF hconj (modelCover h e)
  rw [modelCover_ker] at hn
  exact hn hd

/-- The ordinary SL₃ projection lifts onto the actual actor cover. At odd
f>1 its scalar kernel is trivial, so the actor center is trivial as well. -/
theorem psl3_center_eq_bot {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ f)
    (e : sourceImage H M K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :
    center (actorImage H K) = ⊥ := by
  have hf3 : 3 ≤ f := by
    have hf := h.source.exponent_gt_one
    obtain ⟨n, hn⟩ := h.odd
    omega
  have hcard : 8 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hf3
  let c := modelCover h e
  let := c.isPerfect
  obtain ⟨s, hs, _⟩ := Matrix.PSL3.UniversalProjection.existsUnique_projection_lift
    c.toMonoidHom c.surjective c.ker_le_center (by omega) (by omega)
  have hsurj := Matrix.PSL3.projection_lift_surjective F c.toMonoidHom c.ker_le_center s hs
  have hd := kernel_card_dvd_of_surjective_factor (Matrix.PSL3.projection F)
    c.toMonoidHom s hsurj hs
  have hk := (Matrix.PSL3.projection F).ker_eq_bot_iff.mpr
    (psl3Projection_injective_of_odd hF h.odd)
  rw [hk, card_bot] at hd
  apply card_eq_one.mp
  rw [← modelCover_ker h e]
  exact Nat.dvd_one.mp hd

/-- The even Sp₄ universal kernel makes the actual actor cover injective. -/
theorem sp4_center_eq_bot {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ f)
    (e : sourceImage H M K ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    center (actorImage H K) = ⊥ := by
  have hi := (modelCover h e).injective_of_universalProjection_ker_eq_bot
    (Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.universalProjection_ker_eq_bot_of_card_pow
      hF h.source.exponent_gt_one)
  rw [← modelCover_ker h e]
  exact (modelCover h e).toMonoidHom.ker_eq_bot_iff.mpr hi

/-- All three genuine Bender source models have centerless actors. -/
theorem benderModel_center_eq_bot (hm : BenderModel H M K f) :
    center (actorImage H K) = ⊥ := by
  rcases hm with hm | ⟨F, hF, hfin, hc, J, hJ, hf, hcard, hconj, hfix, e, hB⟩
  · exact exchangedModel_center_eq_bot h hm
  · exact psu3_center_eq_bot h J hcard hconj e

/-- Both rank-two source models have centerless actors. The Sp₄′ model is
compared with Sp₄ by the actual derived inclusion. -/
theorem diagramModel_center_eq_bot (hm : DiagramModel H M K T f) :
    center (actorImage H K) = ⊥ := by
  rcases hm with ⟨F, hF, hfin, hc, hf, hcard, e, hB, hd⟩ |
    ⟨F, hF, hfin, hc, hf, hcard, e, hB, hd⟩
  · exact psl3_center_eq_bot h hcard e
  · exact sp4_center_eq_bot h hcard
      (e.trans (spFourDerivedEquiv hcard h.source.exponent_gt_one))

/-- The component in the original H/O₂(H) action is centerless in every
single-component E.2.2 branch, with no additional cover premise. -/
theorem actor_center_eq_bot : center (actorImage H K) = ⊥ := by
  rcases (single_source_cases h.source.cases h.single).2 with hm | hm
  · exact benderModel_center_eq_bot h hm
  · exact diagramModel_center_eq_bot h hm

/-- The original E.2.2 kernel J is exactly O₂(H) in the single-component case. -/
theorem sourceKernel_eq_twoCore : sourceKernel H M = pCore 2 H :=
  sourceKernel_eq_twoCore_of_center_eq_bot h (actor_center_eq_bot h)

end CoverModels
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
