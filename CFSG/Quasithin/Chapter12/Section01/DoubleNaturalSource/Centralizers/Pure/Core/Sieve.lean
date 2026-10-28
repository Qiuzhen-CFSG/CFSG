module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Quotient
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.G2Even.TwoRank
public import Theory.Mathieu.M11.Properties.ThreeInvolutions
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.Mathieu.SmallModuleRanks.M24
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.TwoRankCoarse
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank
public import Theory.SpecificGroups.Held.TwoRank.Intrinsic
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix

/-!
# Rank exclusion of the pure-point component models in dimension five

The central pure point eliminates the centerless and alternating branches
of 1.1.5. The actual image of U in K/O₂(K) has rank eight. Existing intrinsic
rank bounds for PSL₃(4), G₂(4), and all remaining sporadic carriers other than
J₄ exclude those models. Every comparison uses the original quotient and
an actual model equivalence; no new model-order or simplicity premise is used.

The source application discharges the ambient Sylow using the permitted
positive globalW input and retains all three original fusion/closure
conclusions. Its alternative is an actual quasisimple Janko-four cover,
with the residual, moved subgroup, central point line and involution action
still marked. Excluding that alternative and completing dimension four
remain with the assembly owner `qt-d-double-natural-pure-fusion`.
Source: Aschbacher--Smith, 12.1.6, printed p.791; rank table p.356 and
1.1.5(3), pp.501--503. Imported model proofs retain their source attribution.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels

private theorem sporadic_rank_le_seven (name : SporadicName) (hj3 : name ≠ .j3) (hj4 : name ≠ .j4) :
    primeRank 2 name.Carrier ≤ 7 := by
  cases name with
  | m11 =>
    exact (Theory.GroupTheory.primeRank_le_of_injective 2 MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot Sporadic.Mathieu.m11_center_eq_bot)).trans
      (Sporadic.Mathieu.m11_automorphism_twoRank_le_two.trans (by decide))
  | m12 => exact Sporadic.Mathieu.m12_twoRank_le_three.trans (by decide)
  | m22 => exact Sporadic.Mathieu.m22_twoRank_le_four.trans (by decide)
  | m23 => exact Sporadic.Mathieu.m23_twoRank_le_four.trans (by decide)
  | m24 => exact Sporadic.Mathieu.m24_twoRank_le_six.trans (by decide)
  | j2 => exact Sporadic.LeechRelated.J2.primeRank_two_le_seven
  | j3 => exact (hj3 rfl).elim
  | j4 => exact (hj4 rfl).elim
  | hs => exact Sporadic.LeechRelated.HS.twoRank_le_four.trans (by decide)
  | he => exact Held.primeRank_two_le_six.trans (by decide)
  | ru => exact Rudvalis.primeRank_le_six.trans (by decide)

private theorem psl_three_four_rank {Q : Type*} [Group Q] [Finite Q]
    (hm : ClassicalGroup.IsPSL Q 3 4) : primeRank 2 Q = 4 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [primeRank_equiv 2 e]
  exact Matrix.PSL3Even.two_rank F (n := 2) (by decide) hF

private theorem g2_four_rank {Q : Type*} [Group Q] [Finite Q]
    (hm : IsG2At Q 4) : primeRank 2 Q = 6 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [primeRank_equiv 2 e]
  exact Atlas.G2.EvenTwoRank.two_rank F (n := 2) hF

/-- At rank eight, the complete 1.1.5 alternatives with a central involution
leave only the actual Janko-four quotient. -/
theorem model115_of_central_involution_of_eight_le_rank
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K] (a : MulAut K) (hm : ModelAction115 K a)
    (v : K) (hv : v ∈ center K) (hv2 : orderOf v = 2)
    (hr : 8 ≤ primeRank 2 (K ⧸ pCore 2 K)) :
    Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) ∧ TwoCentralInner a := by
  rcases model115_of_central_involution a hm v hv hv2 with ⟨_,hm,_⟩ | ⟨name,hj3,hm,ha⟩
  · rcases hm with hm | hm
    · have := psl_three_four_rank hm
      omega
    · have := g2_four_rank hm
      omega
  · by_cases hj4 : name = .j4
    · subst name
      exact ⟨hm,ha⟩
    · obtain ⟨e⟩ := hm
      let : Finite name.Carrier := Finite.of_equiv (K ⧸ pCore 2 K) e.toEquiv
      have hh := sporadic_rank_le_seven name hj3 hj4
      rw [←primeRank_equiv 2 e] at hh
      omega

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In dimension five the model rank bounds exclude every source alternative
except an actual Janko-four quotient. The marked Sylow is discharged by the
permitted positive globalW input. The Janko-four exclusion remains in this task. -/
theorem doubleNatural_five_pure_conclusions_or_jankoFour_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hW : 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ∀ z : G, orderOf z = 2 → z ∈ centerIn (T : Subgroup G) →
      (B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes) ∨
      ∃ K : Subgroup (B.pointCentralizer w), IsComponent (B.pointCentralizer w) K ∧
        K.Normal ∧ K = componentLayer (B.pointCentralizer w) ∧
        (B.pointResidual w).subgroupOf (B.pointCentralizer w) ≤ K ∧
        B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤ K.map (B.pointCentralizer w).subtype ∧
        (B.naturalSummand ⊔ S.pureDualHyperplane w hp) ⊓
          ((center K).map K.subtype).map (B.pointCentralizer w).subtype = zpowers (w : G) ∧
        center K = pCore 2 K ∧
        Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) ∧
        ∃ a : MulAut K, (∀ x : K, ((a x : B.pointCentralizer w) : G) = z * (x : G) * z⁻¹) ∧
          TwoCentralInner a := by
  let := D.doubledOrbit_elementary h
  intro S hns w hw hp hfix z hz hzT
  have hs : S.MarkedAmbientSylow D.sylow_normalizes_component := by
    intro v hv hpv hfixv
    exact (D.doubleNatural_five_marked_pure_sylow_of_many h hmany B hW S v hv hpv hfixv).2
  rcases D.doubleNatural_pure_component_alternative_of_many h hmany B S hns hs
      w hw hp hfix z hz hzT with hc | ⟨K,hK,_,_,hm⟩
  · exact Or.inl (D.doubleNatural_five_pure_conclusions_of_one_characteristicTwo_of_many
      h hmany B hW S hns w hw hp hc)
  · obtain ⟨hn,hLayer,hX,hU,hZ,hcore,_⟩ := D.doubleNatural_pure_component_models_of_many
      h hmany B S hns hs w hw hp hfix K hK z hm
    have hr := D.doubleNatural_pure_component_quotient_rank_of_many h hmany B S hns hs
      w hw hp hfix K hK
    obtain ⟨v,_,hv,hv2⟩ := S.pure_component_central_point w hw hp K hU
    obtain ⟨a,ha,hm⟩ := hm
    let := hK.2
    obtain ⟨he,hai⟩ := DoubledBranch.SourceModel.model115_of_central_involution_of_eight_le_rank
      a hm v hv hv2 hr
    exact Or.inr ⟨K,hK,hn,hLayer,hX,hU,hZ,hcore,he,a,ha,hai⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
