module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.AmbientSeed
public import CFSG.Quasithin.ChapterD.Section02.JhatRestriction
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.Seed

/-!
# The selected local action's small-three fixed complement

The original centralizing row supplies the faithful solvable local image and
trivial two-core. Its cyclic-starred case restricts to the original Jhat on
the unchanged module. The source Sylow-fixed central seed spans under the
ambient local image, so the normal-subgroup residual-image theorem excludes
the two-core on Jhat's canonical fixed complement. The residual cubic mover
then shows that each noncentral small involution fixes that complement.

This supplies the pre-full-movement D.2.25 input in original 15.1.2. The
ratio-two and five-core alternatives are retained as genuine case inputs;
full Fitting movement of the original module is no longer assumed.

Source: Aschbacher--Smith 15.1.2, first paragraph, printed p.1084, and D.2.25,
printed p.190.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.GroupTheory Stellmacher ChapterD ChapterD.UniqueFactor
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

theorem source_centralizing_smallThree_fixed_complement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let H := Jhat ρ
    let σ := ρ.comp H.subtype
    (∀ A ∈ QhatStar ρ, rank A = 1) → cubicRatio ρ = 2 →
    (∀ A ∈ QhatStar σ, ⁅pCore 5 H,A⁆ = ⊥) →
    ∀ t ∈ smallSupportInvolutions σ,
      letI := BinaryGroupAction.action σ
      let Y := smallSupportGroup H (Multiplicative (Additive (localModule T M))) 1
      t∉centralizer (Y:Set H) → fixedSpace σ Y ≤ fixedSpace σ (zpowers t) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let H := Jhat ρ
  let := source_localAction_isSolvable hG T hempty hM
  let : H.Normal := Jhat_normal ρ
  dsimp only
  intro hrank hq hfive t ht
  have hbound := source_centralizing_cubicRatio_le_two hG T hempty hM hmany hJ
  have hcore := cyclic_Jhat_core ρ (imageRepresentation_injective _ _ _)
    (source_localAction_twoCore hG T hM) hbound hrank
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hbound
  have hqH : cubicRatio (ρ.comp H.subtype) = 2 :=
    (subgroup_starred_transport ρ H ⟨A,hA,le_sSup hA⟩).1.trans hq
  obtain ⟨hfix,hspan⟩ := source_localAction_seed_span hG T hM
  exact hcore.fixed_smallThree_complement_of_ambient_seed ρ H _ _ hfix hspan hfive hqH ht
end CFSG.Quasithin.Chapter15.Section01
