module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedBinaryThree
public import Theory.SpecificGroups.AlternatingSeven.TwoNormalizerSeven
public import Theory.GroupTheory.PerfectSimpleImageKernel
public import Theory.GroupTheory.SimpleSectionOrder

/-!
# Excluding the alternating-seven constrained star

The actual original residual's simple binary-three quotient forces seven
into the order of its nontrivial automorphism image. This image normalizes
the nontrivial two-group induced by the actual radical. Full automorphisms
of A7 have seven-free two-subgroup normalizers, giving a contradiction.
The radical action may include outer automorphisms; no intersection
nontriviality or ambient Sylow containment is assumed.
Source: Aschbacher--Smith C.4.3--8 and 12.1.11, pp.152--154,794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
private instance : IsSimpleGroup BinaryLinearThree.Group := Atlas.Comparisons.Exceptional.sl3Two_simple
private instance : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original constrained star cannot be alternating seven. -/
theorem sourceOrbit_binary_witness_constrained_not_alternating_seven
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    ¬ Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
      alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan := hc.normalized_span_eq hn
  let : Group.IsPerfect LH := by
    have hh := hc.span_perfect
    rwa [hspan] at hh
  let eQ := (coreCentralQuotientCongr
    (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
      (ChapterC.Section04Constrained.source_simple_equiv
        (hc.constrained_source_input K hK hq hout hfK) e
        (alternatingGroup.center_eq_bot (by simp)))
  let eA := MulAut.congr eQ
  let X := LH.subgroupOf H
  let B := coreCentralActorImage K X
  let Y := coreCentralActorImage K (R.subgroupOf H)
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  have hXK : X ≤ normalizer (K : Set H) := by
    simpa only [hspan] using hc.constrained_span_normalizes_intrinsic K hK hq
  let eX : LH ≃* X.subgroupOf (normalizer (K : Set H)) :=
    (subgroupOfEquivOfLe hLH).symm.trans (subgroupOfEquivOfLe hXK).symm
  let b : LH →* B := ((normalizerCoreCentralAction K).subgroupMap
    (X.subgroupOf (normalizer (K : Set H)))).comp eX.toMonoidHom
  have hb : Function.Surjective b :=
    ((normalizerCoreCentralAction K).subgroupMap_surjective _).comp eX.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective hb
  have hB : B ≠ ⊥ := by
    simpa only [hspan] using hc.constrained_span_action_nontrivial K hK hq hout
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hB
  obtain ⟨_,_,_,_,_,_,a,_⟩ := D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))
  have hqs : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 LH := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 LH) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := hqker ▸ inferInstance
  have hbne : b ≠ 1 := by
    intro he
    obtain ⟨z,hz⟩ := exists_ne (1 : B)
    obtain ⟨x,rfl⟩ := hb z
    exact hz (DFunLike.congr_fun he x)
  let : Group.IsSolvable b.ker := solvable_ker_of_nontrivial_hom_of_simple_quotient q hqs b hbne
  have hbcard := SimpleSection.card_dvd_of_solvable_representation
    (Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) q hqs b
  rw [Matrix.PSL3Two.card_SL] at hbcard
  have hseven : 7 ∣ Nat.card B := (by decide : 7 ∣ 168).trans hbcard
  have hXR : X ≤ normalizer (R.subgroupOf H : Set H) := by
    intro x hx r
    exact hc.span_normalizes_radical (hspan.symm ▸ hx) (r : G)
  have hBY : B ≤ normalizer (Y : Set _) :=
    coreCentralActorImage_normalizes K X (R.subgroupOf H) hXR
  have hY : IsPGroup 2 Y := hc.isRadical.isPGroup.comap_subtype.map _
  have hYne : Y ≠ ⊥ := hc.constrained_radical_action_nontrivial K hK hq hout hfK
  let Y' := Y.map eA.toMonoidHom
  have hY' : Y' ≠ ⊥ := fun hh => hYne ((Y.map_eq_bot_iff_of_injective eA.injective).mp hh)
  have hBN : B.map eA.toMonoidHom ≤ normalizer (Y' : Set (MulAut (alternatingGroup (Fin 7)))) :=
    (map_mono hBY).trans (Y.le_normalizer_map _)
  have hsev : 7 ∣ Nat.card (B.map eA.toMonoidHom) := by
    rw [card_map_of_injective eA.injective]
    exact hseven
  exact AlternatingSeven.seven_not_dvd_automorphism_two_normalizer Y' (hY.map _) hY'
    (hsev.trans (card_dvd_of_le hBN))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
