module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedBinaryThree
public import Theory.AtlasPort.LinearGroups.G2.BinaryAutomorphismTwoNormalizer
public import Theory.SpecificGroups.FFG2DerivedCenter

/-!
# Excluding the binary derived G₂ constrained star

The original normalized residual acts perfectly and nontrivially on the
selected component's core-central quotient. It normalizes the nontrivial
two-group induced by the original radical. If the star were G₂(2)′, the
native automorphism normalizer theorem would make this perfect image
solvable. All images come from the original reciprocal witness, and the
radical image may include outer automorphisms.

Source: Aschbacher--Smith C.4.3--8 and 12.1.11, pp.152--154,794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original constrained star cannot be the binary derived G₂ group. -/
theorem sourceOrbit_binary_witness_constrained_not_binary_g2
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    ¬ Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) := by
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
        Theory.SpecificGroups.g2_derived_two_center_eq_bot)
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
  have hXR : X ≤ normalizer (R.subgroupOf H : Set H) := by
    intro x hx r
    exact hc.span_normalizes_radical (hspan.symm ▸ hx) (r : G)
  have hBY : B ≤ normalizer (Y : Set _) :=
    coreCentralActorImage_normalizes K X (R.subgroupOf H) hXR
  have hY : IsPGroup 2 Y := hc.isRadical.isPGroup.comap_subtype.map _
  have hYne : Y ≠ ⊥ := hc.constrained_radical_action_nontrivial K hK hq hout hfK
  let Y' := Y.map eA.toMonoidHom
  have hY' : Y' ≠ ⊥ := fun hh => hYne ((Y.map_eq_bot_iff_of_injective eA.injective).mp hh)
  let : Group.IsSolvable (normalizer (Y' : Set (MulAut (commutator (Atlas.G2.Model (ZMod 2)))))) :=
    Atlas.G2.BinaryAutomorphismTwoNormalizer.automorphism_normalizer_isSolvable
      Y' hY' (hY.map _)
  have hBN : B.map eA.toMonoidHom ≤ normalizer (Y' : Set (MulAut (commutator (Atlas.G2.Model (ZMod 2))))) :=
    (map_mono hBY).trans (Y.le_normalizer_map _)
  let j : B →* normalizer (Y' : Set (MulAut (commutator (Atlas.G2.Model (ZMod 2))))) := (eA.toMonoidHom.comp B.subtype).codRestrict _
    (fun z => hBN (mem_map_of_mem eA.toMonoidHom z.property))
  have hj : Function.Injective j := fun x y hh =>
    Subtype.ext (eA.injective (congrArg Subtype.val hh))
  exact Group.IsPerfect.not_isSolvable B (Group.isSolvable_of_isSolvable_injective hj)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
