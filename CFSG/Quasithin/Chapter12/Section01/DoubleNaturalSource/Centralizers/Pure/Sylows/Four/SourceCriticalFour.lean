module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.SourceCoreBound
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.SourceLargeDistance

/-!
# The exact distance-four MS setup from the original contrary Sylow source

The actual moved subgroup excludes an abelian commutator core. The corrected
small-displacement argument excludes critical distance greater than four.
Evenness and the genuine nonabelian common facts therefore force distance
four. The final producer constructs the binary input and its setup from the
same original marked point and the contrary ambient Sylow hypothesis.
No MS alternatives, path input, fixation, or recognition callback is assumed.
The distance-four source geometry remains to be excluded.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open ChapterC ChapterC.BinaryMS ChapterC.BinaryMS.MS93
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- Nonabelianness is preserved on the literal binary input carrier. -/
theorem pure_binaryCore_nonabelian
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (hms : SmallMSPair KnownSimple.IsKnownSimple (B.pointResidual w) (B.pointSylow w))
    (e : (B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ¬ IsMulCommutative (commutatorCore
      ((B.pointResidual w).subgroupOf (B.pointResidual w ⊔ B.pointSylow w))) := by
  intro hc
  let := hc
  apply S.pure_msCore_nonabelian hNM hWT hTM w hw hp hms e
  let q := binaryCoreEquiv (B.pointResidual w) (B.pointSylow w)
  exact ⟨⟨fun a b => q.symm.injective (by simp only [map_mul, mul_comm])⟩⟩

include S in
/-- Every actual setup of the original pure-point MS pair has distance four. -/
theorem pure_binary_setup_distance_eq_four
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (hms : SmallMSPair KnownSimple.IsKnownSimple (B.pointResidual w) (B.pointSylow w))
    (e : (B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : InputSetup (hms.binaryInput e)) :
    t.geometry.b t.reduction.radical = 4 := by
  have hc := S.pure_binaryCore_nonabelian hNM hWT hTM w hw hp hms e
  have hupper := S.pure_binary_setup_distance_le_four hNM hWT hTM w hw hp hms e t hc
  obtain ⟨common⟩ := t.commonFacts hc
  have hlower := common.large_distance
  obtain ⟨n, hn⟩ := t.geometry.even (MS93.alpha t.reduction.radical) rfl
  change t.geometry.b t.reduction.radical = n + n at hn
  omega

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open ChapterC ChapterC.BinaryMS ChapterC.BinaryMS.MS93
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- All original marked-point hypotheses produce a genuine nonabelian binary
MS setup at distance four, on the same original point residual and point Sylow. -/
theorem doubleNatural_four_pure_critical_four_source_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      ∃ (hms : SmallMSPair KnownSimple.IsKnownSimple (B.pointResidual w) (B.pointSylow w))
        (e : (B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
        (t : InputSetup (hms.binaryInput e)),
        ¬ IsMulCommutative (commutatorCore
          ((B.pointResidual w).subgroupOf (B.pointResidual w ⊔ B.pointSylow w))) ∧
        t.geometry.b t.reduction.radical = 4 := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  obtain ⟨hms, ⟨e⟩, _⟩ := D.doubleNatural_four_pure_smallMSPair_of_many h hmany B S w hw hp hfix hf
  have hNM := D.doubledOrbit_normalizer_eq h B.orbit_eq
  have hWT := (D.doubledOrbit_E322 h).le_sylow
  have hc := S.pure_binaryCore_nonabelian hNM hWT D.sylow_normalizes_component w hw hp hms e
  obtain ⟨t⟩ := MS93.exists_setup (hms.binaryInput e) hc
  exact ⟨hms, e, t, hc,
    S.pure_binary_setup_distance_eq_four hNM hWT D.sylow_normalizes_component w hw hp hms e t⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
