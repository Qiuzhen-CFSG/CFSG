module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.SmallModelExclusion.Local
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicRecognition
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ThreeObstruction
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility

/-!
# Excluding the actual binary derived G₂ carrier

The component intersection has a nontrivial two-core. The checked octonion
hexagon places its normalizer in a root parabolic, and Sylow conjugacy aligns
the subgroup with a standard marking. At field order two neither restricted
parabolic has order divisible by nine, contradicting the full source shadow.
The full octonion group and its commutator subgroup remain distinct throughout.

Source: Aschbacher--Smith, initial parabolic selection, printed p.1139;
the binary local geometry also occurs in the proof of 1.3.4, p.511.
The imported octonion conventions and calculations are from the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
open SmallModelExclusion
variable {G : Type*} [Group G] [Finite G]
variable {L MI Y S : Subgroup G} [L.Normal]
private instance component_normal : (centralizerQuotientComponent L).Normal :=
  (inferInstance : L.Normal).map (centralizerQuotientMap L) (QuotientGroup.mk'_surjective _)

/-- The binary octonion-derived model is incompatible with the local selection inputs. -/
theorem Setup.not_g2_derived (d : Setup L MI Y S)
    (hm : Nonempty (centralizerQuotientComponent L ≃*
      commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  obtain ⟨e⟩ := hm
  let H := (MI.map (centralizerQuotientMap L)).subgroupOf (centralizerQuotientComponent L)
  obtain ⟨Q, hQ⟩ := local_sylow d.quotient_local
  obtain ⟨f, i, _, hplace⟩ :=
    Atlas.G2.SylowParabolicRecognition.exists_aligned_parabolic_of_twoCore e Q H hQ
      (local_core_ne_bot d.quotient_local (quotient_two d))
  have hd : 9 ∣ Nat.card (Atlas.G2.SylowParabolicRecognition.rootParabolic (F := ZMod 2) i) := by
    have h9 : 9 ∣ Nat.card (H.map f.toMonoidHom) := by
      rw [card_map_of_injective f.injective]
      exact local_nine d.quotient_local (quotient_two d)
    exact h9.trans (card_dvd_of_le hplace)
  fin_cases i
  · apply Atlas.G2.BinaryParabolicPair.ThreeObstruction.derived_first_nine_not_dvd
    simpa [Atlas.G2.SylowParabolicRecognition.rootParabolic,
      Atlas.G2.LieParabolicSetup.parabolic₁_binary,
      Atlas.G2.BinaryParabolicPair.derivedFirst] using hd
  · apply Atlas.G2.BinaryParabolicPair.ThreeObstruction.derived_second_nine_not_dvd
    simpa [Atlas.G2.SylowParabolicRecognition.rootParabolic,
      Atlas.G2.BinaryParabolicPair.derivedSecond, Atlas.G2.BinaryCore.secondParabolic,
      Atlas.G2.BinaryParabolicPair.DerivedModel, Atlas.G2.LieParabolicSetup.parabolic₂] using hd


end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
