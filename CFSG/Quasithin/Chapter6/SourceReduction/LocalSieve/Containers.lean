module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.Components
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityPointBinary

/-!
# The actual containing component and its normal Sylow orbit

Source 1.2.4 embeds the E.2.2 seed uniquely in a component of the given Y.
The one-or-two-conjugate theorem makes its entire T-orbit normal in Y.
If this orbit equalled the original residual, Y would normalize that
residual, contradicting Cartan escape. This proves proper enlargement
without assuming that either the seed or its container is T-invariant.

Source: Aschbacher--Smith, 1.2.1(3), 1.2.4 and 5.1.12--13, pp.504--505,635--636.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

/-- The source containing component may move under T. Its whole T-orbit
is nevertheless normal in Y, and escape forces that orbit to enlarge O²(H). -/
theorem containing_orbit_normal_and_strict
    {T : Sylow 2 G} {H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTH : (T : Subgroup G) ≤ H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent)
    (hR : residual H ≤ componentOrbit (C.map Y.subtype) (T : Subgroup G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
      residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) := by
  have hTY := hTH.trans hY.2
  have hc : ((C.map Y.subtype).subgroupOf Y).IsCComponent := by
    change (C.map Y.subtype |>.comap Y.subtype).IsCComponent
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hC
  have hn := Chapter1.Section02.MovedMaximalityPoint.relative_sylow_orbit_normalized
    hG (map_subtype_le C) hY.1
    (show Chapter1.IsSylowIn 2 (T : Subgroup G) Y from
      ⟨T.subtype hTY, by
        simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTY]⟩) hc
  rw [conjugateSpanBy_eq_iSup_conj] at hn
  change Y ≤ normalizer (componentOrbit (C.map Y.subtype) (T : Subgroup G) : Set G) at hn
  have hle : componentOrbit (C.map Y.subtype) (T : Subgroup G) ≤ Y :=
    (componentOrbit_le_sup _ _).trans (sup_le (map_subtype_le C) hTY)
  refine ⟨(normal_subgroupOf_iff_le_normalizer hle).mpr hn,
    lt_of_le_of_ne hR ?_⟩
  intro he
  apply hescape
  rw [he]
  exact inf_le_right.trans hn

/-- The unique containing component and its proper normal orbit are constructed
in the original overgroup, without identifying a moved seed with its residual. -/
theorem exists_escape_seed_embedding {T : Sylow 2 G} {M H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hgen : 1 < ChapterE.generationParameter H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃! C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal := by
  obtain ⟨K, hKH, hK, hq, hg, hl, ho, C, hc, hu⟩ :=
    exists_seed_embedding hG hTM hH hgen hY
  obtain ⟨hn, hlt⟩ := containing_orbit_normal_and_strict hG hH.1.1.2 hY C hc.1 hc.2.2 hescape
  exact ⟨K, hKH, hK, hq, hg, hl, ho, C, ⟨hc.1, hc.2.1, hlt, hn⟩,
    fun D hd => hu D ⟨hd.1, hd.2.1, hd.2.2.1.le⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
