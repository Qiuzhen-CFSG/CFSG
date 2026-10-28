module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalCartan
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.GroupTheory.SolvableResidual

/-!
# The original seed and its containing local component

The shared H-star preparation makes the original H a nonsolvable minimal
parabolic. E.2.2 supplies a C-component inside H. Its Sylow orbit is exactly
the embedded two-residual: perfectness gives one inclusion, and the orbit's
normality and two-group quotient give the other. Source A.3.12 then embeds
the seed uniquely in a C-component of the actual local overgroup Y.

No normalization of the seed by T is assumed. The paired case is retained,
and the containing component's T-orbit contains the entire residual. Once
the residual itself belongs to the local family, source 1.2.4 gives a normal
containing component. Cartan escape rules out equality with the residual.
The remaining embedding/model exclusions are not asserted here.

Source: Aschbacher--Smith, E.2.2 and 5.1.10--13, printed pp.215--216,634--637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem orbit_eq_residual {E : Type*} [Group E] [Finite E]
    (S : Sylow 2 E) (K : Subgroup E) [Group.IsPerfect K]
    (hgen : K ⊔ (S : Subgroup E) = ⊤) :
    componentOrbit K (S : Subgroup E) = pResidual 2 E := by
  have hK : K ≤ pResidual 2 E := by
    apply le_sInf
    rintro N ⟨hn, hN⟩
    let := hn
    let : Group.IsNilpotent (E ⧸ N) := hN.isNilpotent
    exact (le_solvableResidual_of_isPerfect K).trans
      (solvableResidual_le_of_solvable_quotient N)
  have hn : (componentOrbit K (S : Subgroup E)).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le ((le_componentOrbit K _).trans (componentOrbit K _).le_normalizer)
      (le_normalizer_componentOrbit K _)
  let := hn
  exact le_antisymm
    (iSup_conjugates_le_of_le_normalizer K _ _ hK le_normalizer_of_normal)
    (sInf_le ⟨hn, isPGroup_quotient_of_sup_eq_top _ (S : Subgroup E) S.isPGroup'
      ((componentOrbit_sup K _).trans hgen)⟩)

/-- The genuine initial component of 5.1.10 and its full residual orbit,
with no assumption that the component is fixed by T. -/
theorem exists_seed {T : Sylow 2 G} {M H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hgen : 1 < ChapterE.generationParameter H) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H := by
  let S := T.subtype hH.1.1.2
  have hS : (S : Subgroup H).map H.subtype = (T : Subgroup G) := by
    change ((T : Subgroup G).subgroupOf H).map H.subtype = _
    exact map_subgroupOf_eq_of_le hH.1.1.2
  have hs : ¬ Group.IsSolvable H := by
    intro hh
    let := hh
    exact (Nat.not_le_of_gt hgen) ChapterE.generationParameter_le_one_of_solvable
  obtain ⟨K, hK, hq, hg, _⟩ := ChapterE.Structure.source_original_component
    (Chapter3.sqtk_of_mem_H hG hH.1.1.1) S
    (hstar_minimalParabolic_of_generation_gt_one hTM hH hgen) hs
  let B := K.map H.subtype
  have hBH : B ≤ H := map_subtype_le _
  have hc : (B.subgroupOf H).IsCComponent := by
    change (K.map H.subtype |>.comap H.subtype).IsCComponent
    simpa only [comap_map_eq_self_of_injective H.subtype_injective] using hK
  have hBT : B ⊔ (T : Subgroup G) = H := by
    have hm := congrArg (map H.subtype) hg
    simpa only [Subgroup.map_sup, hS,
      ← MonoidHom.range_eq_map, range_subtype] using hm
  let e := K.equivMapOfInjective H.subtype H.subtype_injective
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hbq : IsQuasisimple (B ⧸ pCore 2 B) := by
    let := hq
    exact IsQuasisimple.of_mulEquiv q
  have hl : B ∈ Chapter1.L G (T : Subgroup G) := by
    change (B.subgroupOf (B ⊔ (T : Subgroup G))).IsCComponent ∧ _
    rw [hBT]
    refine ⟨hc, ⟨S, ?_⟩, hH.1.1.1⟩
    exact hS
  refine ⟨B, hBH, hc, hbq, hBT, hl, ?_⟩
  let := hK.perfect
  have ho := congrArg (map H.subtype) (orbit_eq_residual S K hg)
  simpa only [map_componentOrbit, hS] using ho

/-- The opening containment assertion of 5.1.12, applied to the constructed
seed in every original local overgroup. Its orbit contains all of O²(H). -/
theorem exists_seed_embedding {T : Sylow 2 G} {M H Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hgen : 1 < ChapterE.generationParameter H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃! C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H ≤ componentOrbit (C.map Y.subtype) (T : Subgroup G) := by
  obtain ⟨K, hKH, hc, hq, hg, hl, ho⟩ := exists_seed hG hTM hH hgen
  have hTY := hH.1.1.2.trans hY.2
  have hKY := hKH.trans hY.2
  have hk : K.subgroupOf Y ∈ Chapter1.L Y (T.subtype hTY : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hKY).mp ⟨hKY, hl⟩
  obtain ⟨C, ⟨hC, hKC⟩, hu⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
      (Chapter1.Section02.containment_of_theoremsAC
        (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
        (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)))
      (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hY.1)
      (T.subtype hTY) hk
  have hKC' : K ≤ C.map Y.subtype := by
    simpa only [map_subgroupOf_eq_of_le hKY] using map_mono (f := Y.subtype) hKC
  refine ⟨K, hKH, hc, hq, hg, hl, ho, C, ⟨hC, hKC', ?_⟩, ?_⟩
  · rw [← ho]
    exact iSup_mono fun _ => map_mono hKC'
  · intro D hD
    apply hu D ⟨hD.1, ?_⟩
    have hh := comap_mono (f := Y.subtype) hD.2.1
    change K.comap Y.subtype ≤ D
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hh

/-- In the branch where the whole residual is a local component, 1.2.4
constructs its normal container and the original escape excludes equality.
The local-family hypothesis is still a genuine earlier source obligation. -/
theorem exists_proper_normal_component {T : Sylow 2 G} {H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTH : (T : Subgroup G) ≤ H)
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ X : Subgroup G, X ≤ Y ∧ (X.subgroupOf Y).IsCComponent ∧
      (X.subgroupOf Y).Normal ∧ residual H < X := by
  have hTY := hTH.trans hY.2
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  let S := T.subtype hTY
  have hr : (residual H).subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hRY).mp ⟨hRY, hR⟩
  have hn : (S : Subgroup Y) ≤ normalizer ((residual H).subgroupOf Y : Set Y) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp ((hTH.trans (le_normalizer_residual H)) hs) (x : G)
  obtain ⟨C, ⟨hC, hRC, hCn⟩, _⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hY.1) S hr hn
  let X := C.map Y.subtype
  have hXY : X ≤ Y := map_subtype_le _
  have hc : (X.subgroupOf Y).IsCComponent := by
    change (C.map Y.subtype |>.comap Y.subtype).IsCComponent
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hC
  have hnormal : (X.subgroupOf Y).Normal := by
    change (C.map Y.subtype |>.comap Y.subtype).Normal
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hCn
  have hRX : residual H ≤ X := by
    simpa only [map_subgroupOf_eq_of_le hRY] using map_mono (f := Y.subtype) hRC
  refine ⟨X, hXY, hc, hnormal, lt_of_le_of_ne hRX ?_⟩
  intro he
  apply hescape
  rw [he]
  exact inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer hXY).mp hnormal)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
