module
public import CFSG.Quasithin.Chapter10.SourceSetup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs

/-!
# The original Sylow-stabilizer MS hypotheses in the tensor branch

For an outside overgroup H containing L and the original stabilizer
T₁=N_T(L), assume T₁ is Sylow in H, as established at source9.3.4.
The source index-two theorem makes T₁ normal in T. A nontrivial
characteristic subgroup of T₁ normal in H would therefore be normalized
by both L and T. Original uniqueness puts its full normalizer in M,
contradicting H outside M. This proves MS3. For MS2(a), use the proper
odd-index subgroup T₁ itself, whose two-core is all of T₁.

These are actual producers of the two MS hypotheses used by the narrow
Sp₄(4) whole-core recognition. They do not assume a block reconstruction.
Source: Aschbacher--Smith9.3.10 and C.1.31, printed pp.734 and135.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D
private theorem source_uniqueness_ms : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

omit D [Finite G] in
private theorem normalizer_mapped_characteristic_ms
    {P : Type*} [Group P] (C : Subgroup P) (F : Subgroup C) [F.Characteristic]
    (i : P →* G) (hi : Function.Injective i) :
    normalizer (C.map i : Set G) ≤ normalizer ((F.map C.subtype).map i : Set G) := by
  let e := C.equivMapOfInjective i hi
  let K := F.map e.toMonoidHom
  have hK : K.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
    exact e.apply_symm_apply (a (e y))
  have he : (F.map C.subtype).map i = K.map (C.map i).subtype := by
    rw [map_map, map_map]
    rfl
  rw [he]
  exact normalizer_le_normalizer_characteristic_image (C.map i) K

/-- Original uniqueness excludes characteristic subgroups normal in an outside overgroup. -/
theorem source_msCharacteristic_of_outside
    (H R : Subgroup G) (hRH : R ≤ H) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hLH : L ≤ H) (hout : ¬ H ≤ D.maximalLocal) :
    ChapterC.MSCharacteristicCondition (R.subgroupOf H) := by
  intro C hc hne hn
  let := hc
  let := hn
  let W := (C.map (R.subgroupOf H).subtype).map H.subtype
  have hpR : IsPGroup 2 (R.subgroupOf H) :=
    (T.isPGroup'.to_le hRT).of_equiv (subgroupOfEquivOfLe hRH).symm
  have hpW : IsPGroup 2 W :=
    ((hpR.to_subgroup C).map (R.subgroupOf H).subtype).map H.subtype
  have hneW : W ≠ ⊥ := by
    intro he
    exact hne ((C.map_eq_bot_iff_of_injective (R.subgroupOf H).subtype_injective).mp
      (((C.map (R.subgroupOf H).subtype).map_eq_bot_iff_of_injective H.subtype_injective).mp he))
  have hHW : H ≤ normalizer (W : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg w hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact mem_map.mpr ⟨⟨g, hg⟩ * v * ⟨g, hg⟩⁻¹,
      (inferInstance : (C.map (R.subgroupOf H).subtype).Normal).conj_mem v hv ⟨g, hg⟩, rfl⟩
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) := by
    have hh := normalizer_mapped_characteristic_ms (R.subgroupOf H) C
      H.subtype H.subtype_injective
    rw [map_subgroupOf_eq_of_le hRH] at hh
    exact hTR.trans hh
  apply hout
  apply hHW.trans
  apply normalizer_le_of_unique_maximalTwoLocal
    (D.lemma_3_2_3_uniqueness (source_uniqueness_ms D)).2.2 hpW hneW
  exact sup_le (iSup_conjugates_le_of_le_normalizer L T _ (hLH.trans hHW)
    (hTW.trans (normalizer (W : Set G)).le_normalizer)) hTW

/-- MS2(a) uses the Sylow subgroup itself as the odd-index subgroup. -/
theorem source_msOddIndexRadical_of_outside
    (H R : Subgroup G) (hRH : R ≤ H) (hRT : R ≤ (T : Subgroup G))
    (hs : Chapter1.IsSylowIn 2 R H) (hout : ¬ H ≤ D.maximalLocal) :
    ChapterC.MSOddIndexRadical (R.subgroupOf H) := by
  obtain ⟨S, hS⟩ := hs
  have he : (S : Subgroup H) = R.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le hRH]
  refine ⟨R.subgroupOf H, lt_top_iff_ne_top.mpr ?_, ?_, ?_⟩
  · intro ht
    have hHR : H ≤ R := by
      intro g hg
      exact (show (⟨g, hg⟩ : H) ∈ R.subgroupOf H from ht ▸ mem_top _)
    exact hout (hHR.trans (hRT.trans (le_normalizer_componentOrbit L T)))
  · rw [← he]
    simpa only [← even_iff_two_dvd, Nat.not_even_iff_odd] using S.not_dvd_index
  · have hp : IsPGroup 2 (R.subgroupOf H) := he ▸ S.isPGroup'
    have hcore : pCore 2 (R.subgroupOf H) = ⊤ :=
      top_unique (le_sSup ⟨inferInstance, hp.of_equiv topEquiv.symm⟩)
    rw [hcore, ← MonoidHom.range_eq_map, range_subtype]

/-- The index-two source stabilizer supplies both literal MS inputs. -/
theorem source_nonnormal_stabilizer_msInputs
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hLH : L ≤ H) (hout : ¬ H ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H) :
    ChapterC.MSOddIndexRadical (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H) ∧
    ChapterC.MSCharacteristicCondition (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H) := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hi : ((normalizer (L : Set G)).subgroupOf (T : Subgroup G)).index = 2 :=
    source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  have he : R.subgroupOf (T : Subgroup G) =
      (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
    ext x
    exact and_iff_right x.property
  have hnormal : (R.subgroupOf (T : Subgroup G)).Normal :=
    he ▸ normal_of_index_eq_two hi
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show R ≤ (T : Subgroup G) from inf_le_left)).mp hnormal
  exact ⟨source_msOddIndexRadical_of_outside D H R hRH inf_le_left hs hout,
    source_msCharacteristic_of_outside D H R hRH inf_le_left hTR hLH hout⟩
end CFSG.Quasithin.Chapter10
