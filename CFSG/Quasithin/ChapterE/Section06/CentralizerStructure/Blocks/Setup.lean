module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow
public import CFSG.Quasithin.ChapterE.Section06.Obstructions
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Local inputs and corank deductions for the block argument

An escaping centralizer is a subgroup of the two-local normalizer of its
nonidentity elementary abelian subgroup. Thus it and all its subgroups are
SQTK groups. The Sylow subgroup and characteristic-normalizer control of E.6.5
restrict to every intermediate group containing Q. These are the actual inputs
to C.1.29 in the proof of E.6.7.

The remaining deductions compare the fixed-space corank with the obstruction
corank and with r. They apply to any escaping subgroup, independently of its
eventual block identification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7,
printed p.246 (PDF p.257). The block and module classification is separate.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06
open Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {𝒦 : GroupClass} {T : Sylow 2 G} {M V U K L : Subgroup G}

theorem HypothesisE61.obstructionCentralizer_sqtk
    (h : HypothesisE61 𝒦 T M V) (hU : U ∈ obstructionFamily M V) :
    IsSQTK 𝒦 (centralizer (U : Set G)) := by
  let _ := h.elementary
  have hn := h.simpleQTKE.twoLocal_sqtk
    (show IsTwoLocal (normalizer (U : Set G)) from
      ⟨U, hU.2.1, (IsElementaryAbelian.isPGroup 2 V).to_le hU.1, rfl⟩)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe (centralizer_le_normalizer (U : Set G)))).mp
    (hn.subgroup ((centralizer (U : Set G)).subgroupOf (normalizer (U : Set G))))

theorem HypothesisE61.obstructionIntermediate_sqtk
    (h : HypothesisE61 𝒦 T M V) (hU : U ∈ obstructionFamily M V)
    (hKH : K ≤ centralizer (U : Set G)) : IsSQTK 𝒦 K :=
  (IsSQTK.equiv (subgroupOfEquivOfLe hKH)).mp
    ((h.obstructionCentralizer_sqtk hU).subgroup (K.subgroupOf (centralizer (U : Set G))))

/-- Restriction of E.6.5(1) to the intermediate group in E.6.7. -/
theorem HypothesisE61.sylow_obstructionIntermediate
    (h : HypothesisE61 𝒦 T M V) (hU : U ∈ obstructionFamily M V)
    (hQK : sylowCentralizer (T : Subgroup G) V ≤ K)
    (hKH : K ≤ centralizer (U : Set G)) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype =
      sylowCentralizer (T : Subgroup G) V := by
  obtain ⟨S, hS⟩ := h.sylow_obstruction hU
  have hSK : (S : Subgroup (centralizer (U : Set G))) ≤
      K.subgroupOf (centralizer (U : Set G)) := by
    intro x hx
    exact hQK (hS ▸ mem_map_of_mem _ hx)
  let e := subgroupOfEquivOfLe hKH
  refine ⟨(S.subtype hSK).mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  ext x
  constructor
  · rintro ⟨k, ⟨s, hs, rfl⟩, rfl⟩
    exact hS ▸ mem_map_of_mem _ hs
  · intro hx
    obtain ⟨s, hs, rfl⟩ := (show x ∈
      (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype
      from hS.symm ▸ hx)
    exact ⟨e ⟨s, hQK hx⟩, ⟨⟨s, hQK hx⟩, hs, rfl⟩, rfl⟩

/-- Control of characteristic normalizers is intrinsic to K, not normality in G. -/
theorem HypothesisE61.characteristic_normalizers_intermediate
    (h : HypothesisE61 𝒦 T M V)
    (hQK : sylowCentralizer (T : Subgroup G) V ≤ K) :
    ((sylowCentralizer (T : Subgroup G) V).subgroupOf K).characteristicNormalizerClosure ≤
      M.subgroupOf K := by
  let Q := sylowCentralizer (T : Subgroup G) V
  have hQp : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro D hD hDne
  let _ := hD
  let E := (D.map (Q.subgroupOf K).subtype).map K.subtype
  have hEp : IsPGroup 2 E := ((hQp.comap_subtype.to_subgroup D).map _).map _
  have hEne : E ≠ ⊥ := by
    intro he
    exact hDne ((D.map_eq_bot_iff_of_injective
      (f := K.subtype.comp (Q.subgroupOf K).subtype)
      (K.subtype_injective.comp (Q.subgroupOf K).subtype_injective)).mp
        (by simpa only [E, map_map] using he))
  have hn : normalizer (Q : Set G) ≤ normalizer (E : Set G) := by
    simpa only [map_subgroupOf_eq_of_le (show Q ≤ K from hQK)] using
      normalizer_le_normalizer_characteristic_map K.subtype K.subtype_injective
        (Q.subgroupOf K) D
  have hbound := normalizer_le_of_unique_maximalTwoLocal h.unique hEp hEne
    (inf_le_right.trans hn)
  intro x hx
  exact hbound ((le_normalizer_map K.subtype) (mem_map_of_mem K.subtype hx))

/-- An escaping subgroup supplies a genuine witness for the minimum defining r. -/
theorem HypothesisE61.globalR_le_fixedSpace_corank
    (h : HypothesisE61 𝒦 T M V) (hLM : ¬ L ≤ M) :
    globalR V ≤ (subgroupCorank V (V ⊓ centralizer (L : Set G)) : ℕ∞) := by
  apply globalR_le_corank inf_le_left
  intro hc
  exact hLM (((le_centralizer_iff.mpr inf_le_right).trans hc).trans h.normalizer_le)

/-- The last inequality of E.6.7(3). -/
theorem fixedSpace_corank_le_obstruction (hUV : U ≤ V)
    (hLH : L ≤ centralizer (U : Set G)) :
    subgroupCorank V (V ⊓ centralizer (L : Set G)) ≤ subgroupCorank V U :=
  subgroupCorank_antitone (le_inf hUV (le_centralizer_iff.mpr hLH))

/-- Once the intrinsic alternating-block calculation bounds the corank by one,
escape forces both this corank and the global parameter to equal one. -/
theorem HypothesisE61.fixedSpace_corank_eq_one
    (h : HypothesisE61 𝒦 T M V) (hLM : ¬ L ≤ M)
    (hsmall : subgroupCorank V (V ⊓ centralizer (L : Set G)) ≤ 1) :
    subgroupCorank V (V ⊓ centralizer (L : Set G)) = 1 ∧ globalR V = 1 := by
  have hr := h.globalR_le_fixedSpace_corank hLM
  have hl : (1 : ℕ∞) ≤ (subgroupCorank V (V ⊓ centralizer (L : Set G)) : ℕ∞) :=
    (one_le_globalR V).trans hr
  have he : subgroupCorank V (V ⊓ centralizer (L : Set G)) = 1 := by
    exact le_antisymm hsmall (by exact_mod_cast hl)
  exact ⟨he, le_antisymm (by simpa only [he, Nat.cast_one] using hr) (one_le_globalR V)⟩

/-- A direct decomposition gives the exact fixed-space corank from the order
of the displacement module; the factors need only normalize one another. -/
theorem corank_of_direct_decomposition {C D : Subgroup G} {n : ℕ}
    (hgen : V = C ⊔ D) (hn : D ≤ normalizer (C : Set G))
    (hdis : Disjoint C D) (hcard : Nat.card D = 2 ^ n) :
    subgroupCorank V C = n := by
  have hc : Nat.card V = Nat.card C * Nat.card D := by
    rw [hgen]
    exact card_sup_eq_mul_of_normalizes_of_disjoint C D hn hdis
  have ht := relIndex_mul_relIndex (⊥ : Subgroup G) C V bot_le
    (hgen ▸ le_sup_left)
  simp only [relIndex_bot_left] at ht
  rw [hc] at ht
  have hi : C.relIndex V = Nat.card D := Nat.eq_of_mul_eq_mul_left Nat.card_pos ht
  simp only [subgroupCorank, hi, hcard, Nat.log_pow (by decide : 1 < 2)]

end CFSG.Quasithin.ChapterE.Section06
