module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LargeLocalQuotients
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerChiefBound
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallResidualNormalizer

/-!
# The terminal central-fixer contradiction

In the general residual case, the right two-core has index two in the
original overlap. If it were the edge normalizer of a maximal candidate,
the first local normalizer would have index two in the left endpoint.
The right endpoint normalizes the first normalizer's Sylow two-subgroup,
so the shared local classification consequence makes every Sylow three-subgroup
normal in that normalizer. Such a Sylow is characteristic there and therefore
normal in the left endpoint, contradicting its excluded cubic residual.

The overlap/core calculation is also used by the central-fixer selection
argument, which constructs the maximal candidate and the forbidden equality.
All subgroup maps here are the literal inclusions in the original completion.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.3),
printed p.395, the application of (2.15) in the final paragraph.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem normal_three_sylow_of_index_two {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) (hi : K.index = 2)
    (P : Sylow 3 K) (hn : (P : Subgroup K).Normal) :
    ∃ Q : Sylow 3 H, (Q : Subgroup H).Normal := by
  let : K.Normal := normal_of_index_eq_two hi
  let : (P : Subgroup K).Characteristic := P.characteristic_of_normal hn
  have hmap : ((P : Subgroup K).map K.subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    simpa only [K.normalizer_eq_top] using
      normalizer_le_normalizer_characteristic_image K (P : Subgroup K)
  have hind : ¬ 3 ∣ ((P : Subgroup K).map K.subtype).index := by
    rw [index_map_subtype, hi]
    exact Nat.Prime.not_dvd_mul (by decide) P.not_dvd_index (by decide)
  exact ⟨(P.isPGroup'.map K.subtype).toSylow hind, hmap⟩

/-- The literal right two-core lies in the overlap with index two. This
calculation is shared by the central-fixer selection and terminal arguments. -/
theorem CubicTreeAction.right_twoCore_overlap_of_large_residual (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4))) :
    let C := (pCore 2 (F true)).map (F true).subtype
    C ≤ F false ⊓ F true ∧ C.relIndex (F false ⊓ F true) = 2 := by
  let C := (pCore 2 (F true)).map (F true).subtype
  let T := F false ⊓ F true
  let P : Sylow 2 (F true) :=
    (h.primitive.sylow.isPGroup.comap_subtype : IsPGroup 2 (T.subgroupOf (F true))).toSylow
      (by change ¬ 2 ∣ T.relIndex (F true)
          rw [h.overlap_relIndex true]
          decide)
  have hCP : pCore 2 (F true) ≤ (P : Subgroup (F true)) :=
    pCore_isPGroup.le_sylow_of_normal P
  have hCT : C ≤ T := by
    have hm := map_mono (f := (F true).subtype) hCP
    change C ≤ (T.subgroupOf (F true)).map (F true).subtype at hm
    rwa [map_subgroupOf_eq_of_le (show T ≤ F true from inf_le_right)] at hm
  obtain ⟨e⟩ := h.local_quotient_symmetricThree_of_large_residual hC hA true
  have hCB : C.relIndex (F true) = 6 := by
    change (((pCore 2 (F true)).map (F true).subtype).comap (F true).subtype).index = 6
    rw [comap_map_eq_self_of_injective (F true).subtype_injective]
    change Nat.card ((F true) ⧸ pCore 2 (F true)) = 6
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have hm := relIndex_mul_relIndex C T (F true) hCT inf_le_right
  have ht := h.overlap_relIndex true
  change T.relIndex (F true) = 3 at ht
  rw [ht, hCB] at hm
  change C ≤ T ∧ C.relIndex T = 2
  exact ⟨hCT, by omega⟩

private theorem candidate_local_index_two (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (R : Subgroup G) (hR : NormalizerCandidate F R)
    (he : edgeNormalizer F R = (pCore 2 (F true)).map (F true).subtype) :
    (localNormalizer F R false).relIndex (F false) = 2 := by
  let E := edgeNormalizer F R
  let T := F false ⊓ F true
  let M := localNormalizer F R false
  have hET : E.relIndex T = 2 := by
    rw [show E = (pCore 2 (F true)).map (F true).subtype from he]
    exact (h.right_twoCore_overlap_of_large_residual hC hA).2
  have hEL : E.relIndex M = 3 := by
    have heq : E.subgroupOf M = T.subgroupOf M := by
      ext x
      exact ⟨fun hx => hx.2, fun hx => ⟨x.property.1, hx⟩⟩
    change (E.subgroupOf M).index = 3
    rw [heq]
    exact hR.left_index
  have h2 := relIndex_mul_relIndex E T (F false)
    (show E ≤ T from inf_le_right) inf_le_left
  have h3 := relIndex_mul_relIndex E M (F false)
    (edgeNormalizer_le_local R false) inf_le_right
  have hf := h.overlap_relIndex false
  change T.relIndex (F false) = 3 at hf
  rw [hET, hf] at h2
  rw [hEL] at h3
  change M.relIndex (F false) = 2
  omega

private theorem candidate_edge_ne_core_of_normal_three (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (R : Subgroup G) (hR : NormalizerCandidate F R)
    (he : edgeNormalizer F R = (pCore 2 (F true)).map (F true).subtype)
    (hn : ∀ P : Sylow 3 (localNormalizer F R false),
      (P : Subgroup (localNormalizer F R false)).Normal) : False := by
  classical
  let : Finite (F false) := h.finite false
  let M := localNormalizer F R false
  let : Finite M := h.finite_localNormalizer R false
  let K := M.subgroupOf (F false)
  let e : K ≃* M := subgroupOfEquivOfLe (show M ≤ F false from inf_le_right)
  let P : Sylow 3 M := default
  let Q : Sylow 3 K := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hQ : (Q : Subgroup K).Normal :=
    (hn P).map e.symm.toMonoidHom e.symm.surjective
  have hi : K.index = 2 := candidate_local_index_two h hC hA R hR he
  obtain ⟨S, hS⟩ := normal_three_sylow_of_index_two K hi Q hQ
  exact h.local_sylow_three_not_normal_of_large_residual hC false S hS

/-- The maximal edge normalizer cannot be the embedded right two-core:
(2.15) would give a normal Sylow three-subgroup in the left endpoint. -/
theorem MaximalNormalizerCandidate.edge_ne_right_twoCore_of_large_residual
    (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    {R : Subgroup G} (hR : MaximalNormalizerCandidate F R) :
    edgeNormalizer F R ≠ (pCore 2 (F true)).map (F true).subtype := by
  intro he
  let M := localNormalizer F R false
  obtain ⟨P, hP, ⟨e⟩, _⟩ := hR.local_pushingUp_input h
  have hPE : (P : Subgroup M).map M.subtype = edgeNormalizer F R := by
    rw [hP]
    exact map_subgroupOf_eq_of_le (edgeNormalizer_le_local R false)
  have hPT : (P : Subgroup M).map M.subtype ≤ F false ⊓ F true := by
    rw [hPE]
    exact inf_le_right
  have hBN : F true ≤ normalizer ((P : Subgroup M).map M.subtype : Set G) := by
    rw [hPE, he]
    have hh := (pCore 2 (F true)).le_normalizer_map (F true).subtype
    simpa only [(pCore 2 (F true)).normalizer_eq_top,
      ← MonoidHom.range_eq_map, range_subtype] using hh
  exact candidate_edge_ne_core_of_normal_three h hC hA R hR.toNormalizerCandidate he
    (h.normal_three_of_opposite_normalized_sylow M inf_le_right P hPT hBN e)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
