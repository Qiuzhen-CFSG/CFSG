module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5LocalFactorization
public import CFSG.Quasithin.ChapterF.Section01.SourceStarredParabolic

/-!
# The reduced A5 pair of DGS (6.1)

Suppose both original Borels normalize the common two-group S in F.1.1.
The full Borel then has core S. Each reduced local group Lᵢ S is normal
in its original parabolic and contains that parabolic's core, so the two
cores agree. For an A5 local quotient, the actual inner-action Sylow
factorization gives Lᵢ S = O₂(Pᵢ)Lᵢ, the starred parabolic of F.1.9.
The inclusion of Lᵢ consequently induces an isomorphism of core quotients.

Replacing both factors by Lᵢ S preserves the full Borel, both parabolics
and the generated group, and gives another genuine F.1.1 pair. This is the
A5 specialization of the reduction in DGS (6.1), including its remark.
No equality O₂(Lᵢ S) = O₂(Lᵢ) is claimed: proving that further equality
for the original factors remains the F.1.12 recognition step. The tensor
consumer supplies both Borel normalizations from its original source data.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs, Part II,
(6.0)--(6.1), printed pp.118--119; Aschbacher--Smith F.1.9--F.1.12,
printed pp.261--264. DGS's reduced Lδ is distinguished throughout from
the original F.1.1 factor Lᵢ.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

namespace HypothesisF11

omit [Finite G] in
/-- The full common Borel normalizes S when both original Borels do. -/
theorem commonBorel_normalizes_S (_h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) :
    commonBorel L S ≤ normalizer (S : Set G) :=
  sup_le (sup_le (hn 0) (hn 1)) S.le_normalizer

omit [Finite G] in
/-- The common Sylow is exactly the core of the full, odd-inclusive Borel. -/
theorem commonBorel_twoCore_eq (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) :
    twoCore (commonBorel L S) = S := by
  obtain ⟨T, hT⟩ := h.sylow_commonBorel
  apply le_antisymm ((pCoreIn_le_sylow _ T).trans_eq hT)
  exact le_pCoreIn_of_normalizes h.S_isP le_sup_right (h.commonBorel_normalizes_S hn)

omit [Finite G] in
/-- Under Borel normalization the reduced local group is normal in its
original parabolic. -/
theorem localJoin_normalizes (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2) :
    parabolic L S i ≤ normalizer ((L i ⊔ S : Subgroup G) : Set G) := by
  apply sup_le (L i ⊔ S).le_normalizer
  exact (le_inf (h.cross i) (hn (other i))).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

omit [Finite G] in
/-- The reduced local group has the same core as the full parabolic.
This does not identify that core with O₂(Lᵢ). -/
theorem localJoin_twoCore_eq_parabolic (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2) :
    twoCore (L i ⊔ S) = twoCore (parabolic L S i) := by
  apply le_antisymm (pCoreIn_mono_of_normalizes le_sup_left (h.localJoin_normalizes hn i))
  exact le_pCoreIn_of_normalizes (pCore_isPGroup.map _)
    ((h.parabolic_core_le_S i).trans le_sup_right)
    (le_sup_left.trans ((parabolic L S i).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))

/-- DGS (6.1) in the A5 row: the reduced group S Pᵢ* equals Pᵢ*.
Here Pᵢ* is the original F.1.9 starred parabolic, not Lᵢ. -/
theorem a5_localJoin_eq_starredParabolic (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)) :
    L i ⊔ S = starredParabolic L S i := by
  have hs := h.a5_local_sylow_factorization i e (hn i)
  rw [h.localJoin_twoCore_eq_parabolic hn i] at hs
  change L i ⊔ S = twoCore (parabolic L S i) ⊔ L i
  apply le_antisymm
  · apply sup_le le_sup_right
    exact hs.le.trans (sup_le le_sup_left (inf_le_right.trans le_sup_right))
  · exact sup_le ((h.parabolic_core_le_S i).trans le_sup_right) le_sup_left

/-- The inclusion-induced quotient map for the reduced local group. -/
@[expose] def localJoinQuotientMap (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Fin 2) :
    L i →* ((L i ⊔ S : Subgroup G) ⧸ pCore 2 (L i ⊔ S : Subgroup G)) :=
  (QuotientGroup.mk' _).comp (inclusion le_sup_left)

omit [Finite G] in
theorem localJoinQuotientMap_ker (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2) :
    (localJoinQuotientMap L S i).ker = pCore 2 (L i) := by
  have hc : (twoCore (L i ⊔ S)).subgroupOf (L i) = pCore 2 (L i) := by
    apply map_injective (L i).subtype_injective
    rw [subgroupOf_map_subtype, inf_comm, h.localJoin_twoCore_eq_parabolic hn i,
      h.local_inf_parabolic_core i]
    rfl
  rw [← hc]
  ext x
  change QuotientGroup.mk (inclusion le_sup_left x) =
    (1 : (L i ⊔ S : Subgroup G) ⧸ pCore 2 (L i ⊔ S : Subgroup G)) ↔
      (x : G) ∈ twoCore (L i ⊔ S)
  rw [QuotientGroup.eq_one_iff]
  exact (mem_map_iff_mem (f := (L i ⊔ S).subtype)
    (L i ⊔ S).subtype_injective).symm

theorem a5_localJoinQuotientMap_surjective (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)) :
    Function.Surjective (localJoinQuotientMap L S i) := by
  have heq : L i ⊔ S = twoCore (L i ⊔ S) ⊔ L i := by
    rw [h.localJoin_twoCore_eq_parabolic hn i]
    exact h.a5_localJoin_eq_starredParabolic hn i e
  intro z
  induction z using QuotientGroup.induction_on with
  | H x =>
    have hxprod : (x : G) ∈ (twoCore (L i ⊔ S) : Set G) * (L i : Set G) := by
      have hnorm : L i ≤ normalizer (twoCore (L i ⊔ S) : Set G) :=
        le_sup_left.trans ((L i ⊔ S).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
      rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm, ← heq]
      exact x.property
    obtain ⟨q, hq, l, hl, he⟩ := hxprod
    let q' : (L i ⊔ S : Subgroup G) := ⟨q, map_subtype_le _ hq⟩
    let l' : L i := ⟨l, hl⟩
    have hq' : q' ∈ pCore 2 (L i ⊔ S : Subgroup G) :=
      (mem_map_iff_mem (f := (L i ⊔ S).subtype)
        (L i ⊔ S).subtype_injective).mp hq
    have hx : q' * inclusion le_sup_left l' = x := Subtype.ext he
    refine ⟨l', ?_⟩
    rw [← hx]
    change _ = (QuotientGroup.mk' _) (_ * _)
    have hqone : (QuotientGroup.mk' (pCore 2 (L i ⊔ S : Subgroup G))) q' = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hq'
    rw [map_mul, hqone, one_mul]
    rfl

/-- The reduced quotient retains the original inclusion marking. -/
@[expose] def a5_localJoinQuotientEquiv (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)) :
    (L i ⧸ pCore 2 (L i)) ≃*
      ((L i ⊔ S : Subgroup G) ⧸ pCore 2 (L i ⊔ S : Subgroup G)) :=
  (QuotientGroup.quotientMulEquivOfEq (h.localJoinQuotientMap_ker hn i).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (h.a5_localJoinQuotientMap_surjective hn i e))

@[simp] theorem a5_localJoinQuotientEquiv_mk (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)) (x : L i) :
    h.a5_localJoinQuotientEquiv hn i e (QuotientGroup.mk x) =
      QuotientGroup.mk (inclusion le_sup_left x) := rfl


omit [Finite G] in
/-- Enlarging the local factor retains its odd Borel; only S is adjoined. -/
theorem localJoin_borel_eq (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2) :
    borel (L i ⊔ S) S = borel (L i) S ⊔ S := by
  change (L i ⊔ S) ⊓ normalizer ((S ⊓ (L i ⊔ S) : Subgroup G) : Set G) = _
  rw [inf_eq_left.mpr (show S ≤ L i ⊔ S from le_sup_right)]
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (L i : Set G) * (S : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (h.S_normalizes i)]
      exact hx.1
    obtain ⟨l, hl, s, hs, rfl⟩ := hxprod
    have hlS : l ∈ normalizer (S : Set G) :=
      ((normalizer (S : Set G)).mul_mem_cancel_right (S.le_normalizer hs)).mp hx.2
    have hlb : l ∈ borel (L i) S :=
      ⟨hl, inf_normalizer_le_normalizer_inf ⟨hlS, (L i).le_normalizer hl⟩⟩
    exact mul_mem (mem_sup_left hlb) (mem_sup_right hs)
  · exact sup_le (le_inf ((borel_le _ _).trans le_sup_left) (hn i))
      (le_inf le_sup_right S.le_normalizer)

omit [Finite G] in
/-- The reduced pair has exactly the original full overlap. -/
theorem localJoin_commonBorel_eq (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) :
    commonBorel (fun i => L i ⊔ S) S = commonBorel L S := by
  unfold commonBorel
  rw [h.localJoin_borel_eq hn 0, h.localJoin_borel_eq hn 1]
  simp only [sup_assoc, sup_left_comm, sup_comm, sup_left_idem]

omit [Finite G] in
/-- Both source parabolics are preserved, with the same orientation. -/
theorem localJoin_parabolic_eq (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2) :
    parabolic (fun j => L j ⊔ S) S i = parabolic L S i := by
  unfold parabolic
  rw [h.localJoin_borel_eq hn (other i)]
  simp only [sup_assoc, sup_left_comm, sup_comm, sup_left_idem]

omit [Finite G] in
/-- This reduction does not replace the source completion. -/
theorem localJoin_generated_eq :
    generated (fun i => L i ⊔ S) S = generated L S := by
  unfold generated
  simp only [sup_assoc, sup_left_comm, sup_comm, sup_left_idem]

/-- DGS (6.1) for the two A5 rows, with all F.1.1 clauses constructed.
It is the reduced pair, rather than the original factors, that contains S. -/
theorem a5_localJoin_hypothesis (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G))
    (he : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))) :
    HypothesisF11 (fun i => L i ⊔ S) S := by
  refine ⟨h.finite_S, h.S_isP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact le_sup_right.trans (L i ⊔ S).le_normalizer
  · intro i
    have hi : ¬ 2 ∣ S.relIndex (L i ⊔ S) := by
      intro hd
      apply h.parabolic_odd_index i
      rw [← relIndex_mul_relIndex S (L i ⊔ S) (parabolic L S i)
        le_sup_right le_sup_left]
      exact dvd_mul_of_dvd_left hd _
    have hp : IsPGroup 2 (S.subgroupOf (L i ⊔ S)) := h.S_isP.comap_subtype
    change ¬ 2 ∣ (S.subgroupOf (L i ⊔ S)).index at hi
    refine ⟨hp.toSylow hi, ?_⟩
    change (S.subgroupOf (L i ⊔ S)).map (L i ⊔ S).subtype = S ⊓ (L i ⊔ S)
    rw [map_subgroupOf_eq_of_le (show S ≤ L i ⊔ S from le_sup_right),
      inf_eq_left.mpr (show S ≤ L i ⊔ S from le_sup_right)]
  · intro i
    obtain ⟨e⟩ := he i
    exact (h.quotient i).of_equiv (h.a5_localJoinQuotientEquiv hn i e).symm
  · intro i
    rw [h.localJoin_borel_eq hn (other i)]
    exact sup_le (le_sup_right.trans (h.localJoin_normalizes hn i))
      (le_sup_right.trans (L i ⊔ S).le_normalizer)
  · rw [localJoin_generated_eq]
    exact h.twoCore_free
  · intro i
    rw [h.localJoin_parabolic_eq hn i]
    exact h.characteristic_two i

end HypothesisF11
end CFSG.Quasithin.ChapterF.Source
