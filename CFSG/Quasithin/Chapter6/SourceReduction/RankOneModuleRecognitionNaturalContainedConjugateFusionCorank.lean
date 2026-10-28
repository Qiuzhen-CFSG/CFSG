module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionDefs
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Coranks of noncentralizing conjugates

Centralizer rigidity below s(G,B) gives the lower bound on the action
of every noncentralizing conjugate. A local upper bound for elementary
action images then makes this an equality. Pulling the actual centralizer
back through conjugation gives the corank formula on B itself; the order
of the natural module proves that this fixed space is nonzero.

The local elementary-image upper bound is explicit and must still be
constructed from the natural action before this proves source 6.1.10(3).
Source: Aschbacher--Smith, printed p.670 (PDF p.687).
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G]

theorem fusion_map_conj_mul (B : Subgroup G) (g k : G) :
    (B.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      B.map (MulAut.conj (g * k)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem fusion_map_conj_inverse (B : Subgroup G) (g : G) :
    (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = B := by
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

theorem fusion_inverse_noncentralizing {B : Subgroup G} {g : G}
    (hnon : ¬ B.map (MulAut.conj g).toMonoidHom ≤ centralizer (B : Set G)) :
    ¬ B.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (B : Set G) := by
  intro hc
  have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hc).trans
    (map_centralizer_le_centralizer_image (B : Set G) (MulAut.conj g).toMonoidHom)
  have he : (B.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = B := by
    simpa using fusion_map_conj_inverse B g⁻¹
  rw [he] at hh
  exact hnon (le_centralizer_iff.mp hh)

theorem fusion_pullback_centralizer (B : Subgroup G) (g : G) :
    ((B.map (MulAut.conj g).toMonoidHom) ⊓ centralizer (B : Set G)).map
      (MulAut.conj g⁻¹).toMonoidHom =
      B ⊓ centralizer (B.map (MulAut.conj g⁻¹).toMonoidHom : Set G) := by
  rw [← map_inf_centralizer_of_injective _ (MulAut.conj g⁻¹).injective,
    fusion_map_conj_inverse]

theorem fusion_pullback_corank (B : Subgroup G) (g : G) :
    ChapterE.subgroupCorank B (B ⊓ centralizer
      (B.map (MulAut.conj g⁻¹).toMonoidHom : Set G)) =
    ChapterE.subgroupCorank (B.map (MulAut.conj g).toMonoidHom)
      (B.map (MulAut.conj g).toMonoidHom ⊓ centralizer (B : Set G)) := by
  have he := congrArg (Nat.log 2) (relIndex_map_map_of_injective
    (B.map (MulAut.conj g).toMonoidHom ⊓ centralizer (B : Set G))
    (B.map (MulAut.conj g).toMonoidHom)
    (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective)
  change ChapterE.subgroupCorank _ _ = _ at he
  simpa only [fusion_map_conj_inverse, fusion_pullback_centralizer,
    ChapterE.subgroupCorank] using he

theorem fusion_inverse_normalizes {B : Subgroup G} {g : G}
    (hn : B ≤ normalizer (B.map (MulAut.conj g).toMonoidHom : Set G)) :
    B.map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (B : Set G) := by
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hn
  rwa [map_equiv_normalizer_eq, fusion_map_conj_inverse] at hh

variable [Finite G] {κ : GroupClass}

/-- E.3.7 gives the lower bound without any local action classification. -/
theorem globalS_le_conjugate_action_corank (B : Subgroup G)
    [IsElementaryAbelian 2 B] (g : G)
    (hnon : ¬ B.map (MulAut.conj g).toMonoidHom ≤ centralizer (B : Set G)) :
    ChapterE.globalS B ≤
      (ChapterE.subgroupCorank (B.map (MulAut.conj g).toMonoidHom)
        (B.map (MulAut.conj g).toMonoidHom ⊓ centralizer (B : Set G)) : ℕ∞) := by
  by_contra hn
  have he := ChapterE.lemma_E_3_7 g
    (le_inf inf_le_left (inf_le_right.trans (centralizer_le_normalizer (B : Set G))))
    (lt_of_not_ge hn)
  have hBC : B ≤ centralizer
      ((B.map (MulAut.conj g).toMonoidHom ⊓ centralizer (B : Set G) : Subgroup G) : Set G) :=
    le_centralizer_iff.mpr inf_le_right
  rw [inf_eq_left.mpr hBC] at he
  exact hnon (le_centralizer_iff.mp (he.le.trans inf_le_right))

/-- The source lower bound and the local elementary-image bound are sharp
on every noncentralizing conjugate which normalizes the base module. -/
theorem conjugate_action_corank_eq_of_rank_bound (B : Subgroup G)
    [IsElementaryAbelian 2 B] {n : ℕ}
    (hs : ChapterE.globalS B = n) (hbound : ElementaryActionRankBound B n)
    (g : G) (hg : B.map (MulAut.conj g).toMonoidHom ≤ normalizer (B : Set G))
    (hnon : ¬ B.map (MulAut.conj g).toMonoidHom ≤ centralizer (B : Set G)) :
    ChapterE.subgroupCorank (B.map (MulAut.conj g).toMonoidHom)
      (B.map (MulAut.conj g).toMonoidHom ⊓ centralizer (B : Set G)) = n := by
  have hlo := globalS_le_conjugate_action_corank B g hnon
  rw [hs] at hlo
  exact le_antisymm (hbound _ (IsElementaryAbelian.map _) hg)
    (ENat.natCast_le_natCast.mp hlo)

/-- A half-dimensional subgroup of the natural module has the field's order. -/
theorem card_eq_pow_of_half_corank {B U : Subgroup G} [IsElementaryAbelian 2 B]
    {n : ℕ} (hUB : U ≤ B) (hcard : Nat.card B = 2 ^ (n * 2))
    (hcor : ChapterE.subgroupCorank B U = n) : Nat.card U = 2 ^ n := by
  have hi : (U.subgroupOf B).index = 2 ^ n := by
    rw [← hcor, ChapterE.subgroupCorank_eq_quotient_finrank]
    exact B.relIndex_eq_two_pow_quotient_finrank U
  have hc := (U.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv, hi, hcard,
    show n * 2 = n + n by omega, pow_add] at hc
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ n) hc

/-- The requested pullback formula, including nonzeroness, from the local
rank bound. Construction of that bound is a separate source obligation. -/
theorem conjugateCorankFormula_of_rank_bound
    {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    (hbound : ElementaryActionRankBound (layer L V) n) :
    ConjugateCorankFormula (T : Subgroup G) (layer L V) n := by
  let := h.layer_elementary
  intro g hg hnon
  have hc := conjugate_action_corank_eq_of_rank_bound (layer L V) hs hbound g
    (hg.trans h.sylow_normalizes_layer) hnon
  have hp := (fusion_pullback_corank (layer L V) g).trans hc
  refine ⟨?_, hp⟩
  have hcard := card_eq_pow_of_half_corank inf_le_left hnatural.card hp
  intro he
  rw [he, Subgroup.card_bot] at hcard
  have hn0 := h.n_gt_one
  have hn : 1 < 2 ^ n := Nat.one_lt_pow (by omega : n ≠ 0) (by decide)
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
