module
public import Theory.Character.ModularBlock.QCCentralizerSupport
public import Mathlib.GroupTheory.Nilpotent

/-!
# Normalizer growth for Brauer pairs

A p-subgroup Q of a finite group is either Sylow or is properly contained
in a larger p-subgroup inside N_G(Q), with strictly larger cardinality.
This is the normalizer-growth step used in the Brauer-pair induction.

Choose a Sylow group containing Q. If containment is proper, the normalizer
condition in that finite nilpotent p-group yields a proper overgroup.
Mapping its internal normalizer back to the ambient group preserves strict
containment, p-group structure, and the normalizer bound; finiteness gives
strict cardinal growth.

The reusable Q C_G(Q) subgroup tower, centralizer algebra embeddings, and
support-transport results are re-exported under the historical campaign
names. Their implementations live in the lower modular-block layer.
Ported from revision c3503435 of public/lean-eval/glauberman_zStar,
Submission/ZStar/NormalizerBrauerPair.lean, the normalizer layer of the
Juhasz proof of Brauer's Third Main Theorem.
-/

public section
namespace Glauberman.ZStar.NormalizerBrauerPair
open Subgroup
universe u

export ModularBlock.NormalizerBrauerPair (
  qcCentralizer
  centralizer_map_subtype_eq_of_ambientCentralizer_le
  qcCentralizer_map_subtype_eq_of_ambientCentralizer_le
  qcCentralizerMapEquiv
  qcCentralizerMapEquiv_apply_coe
  subgroupOf_qcCentralizer_map_qcCentralizerMapEquiv
  centralizerToQcCentralizer
  qcCentralizerAlgebraEmbedding
  qcCentralizerAlgebraEmbedding_single
  centralizerToQcCentralizer_injective
  qcCentralizerAlgebraEmbedding_ne_zero
  coeff_mem_centralizer_of_qcCentralizerAlgebraEmbedding_ne_zero
  coeff_centralizes_subgroupOf_qcCentralizer_of_embedding_ne_zero
  qcCentralizerAlgebraEmbedding_mem_center
  qcCentralizerAlgebraEmbedding_isIdempotent
  qcCentralizerAlgebraEmbedding_mul_eq_self
  augmentation_qcCentralizerAlgebraEmbedding
  subgroupOf_qcCentralizer_hasSupport_embedding
  subgroupOf_qcCentralizer_isMaximalSupport_of_embedding_restriction
  subgroupOf_qcCentralizer_isMaximalSupport_of_embedding_factor
  exists_maximalSupport_qcCentralizerEmbedding_containing
  qcCentralizer_le_normalizer
  qcCentralizer_subgroupOf_normalizer_isNormal
  subgroupOf_qcCentralizer_isNormal
  centralizer_subgroupOf_qcCentralizer_isNormal
  qcCentralizer_le_of_ambientCentralizer_le
  qcCentralizer_le_inf_of_ambientCentralizer_le)

/-- If `Q` is properly contained in a Sylow `p`-subgroup `P`, then
`N_G(Q)` contains a strictly larger `p`-subgroup.

The proof applies the normalizer condition inside the finite `p`-group `P`
and maps the resulting subgroup back to `G`. -/
theorem exists_strict_supergroup_le_normalizer_of_lt_sylow
    {p : ℕ} [Fact (Nat.Prime p)]
    {G : Type u} [Group G] [Finite G]
    (Q : Subgroup G) (P : Sylow p G)
    (hQP : Q < (P : Subgroup G)) :
    ∃ R : Subgroup G,
      IsPGroup p R ∧
        Q < R ∧
        R ≤ Subgroup.normalizer Q ∧
        Nat.card Q < Nat.card R := by
  let QP : Subgroup P := Q.subgroupOf (P : Subgroup G)
  have hQPproper : QP < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact (not_le_of_gt hQP) (Subgroup.subgroupOf_eq_top.mp htop)
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hnormalizer : QP < Subgroup.normalizer QP :=
    Group.normalizerCondition_of_isNilpotent QP hQPproper
  let R : Subgroup G :=
    (Subgroup.normalizer QP).map (P : Subgroup G).subtype
  have hRp : IsPGroup p R := by
    exact (P.isPGroup'.to_subgroup (Subgroup.normalizer QP)).map
      (P : Subgroup G).subtype
  have hQR : Q < R := by
    have hmap : QP.map (P : Subgroup G).subtype < R := by
      exact (Subgroup.map_subtype_lt_map_subtype).2 hnormalizer
    simpa [QP, R, Subgroup.map_subgroupOf_eq_of_le hQP.le] using hmap
  have hRN : R ≤ Subgroup.normalizer Q := by
    have hmap := Subgroup.le_normalizer_map
      (H := QP) (P : Subgroup G).subtype
    simpa [QP, R, Subgroup.map_subgroupOf_eq_of_le hQP.le] using hmap
  have hcard : Nat.card Q < Nat.card R := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le hQR.le)
    intro heq
    apply hQR.ne
    exact Subgroup.eq_of_le_of_card_ge hQR.le (by rw [heq])
  exact ⟨R, hRp, hQR, hRN, hcard⟩

/-- Every finite `p`-subgroup is either Sylow or admits strict `p`-subgroup
growth inside its normalizer. -/
theorem exists_sylow_eq_or_exists_strict_supergroup_le_normalizer
    {p : ℕ} [Fact (Nat.Prime p)]
    {G : Type u} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup p Q) :
    (∃ P : Sylow p G, (P : Subgroup G) = Q) ∨
      ∃ R : Subgroup G,
        IsPGroup p R ∧
          Q < R ∧
          R ≤ Subgroup.normalizer Q ∧
          Nat.card Q < Nat.card R := by
  obtain ⟨P, hQP⟩ := hQ.exists_le_sylow
  by_cases heq : (P : Subgroup G) = Q
  · exact Or.inl ⟨P, heq⟩
  · right
    exact exists_strict_supergroup_le_normalizer_of_lt_sylow Q P
      (lt_of_le_of_ne hQP (fun h => heq h.symm))

end Glauberman.ZStar.NormalizerBrauerPair

