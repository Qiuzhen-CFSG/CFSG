module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.AmbientActors.Group
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The literal outer involution centralizers and elementary actor

The marked conjugation action gives the pointwise matrix formula for every
pure half-degree field lift in G. Its centralizer inside L is the marked
copy of SL₂(K), with an actual multiplicative equivalence. Its centralizer
in the chosen root group is exactly the marked fixed-field root group R_t.
Consequently X = R_t⟨t⟩ is elementary, has order 2^(s+1), and has rank s+1.
The final source application supplies this configuration from even index.

These conclusions concern the original group and its literal subgroups.
The Hermitian vector-space realization, quadraticity, and fixed dimensions
remain distinct obligations. In particular no conclusion here identifies
quadratic threshold actors with minimizing actors.
Source: Aschbacher–Smith, K.3.1.2, printed p.454; D.2.1, printed p.178,
combined manuscript of 1 March 2004.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.RankOne
open Representation Representation.BinaryOffender Subgroup
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne
open Matrix.SpecialLinearGroup
variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {s : ℕ} [NeZero s] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
namespace OrthogonalModel
variable (M : OrthogonalModel s ρ L) [L.Normal]

/-- The layer automorphism retains conjugation on the literal elements of G. -/
theorem projectiveEmbedding_ambientAut (g : G) (a : Theory.PSL2.Group (Field s)) :
    (M.projectiveEquiv.symm (M.ambientAut g a) : G) =
      g * (M.projectiveEquiv.symm a : G) * g⁻¹ := by
  change (M.projectiveEquiv.symm
    (M.projectiveEquiv (MulAut.conjNormal g (M.projectiveEquiv.symm a))) : G) = _
  rw [M.projectiveEquiv.symm_apply_apply]
  rfl

/-- A pure field lift conjugates the marked SL₂ matrices entry by entry. -/
theorem conjugate_modelEmbedding {t : G}
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))
    (a : Matrix.SpecialLinearGroup (Fin 2) (Field s)) :
    t * M.modelEmbedding a * t⁻¹ =
      M.modelEmbedding (Theory.PSL2.sl2FieldAut (conjugation s) a) := by
  have he := M.projectiveEmbedding_ambientAut t (Theory.PSL2.sl2QuotientEquiv (Field s) a)
  rw [ht] at he
  simpa [projectiveEquiv, modelEmbedding, Theory.PSL2.fieldAut, MulAut.congr] using he.symm

/-- Centralization by the actual t is exactly fixed-field membership in the model. -/
theorem commute_modelEmbedding_iff {t : G}
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))
    (a : Matrix.SpecialLinearGroup (Fin 2) (Field s)) :
    Commute t (M.modelEmbedding a) ↔ a ∈ involutionCentralizer s := by
  change t * M.modelEmbedding a = M.modelEmbedding a * t ↔ _
  rw [← mul_inv_eq_iff_eq_mul, M.conjugate_modelEmbedding ht,
    M.modelEmbedding_injective.eq_iff, mem_involutionCentralizer_iff]
  constructor
  · intro he i j
    exact congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (Field s) => A.val i j) he
  · intro he
    ext i j
    exact he i j

/-- The centralizer in the original layer is the embedded fixed-field SL₂. -/
theorem centralizer_layer_eq_modelImage {t : G}
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) :
    centralizer ({t} : Set G) ⊓ L = M.modelImage (involutionCentralizer s) := by
  ext g
  constructor
  · rintro ⟨hc, hgL⟩
    let a := M.groupEquiv ⟨g, hgL⟩
    have he : M.modelEmbedding a = g := by
      change (M.groupEquiv.symm (M.groupEquiv ⟨g, hgL⟩) : G) = g
      rw [M.groupEquiv.symm_apply_apply]
    refine ⟨a, (M.commute_modelEmbedding_iff ht a).mp ?_, he⟩
    rw [he]
    exact (mem_centralizer_singleton_iff.mp hc).symm
  · rintro ⟨a, ha, rfl⟩
    refine ⟨mem_centralizer_singleton_iff.mpr
      ((M.commute_modelEmbedding_iff ht a).mpr ha).symm,
      M.modelImage_le_layer _ (mem_map_of_mem _ ha)⟩

/-- The fixed-field SL₂ is genuinely isomorphic to the original layer centralizer. -/
def fixedFieldEquivLayerCentralizer {t : G}
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) :
    Matrix.SpecialLinearGroup (Fin 2) (fixedField s) ≃*
      (centralizer ({t} : Set G) ⊓ L : Subgroup G) :=
  (fixedFieldEquivCentralizer s).trans
    (((involutionCentralizer s).equivMapOfInjective M.modelEmbedding
      M.modelEmbedding_injective).trans
      (MulEquiv.subgroupCongr (M.centralizer_layer_eq_modelImage ht).symm))

/-- The centralizer of t inside the chosen actual root group is R_t. -/
theorem root_centralizer_eq_modelImage {t : G}
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) :
    M.modelImage (upperUnipotent (Field s)) ⊓ centralizer ({t} : Set G) =
      M.modelImage (fixedRootGroup s) := by
  ext g
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hc⟩
    exact ⟨a, ⟨ha, (M.commute_modelEmbedding_iff ht a).mp
      (mem_centralizer_singleton_iff.mp hc).symm⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨mem_map_of_mem _ ha.1, mem_centralizer_singleton_iff.mpr
      ((M.commute_modelEmbedding_iff ht a).mpr ha.2).symm⟩

/-- The source subgroup X = R_t⟨t⟩, on the original ambient carrier. -/
def outerActor (t : G) : Subgroup G := M.modelImage (fixedRootGroup s) ⊔ zpowers t

private theorem pure_lift_centralizes_fixedRoot {t : G}
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) :
    t ∈ centralizer (M.modelImage (fixedRootGroup s) : Set G) := by
  rintro g ⟨a, ha, rfl⟩
  exact ((M.commute_modelEmbedding_iff ht a).mpr ha.2).symm

/-- The concrete outer actor is elementary abelian on the actual source group. -/
theorem outerActor_elementary {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) :
    IsElementaryTwo (M.outerActor t) := by
  let : IsElementaryAbelian 2 (M.modelImage (fixedRootGroup s)) := M.fixedRoot_calculation.1.2
  let : IsElementaryAbelian 2 (zpowers t) := IsElementaryAbelian.zpowers_of_pow_eq_one ht2
  refine ⟨?_, IsElementaryAbelian.sup_of_le_centralizer
    (zpowers_le.mpr (M.pure_lift_centralizes_fixedRoot ht))⟩
  intro hb
  have htX : t ∈ M.outerActor t := mem_sup_right (mem_zpowers t)
  rw [hb, mem_bot] at htX
  exact htL (htX ▸ L.one_mem)

/-- Adjoining the actual outer involution doubles the order of R_t. -/
theorem outerActor_card {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) :
    Nat.card (M.outerActor t) = 2 ^ (s + 1) := by
  rw [outerActor, card_sup_zpowers_of_normalizing_involution _ t ht2
    (fun hm => htL (M.modelImage_le_layer _ hm))
    (centralizer_le_normalizer _ (M.pure_lift_centralizes_fixedRoot ht))]
  change 2 * Nat.card ((fixedRootGroup s).map M.modelEmbedding) = _
  rw [Subgroup.card_map_of_injective M.modelEmbedding_injective,
    ← Nat.card_congr (fixedRootEquiv s).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (fixedField s) ≃ fixedField s),
    card_fixedField, pow_succ, Nat.mul_comm]

/-- Its elementary rank is s+1, with no assertion yet about its module action. -/
theorem outerActor_rank {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) :
    rank (M.outerActor t) = s + 1 := by
  rw [rank, M.outerActor_card ht2 htL ht, Nat.log_pow Nat.one_lt_two]


/-- The inner part of the actual outer actor is precisely R_t. -/
theorem outerActor_inf_layer [Finite G] (h : SourceHypotheses ρ L)
    {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) :
    M.outerActor t ⊓ L = M.modelImage (fixedRootGroup s) := by
  let : IsElementaryAbelian 2 (M.outerActor t) := (M.outerActor_elementary ht2 htL ht).2
  have hout : ¬ M.outerActor t ≤ L := by
    intro hle
    exact htL (hle (mem_sup_right (mem_zpowers t)))
  have hp := IsElementaryAbelian.card_inf_ker_mul_card_map (M.outerActor t) M.fieldHom
  rw [M.fieldHom_ker h, M.outer_elementary_field_card h _ hout,
    outerActor, card_sup_zpowers_of_normalizing_involution _ t ht2
      (fun hm => htL (M.modelImage_le_layer _ hm))
      (centralizer_le_normalizer _ (M.pure_lift_centralizes_fixedRoot ht))] at hp
  have he : Nat.card (M.outerActor t ⊓ L : Subgroup G) =
      Nat.card (M.modelImage (fixedRootGroup s)) := by
    change Nat.card (M.outerActor t ⊓ L : Subgroup G) * 2 = _ at hp
    omega
  symm
  exact Subgroup.eq_of_le_of_card_ge
    (le_inf le_sup_left (M.modelImage_le_layer _)) he.le

omit [L.Normal] in
/-- The constructed outer actor lies over a nontrivial field component. -/
theorem outerActor_not_le_layer {t : G} (htL : t ∉ L) : ¬ M.outerActor t ≤ L := by
  intro h
  exact htL (h (mem_sup_right (mem_zpowers t)))

end OrthogonalModel

/-- The even-extension source branch now has a literal outer involution,
its actual fixed-field centralizer, root centralizer, and elementary actor X.
The quadratic and dimension assertions require the vector-space realization. -/
theorem SourceHypotheses.orthogonal_outer_group_configuration [Finite G]
    (h : SourceHypotheses ρ L) (M : OrthogonalModel s ρ L) (heven : Even L.index) :
    letI : L.Normal := h.layer_normal
    ∃ t : G, t ^ 2 = 1 ∧ t ∉ L ∧
      M.ambientAut t = Theory.PSL2.fieldAut (conjugation s) ∧
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) (fixedField s) ≃*
        (centralizer ({t} : Set G) ⊓ L : Subgroup G)) ∧
      M.modelImage (upperUnipotent (Field s)) ⊓ centralizer ({t} : Set G) =
        M.modelImage (fixedRootGroup s) ∧
      IsElementaryTwo (M.outerActor t) ∧ rank (M.outerActor t) = s + 1 ∧
      Nat.card (M.outerActor t) = 2 ^ (s + 1) := by
  let : L.Normal := h.layer_normal
  obtain ⟨t, ht2, htL, ht⟩ := M.exists_outer_involution h heven
  exact ⟨t, ht2, htL, ht, ⟨M.fixedFieldEquivLayerCentralizer ht⟩,
    M.root_centralizer_eq_modelImage ht, M.outerActor_elementary ht2 htL ht,
    M.outerActor_rank ht2 htL ht, M.outerActor_card ht2 htL ht⟩

end CFSG.Quasithin.ChapterK.RankOne
