module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.WeakClosureRank
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.WeakClosureActors
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# Kernels and conjugate simplex centralizers for the A₇ weak-closure proof

The marked permutation kernel is the literal module centralizer. Its order
therefore gives the kernel-image formula for N_{Vᵍ}(V). Pulling a rank-three
subgroup of Vᵍ back to V transports the checked constant-weight-four
pointwise-stabilizer theorem to the same conjugate. The centralizer equality
is inside N(Vᵍ); no ambient simplex-centralizer containment is assumed.

Source: Aschbacher--Smith, 12.3.9--10, printed pp.810--811, with the corrected
rank-three code geometry. These interfaces feed `WeakClosure`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 ChapterE BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable (S : Setup T L V) (D : S.LocalAnalysis)
variable (structural : Structural1222 KnownSimple.IsKnownSimple.{u})

/-- The actual permutation kernel is the module centralizer. -/
theorem actor_permutation_eq_one_iff (n : normalizer (V : Set G)) :
    D.model.permutation n = 1 ↔ n.val ∈ centralizer (V : Set G) := by
  constructor
  · intro hp v hv
    have he := D.model.equivariant n ⟨v,hv⟩
    rw [hp, map_one] at he
    have hf := D.model.coordinates.injective (Multiplicative.toAdd.injective he)
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hf)).symm
  · intro hc
    exact D.model.permutation_eq_one_of_centralizes_simplex n
      (centralizer_le D.model.simplex_le hc)

/-- Kernel-image orders for the literal offender normalizer. -/
theorem actor_card_kernel_mul_image (g : G) :
    Nat.card (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) : Subgroup G) *
      Nat.card (actorImage S D g) = Nat.card (offenderNormalizer V g) := by
  have hk : D.model.permutation.ker =
      (centralizer (V : Set G)).subgroupOf (normalizer (V : Set G)) := by
    ext n
    exact actor_permutation_eq_one_iff S D n
  have h := IsElementaryAbelian.card_inf_ker_mul_card_map
    ((offenderNormalizer V g).subgroupOf (normalizer (V : Set G))) D.model.permutation
  rw [hk] at h
  change Nat.card ((offenderNormalizer V g ⊓ centralizer (V : Set G)).subgroupOf
    (normalizer (V : Set G))) * Nat.card (actorImage S D g) = _ at h
  have hC : offenderNormalizer V g ⊓ centralizer (V : Set G) ≤ normalizer (V : Set G) :=
    inf_le_left.trans inf_le_right
  rw [Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (show offenderNormalizer V g ≤ normalizer
      (V : Set G) from inf_le_right)).toEquiv, offenderNormalizer_inf_centralizer] at h
  exact h

omit [Finite G] in
private theorem centralizer_map (U : Subgroup G) (e : G ≃* G) :
    (centralizer (U : Set G)).map e.toMonoidHom = centralizer (U.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

include S D structural in
/-- The rank-three local centralizer equality on the actual conjugate module. -/
theorem conjugate_rank_three_centralizer (g : G) {U : Subgroup G}
    (hUV : U ≤ V.map (MulAut.conj g).toMonoidHom)
    (hr : Nat.log 2 (Nat.card U) = 3)
    (hesc : ¬ centralizer (U : Set G) ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) ⊓ centralizer (U : Set G) =
      centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let e := MulAut.conj g
  let U₀ := U.comap e.toMonoidHom
  have hm : U₀.map e.toMonoidHom = U := map_comap_eq_self_of_surjective e.surjective U
  have h₀ : U₀ ≤ V := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hUV hx
    exact (e.injective he) ▸ hy
  have he₀ : ¬ centralizer (U₀ : Set G) ≤ normalizer (V : Set G) := by
    intro h
    apply hesc
    have hh := map_mono (f := e.toMonoidHom) h
    rwa [centralizer_map, hm, map_equiv_normalizer_eq] at hh
  have hr₀ : Nat.log 2 (Nat.card U₀) = 3 := by
    rw [← hm, card_map_of_injective e.injective] at hr
    exact hr
  have he := D.model.normalizer_inf_centralizer_of_weight_four_rank_three h₀
    (weight_four_of_escaping_centralizer S D structural h₀ he₀) hr₀
  have hh := congrArg (fun H : Subgroup G => H.map e.toMonoidHom) he
  rwa [map_inf _ _ _ e.injective, centralizer_map, centralizer_map,
    map_equiv_normalizer_eq, hm] at hh

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
