module
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Mathlib.GroupTheory.Index

/-!
# Fixed-index saturation through two layers

Two-perfectness lifts fixed points through a central p-kernel, by commutator
idempotence. A fixed-free subgroup in the kernel of a surjective coordinate
map gives a multiplicative lower bound on the fixed index. Matching that
bound in a containing group forces a product with its actual fixed subgroup.

The MS93 first-hat application uses its natural subgroup and natural quotient,
each of order eight, together with the genuine fixed-index bound of 64.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem centralizerModulo_eq_inf_of_pPerfect_central_kernel
    (p : ℕ) [Fact p.Prime] (A L N : Subgroup G)
    [A.Normal] [L.Normal] [N.Normal]
    (hL : IsPPerfect p L) (hA : IsPGroup p A)
    (hN : N ≤ centralizer (L : Set G)) :
    centralizerModulo A L N = A ⊓ centralizer (L : Set G) := by
  let C := centralizerModulo A L N
  let : (L.map (QuotientGroup.mk' N)).Normal :=
    Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  let : C.Normal := by dsimp only [C, centralizerModulo]; infer_instance
  have hCN : ⁅C, L⁆ ≤ N := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    exact (mem_centralizerModulo_iff.mp hx).2 l hl
  have hC : C ≤ centralizer (L : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← commutator_isPPerfect_idempotent L C hL
      (hA.to_le (centralizerModulo_le A L N)) le_normalizer_of_normal]
    exact (commutator_mono hCN le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr hN).le
  apply le_antisymm (le_inf (centralizerModulo_le A L N) hC)
  intro x hx
  apply mem_centralizerModulo_iff.mpr
  refine ⟨hx.1, fun l hl => ?_⟩
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 l hl)]
  exact N.one_mem

/-- A subgroup with a large fixed-free kernel layer and a large quotient has
at least the product of their dimensions as fixed-point index. -/
theorem fixed_index_lower_of_two_layers
    {T : Type*} [Group T] [Finite T] (W U C : Subgroup G)
    (hUW : U ≤ W) (hCW : C ≤ W) (f : W →* T)
    (hf : Function.Surjective f)
    (hU : U.subgroupOf W ≤ f.ker) (hC : C.subgroupOf W ≤ f.ker)
    (hdis : Disjoint U C) :
    Nat.card U * Nat.card T ≤ C.relIndex W := by
  let K := f.ker.map W.subtype
  have hKW : K ≤ W := map_subtype_le _
  have hUK : U ≤ K := by
    intro x hx
    exact ⟨⟨x,hUW hx⟩,hU hx,rfl⟩
  have hCK : C ≤ K := by
    intro x hx
    exact ⟨⟨x,hCW hx⟩,hC hx,rfl⟩
  have hKU : C.relIndex U = Nat.card U := by
    rw [← inf_relIndex_right, inf_comm, hdis.eq_bot, relIndex_bot_left]
  have hCKlower : Nat.card U ≤ C.relIndex K := by
    rw [← hKU]
    exact relIndex_le_of_le_right hUK index_ne_zero_of_finite
  have hKI : K.relIndex W = Nat.card T := by
    have hh := relIndex_map_map_of_injective f.ker (⊤ : Subgroup W) W.subtype_injective
    rw [← MonoidHom.range_eq_map, range_subtype, relIndex_top_right, index_ker,
      f.range_eq_top_of_surjective hf, Nat.card_congr (topEquiv : (⊤ : Subgroup T) ≃* T).toEquiv] at hh
    exact hh
  rw [← relIndex_mul_relIndex C K W hCK hKW, hKI]
  exact Nat.mul_le_mul_right _ hCKlower

/-- Equality of the fixed indices forces the smaller moving seed to supplement
all fixed points in the containing group. -/
theorem sup_eq_of_fixed_indices
    (A W C : Subgroup G) [C.Normal] (hWA : W ≤ A) (hCA : C ≤ A)
    (n : ℕ) (hW : n ≤ C.relIndex W) (hA : C.relIndex A ≤ n) : W ⊔ C = A := by
  have hle : W ⊔ C ≤ A := sup_le hWA hCA
  have he : C.relIndex (W ⊔ C) = C.relIndex A := by
    rw [relIndex_sup_right]
    exact le_antisymm (relIndex_le_of_le_right hWA index_ne_zero_of_finite)
      (hA.trans hW)
  have ht := relIndex_mul_relIndex C (W ⊔ C) A le_sup_right hle
  rw [he] at ht
  have hp : C.relIndex A ≠ 0 := index_ne_zero_of_finite
  have hi : (W ⊔ C).relIndex A = 1 := Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero hp) (by simpa using ht)
  exact le_antisymm hle (relIndex_eq_one.mp hi)
end Subgroup
