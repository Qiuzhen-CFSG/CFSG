module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.RankOneFourNormalizer.Centralizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Action

/-!
# The unique Sylow-normal four-group and its strictly larger normalizer in HS

The checked elementary catalogue has orders two, four and eight. Thus a normal
elementary four-group in the marked Sylow is the middle entry. Swapping the
second and third elementary generators defines an actual automorphism of the
eight, which is induced by its full ambient normalizer. This automorphism moves
the four-group, proving strictness of the normalizer containment.

Sources: the degree-100 ATLAS HS carrier; GLS3, Table 5.3m;
Aschbacher–Smith, proof of 15.3.43, p.1140.
-/

namespace Sporadic.LeechRelated.HS.RankOneFourNormalizer
open Subgroup EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData BlockNormalizer
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option Elab.async false

private def productIndex (i j : Fin 8) : Fin 8 :=
  ⟨(Nat.xor i.val j.val) % 8, Nat.mod_lt _ (by decide)⟩

private theorem small_mul (i j : Fin 8) : small i * small j = small (productIndex i j) := by
  have h : ∀ (i j : Fin 8) (x : Fin 100),
      ((small i * small j : Carrier) : Equiv.Perm (Fin 100)) x =
        (small (productIndex i j) : Equiv.Perm (Fin 100)) x := by
    apply allFin₃
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i j))

private theorem small_inv (i : Fin 8) : (small i)⁻¹ = small i := by
  have h : ∀ (i : Fin 8) (x : Fin 100),
      ((small i)⁻¹ : Equiv.Perm (Fin 100)) x =
        (small i : Equiv.Perm (Fin 100)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

private theorem small_injective : Function.Injective small := by
  have h : ∀ i j : Fin 8,
      (small i : Equiv.Perm (Fin 100)) 1 = (small j : Equiv.Perm (Fin 100)) 1 → i = j := by
    apply allFin₂
    decide +kernel
  intro i j he
  exact h i j (congrArg (fun x : Carrier => (x : Equiv.Perm (Fin 100)) 1) he)

private theorem small_of_mem_elementary (i : Fin 3) {x : Carrier} (hx : x ∈ elementary i) :
    ∃ j : Fin 8, j.val < 2 ^ (i.val + 1) ∧ small j = x := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨![1, 2, 4] k, ?_, ?_⟩
    · have ht : ∀ i k : Fin 3, k ≤ i →
          (![1, 2, 4] k : Fin 8).val < 2 ^ (i.val + 1) := by decide
      exact ht i k hk
    · fin_cases k <;> rfl
  | one => exact ⟨0, Nat.two_pow_pos _, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := hy
    refine ⟨productIndex j k, ?_, (small_mul j k).symm⟩
    have ht : ∀ (i : Fin 3) (j k : Fin 8),
        j.val < 2 ^ (i.val + 1) → k.val < 2 ^ (i.val + 1) →
          (productIndex j k).val < 2 ^ (i.val + 1) := by decide
    exact ht i j k hj hk
  | inv x _ hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact ⟨j, hj, (small_inv j).symm⟩

/-- Exact cardinalities of the three marked elementary subgroups. -/
public theorem elementary_card (i : Fin 3) : Nat.card (elementary i) = 2 ^ (i.val + 1) := by
  have hb : 2 ^ (i.val + 1) ≤ 8 := by fin_cases i <;> decide
  let f : Fin (2 ^ (i.val + 1)) → elementary i := fun j =>
    ⟨small ⟨j.val, lt_of_lt_of_le j.isLt hb⟩, small_mem_elementary _ i j.isLt⟩
  have hi : Function.Injective f := by
    intro j k he
    have hv : small ⟨j.val, lt_of_lt_of_le j.isLt hb⟩ =
        small ⟨k.val, lt_of_lt_of_le k.isLt hb⟩ := congrArg Subtype.val he
    exact Fin.ext (congrArg (fun x : Fin 8 => x.val) (small_injective hv))
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨j, hj, he⟩ := small_of_mem_elementary i x.property
    exact ⟨⟨j.val, hj⟩, Subtype.ext he⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)).symm.trans (Nat.card_fin _)

/-- The relative normality and order hypotheses identify the fixed four-group. -/
public theorem normal_four_eq (W : Subgroup Carrier) (hW : W ≤ subgroup)
    (hn : (W.subgroupOf subgroup).Normal) (he : IsElementaryAbelian 2 W)
    (hc : Nat.card W = 4) : W = elementary 1 := by
  let := he
  have hne : W.subgroupOf subgroup ≠ ⊥ := by
    intro hh
    have hw := congrArg (Subgroup.map subgroup.subtype) hh
    rw [map_subgroupOf_eq_of_le hW, Subgroup.map_bot] at hw
    have hcard : Nat.card W = 1 := by rw [hw]; simp
    omega
  obtain ⟨i, hi⟩ := normal_elementary_catalogue (W.subgroupOf subgroup) hne hn
    (IsElementaryAbelian.subgroupOf hW)
  rw [map_subgroupOf_eq_of_le hW] at hi
  have hc' := hc
  rw [hi, elementary_card] at hc'
  have hi1 : i = 1 := by
    have hp : 2 ^ (i.val + 1) = 2 ^ 2 := hc'
    have hv := Nat.pow_right_injective (by decide : 1 < 2) hp
    exact Fin.ext (by omega)
  exact hi.trans (congrArg elementary hi1)

private def swapIndex : Fin 8 → Fin 8 := ![0, 1, 4, 5, 2, 3, 6, 7]

private def swapEquiv : Equiv.Perm (Fin 8) where
  toFun := swapIndex
  invFun := swapIndex
  left_inv := by decide
  right_inv := by decide

private noncomputable def smallEquiv : Fin 8 ≃ elementary 2 :=
  Equiv.ofBijective (fun j => ⟨small j, small_mem_elementary j 2 j.isLt⟩)
    ⟨fun _ _ h => small_injective (congrArg Subtype.val h), fun x => by
      obtain ⟨j, _, hj⟩ := small_of_mem_elementary 2 x.property
      exact ⟨j, Subtype.ext hj⟩⟩

private theorem swapped_mul (i j : Fin 8) :
    small (swapIndex (productIndex i j)) = small (swapIndex i) * small (swapIndex j) := by
  have h : ∀ i j : Fin 8,
      swapIndex (productIndex i j) = productIndex (swapIndex i) (swapIndex j) := by decide
  rw [h, small_mul]

private noncomputable def swapAut : MulAut (elementary 2) :=
  { smallEquiv.symm.trans (swapEquiv.trans smallEquiv) with
    map_mul' := by
      intro x y
      obtain ⟨i, rfl⟩ := smallEquiv.surjective x
      obtain ⟨j, rfl⟩ := smallEquiv.surjective y
      have hmul : smallEquiv i * smallEquiv j = smallEquiv (productIndex i j) :=
        Subtype.ext (small_mul i j)
      change smallEquiv (swapEquiv (smallEquiv.symm (smallEquiv i * smallEquiv j))) =
        smallEquiv (swapEquiv (smallEquiv.symm (smallEquiv i))) *
        smallEquiv (swapEquiv (smallEquiv.symm (smallEquiv j)))
      rw [hmul, smallEquiv.symm_apply_apply, smallEquiv.symm_apply_apply,
        smallEquiv.symm_apply_apply]
      exact Subtype.ext (swapped_mul i j) }

private theorem swapAut_two : swapAut (smallEquiv 2) = smallEquiv 4 := by
  change smallEquiv (swapEquiv (smallEquiv.symm (smallEquiv 2))) = smallEquiv 4
  rw [smallEquiv.symm_apply_apply]
  rfl

/-- The full action on the eight moves its marked four-group. -/
public theorem eight_normalizer_not_le_four_normalizer :
    ¬ normalizer (elementary 2 : Set Carrier) ≤ normalizer (elementary 1 : Set Carrier) := by
  intro hn
  obtain ⟨g, hg⟩ := baseNormalizer_action_surjective swapAut
  have hmove := congrArg (fun φ : MulAut (elementary 2) => φ (smallEquiv 2)) hg
  rw [swapAut_two] at hmove
  have hm : g.val * e1 * g.val⁻¹ = e2 := congrArg Subtype.val hmove
  have he1 : e1 ∈ elementary 1 := subset_closure ⟨1, by decide, rfl⟩
  have he2 : e2 ∈ elementary 1 := hm ▸ ((hn g.property) e1).mp he1
  obtain ⟨j, hj, he⟩ := small_of_mem_elementary 1 he2
  have hj4 : j = 4 := small_injective he
  subst j
  norm_num at hj

end Sporadic.LeechRelated.HS.RankOneFourNormalizer
