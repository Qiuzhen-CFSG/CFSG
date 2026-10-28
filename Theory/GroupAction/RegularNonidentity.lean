module
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Data.Fintype.Option

/-!
# Invariant subgroups of a regular nonidentity conjugation action

If a finite group K acts freely by conjugation on W minus its identity and
|K|+1=|W|, every nontrivial invariant subgroup is all of W. A commuting
actor therefore has either trivial fixed subgroup in W or fixes W pointwise.
The proof injects K, together with the identity, into an invariant subgroup.

This is the finite-line argument used for full Cartan actions in DGS,
*Groups and Graphs* (1985), 5.1 and 9.10(4), pp.105 and 148.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

/-- A regular action on the nonidentity elements makes every invariant
subgroup trivial or equal to its ambient subgroup. -/
theorem invariant_eq_bot_or_eq_of_regular_card
    (K W N : Subgroup G) [Finite K] [Finite W]
    (hcard : Nat.card K + 1 = Nat.card W)
    (hNW : N ≤ W) (hn : K ≤ normalizer (N : Set G))
    (hfree : ∀ k ∈ K, ∀ w ∈ W, w ≠ 1 → k*w*k⁻¹ = w → k = 1) :
    N = ⊥ ∨ N = W := by
  classical
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨w,hw,hw1⟩ := N.bot_or_exists_ne_one.resolve_left hN
  let f : Option K → N
    | none => 1
    | some k => ⟨(k : G)*w*(k : G)⁻¹,
        (mem_normalizer_iff.mp (hn k.property) w).mp hw⟩
  have hfi : Function.Injective f := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some k =>
        have hh : 1 = (k : G)*w*(k : G)⁻¹ := congrArg Subtype.val hij
        have hconj := congrArg (fun z : G => (k : G)⁻¹*z*k) hh
        simp only [mul_one, inv_mul_cancel, mul_assoc, inv_mul_cancel_left] at hconj
        exact (hw1 hconj.symm).elim
    | some k =>
      cases j with
      | none =>
        have hh : (k : G)*w*(k : G)⁻¹ = 1 := congrArg Subtype.val hij
        have hconj := congrArg (fun z : G => (k : G)⁻¹*z*k) hh
        simp only [mul_one, inv_mul_cancel, mul_assoc, inv_mul_cancel_left] at hconj
        exact (hw1 hconj).elim
      | some l =>
        have hh : (k : G)*w*(k : G)⁻¹ = (l : G)*w*(l : G)⁻¹ := congrArg Subtype.val hij
        have he : (l : G)⁻¹*k*w*((l : G)⁻¹*k)⁻¹ = w := by
          calc
            _ = (l : G)⁻¹*((k : G)*w*(k : G)⁻¹)*l := by group
            _ = (l : G)⁻¹*((l : G)*w*(l : G)⁻¹)*l := by rw [hh]
            _ = w := by group
        have he1 := hfree _ (K.mul_mem (K.inv_mem l.property) k.property) w (hNW hw) hw1 he
        have hkl : k = l := Subtype.ext (inv_mul_eq_one.mp he1).symm
        exact congrArg some hkl
  let : Finite N := Finite.of_injective (inclusion hNW) (inclusion_injective _)
  have hle : Nat.card (Option K) ≤ Nat.card N := Nat.card_le_card_of_injective f hfi
  have hOption : Nat.card (Option K) = Nat.card K + 1 := by
    let : Fintype K := Fintype.ofFinite K
    simp only [Nat.card_eq_fintype_card, Fintype.card_option]
  exact eq_of_le_of_card_ge hNW (by rw [←hcard,←hOption]; exact hle)

/-- A commuting actor has either no nonidentity fixed elements or fixes
all of a line with a regular nonidentity action. -/
theorem inf_centralizer_eq_bot_or_le_of_regular_card
    (K W T : Subgroup G) [Finite K] [Finite W]
    (hcard : Nat.card K + 1 = Nat.card W)
    (hn : K ≤ normalizer (W : Set G))
    (hc : K ≤ centralizer (T : Set G))
    (hfree : ∀ k ∈ K, ∀ w ∈ W, w ≠ 1 → k*w*k⁻¹ = w → k = 1) :
    W ⊓ centralizer (T : Set G) = ⊥ ∨ W ≤ centralizer (T : Set G) := by
  have hnC : K ≤ normalizer (centralizer (T : Set G) : Set G) :=
    hc.trans (centralizer (T : Set G)).le_normalizer
  rcases invariant_eq_bot_or_eq_of_regular_card K W (W ⊓ centralizer (T : Set G))
    hcard inf_le_left ((le_inf hn hnC).trans inf_normalizer_le_normalizer_inf) hfree with he | he
  · exact Or.inl he
  · exact Or.inr (he ▸ inf_le_right)

end Subgroup
