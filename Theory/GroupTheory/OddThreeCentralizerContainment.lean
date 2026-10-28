module

public import Theory.GroupAction.KleinFourFactorization
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Containment from three centralizers in an odd subgroup

For two commuting involutions normalizing an odd-order subgroup P, the
three element centralizers factor P. Thus containment of those three
centralizers in Y implies P ≤ Y. This retains the original ambient
conjugation action and permits a nonfaithful action.

Source application: Aschbacher–Smith, J.2.10, printed p.438 (PDF p.449),
the generation-by-hyperplane-centralizers step for O(C_G(Y)). The general
factorization is proved in `KleinFourFactorization`.
-/

public section
namespace Subgroup
open MulAut
variable {G : Type*} [Group G]

/-- Three involution centralizers control an odd invariant subgroup. -/
theorem le_of_three_odd_centralizers (P Y : Subgroup G) [Finite P]
    (hodd : Odd (Nat.card P)) (a b : normalizer (P : Set G))
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b)
    (hfix : ∀ t ∈ ({(a : G), (b : G), ((a * b : normalizer (P : Set G)) : G)} : Set G),
      P ⊓ centralizer ({t} : Set G) ≤ Y) : P ≤ Y := by
  let f := P.normalizerMonoidHom
  have hinv (t : normalizer (P : Set G)) (ht : t ^ 2 = 1) :
      Function.Involutive (f t) := by
    intro x
    have h : f t ^ 2 = 1 := by rw [← map_pow, ht, map_one]
    exact congrArg (fun e : MulAut P => e x) h
  intro x hx
  obtain ⟨u, v, w, hu, hv, hw, he⟩ := exists_fixed_mul_fixed_mul_fixed_of_odd_card
    hodd (f a) (f b) (hinv a ha) (hinv b hb) (hab.map f) (⟨x, hx⟩ : P)
  have hmem (t : normalizer (P : Set G)) (ht : (t : G) ∈
      ({(a : G), (b : G), ((a * b : normalizer (P : Set G)) : G)} : Set G))
      (q : P) (hq : f t q = q) : (q : G) ∈ Y := by
    apply hfix (t : G) ht
    refine ⟨q.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have hh := congrArg Subtype.val hq
    change (t : G) * (q : G) * (t : G)⁻¹ = q at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have huY := hmem a (by simp) u hu
  have hvY := hmem b (by simp) v hv
  have hwY := hmem (a * b) (by simp) w (by simpa only [map_mul] using hw)
  have := Y.mul_mem (Y.mul_mem huY hvY) hwY
  simpa only [← Subgroup.coe_mul, ← he] using this

end Subgroup
