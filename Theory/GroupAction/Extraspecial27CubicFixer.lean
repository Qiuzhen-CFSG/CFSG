module

public import Theory.GroupAction.Extraspecial27ElementaryActor
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Elementary two-groups fixing a cubic in an extraspecial group

A faithful elementary two-group of automorphisms of an extraspecial group of
order 27 fixing a cubic subgroup pointwise has order at most two. For the
central cubic, use the center-preserving actor bound. For a noncentral cubic,
the action on the center is faithful: a nonidentity involution fixing the
center has precisely that center as its fixed subgroup. The automorphism
group of the center has order two.

This supplies the point-centralizer bound for Aschbacher–Smith 14.7.15(1),(2),
printed p.1047, without first assuming that the point cubic is normal.
-/

public section
open Subgroup
namespace MulAut
open scoped IsMulCommutative

/-- Fixing any cubic pointwise bounds a faithful elementary actor by two. -/
theorem elementary_two_cubic_fixer_card_le_two
    {P A : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
    [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hP : Nat.card P = 27) (f : A →* MulAut P) (hf : Function.Injective f)
    (X : Subgroup P) (hX : Nat.card X = 3)
    (hfix : ∀ a : A, ∀ x ∈ X, f a x = x) : Nat.card A ≤ 2 := by
  by_cases hXZ : X ≤ center P
  · have he : X = center P := eq_of_le_of_card_ge hXZ
      (by rw [hX,IsExtraspecial.center_order_p 3 P])
    exact elementary_two_center_preserving_card_le_two hP f hf (by simpa only [he] using hfix)
  let b := (MulAut.characteristic (center P)).comp f
  have hb : Function.Injective b := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    by_contra hn
    have hane : a ≠ 1 := by simpa only [mem_bot] using hn
    have hinv : Function.Involutive (f a) := by
      intro x
      have he : f a ^ 2 = 1 := by
        rw [←map_pow,Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A) a,map_one]
      exact congrArg (fun j : MulAut P => j x) (by simpa only [pow_two] using he)
    have he := fixed_eq_center_of_extraspecial27_involution hP (f a) hinv
      (fun hh => hane (hf (hh.trans f.map_one.symm))) (fun z hz =>
        congrArg (fun j : MulAut (center P) => (j ⟨z,hz⟩ : P)) ha)
    apply hXZ
    intro x hx
    rw [←he]
    exact (mem_fixedSubgroup _ _).mpr (hfix a x hx)
  have hcard : Nat.card (MulAut (center P)) = 2 := by
    let : IsCyclic (center P) := isCyclic_of_prime_card (IsExtraspecial.center_order_p 3 P)
    rw [IsCyclic.card_mulAut,IsExtraspecial.center_order_p 3 P]
    decide
  exact (Nat.card_le_card_of_injective b hb).trans_eq hcard
end MulAut
