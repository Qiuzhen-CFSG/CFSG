module
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.FixedPointFree
/-!
# Elementary two-actors on a ternary plane

An elementary two-group acting on a group of order nine preserves a subgroup
of order three. If an actor has a proper nontrivial fixed subgroup, that
subgroup is stable under all the commuting actors. Otherwise each actor is
the identity or a fixed-free involution, hence inversion, and any cubic
subgroup works. Faithfulness is not required.

Source application: the reducible Sylow exclusion in Aschbacher–Smith
14.7.15(2), printed p.1047.
-/
public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace MulAut
/-- An elementary two-group on a group of order nine preserves a line. -/
theorem exists_stable_three_of_elementary_two
    {A W : Type*} [Group A] [IsElementaryAbelian 2 A] [Group W] [Finite W]
    (α : A →* MulAut W) (hW : Nat.card W = 9) :
    ∃ J : Subgroup W, Nat.card J = 3 ∧ ∀ a : A, ∀ x ∈ J, α a x ∈ J := by
  have hinvol (a : A) : Function.Involutive (α a) := by
    intro x
    have he := congrArg α (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a)
    rw [map_pow,map_one,pow_two] at he
    exact congrArg (fun f : MulAut W => f x) he
  by_cases hm : ∃ a : A, fixedSubgroup (α a) ≠ ⊥ ∧ fixedSubgroup (α a) ≠ ⊤
  · obtain ⟨a,ha0,ha1⟩ := hm
    let J := fixedSubgroup (α a)
    have hc : Nat.card J = 3 := by
      have hd := J.card_subgroup_dvd_card
      rw [hW] at hd
      obtain ⟨n,hn,hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (show Nat.card J ∣ 3^2 from hd)
      interval_cases n
      · exact (ha0 (card_eq_one.mp hc)).elim
      · exact hc
      · exact (ha1 (eq_of_le_of_card_ge le_top (by rw [card_top,hW,hc]; norm_num))).elim
    refine ⟨J,hc,?_⟩
    intro b x hx
    apply (mem_fixedSubgroup _ _).mpr
    have he : α a * α b = α b * α a := by rw [←map_mul,←map_mul,mul_comm a b]
    have he' := congrArg (fun f : MulAut W => f x) he
    change α a (α b x) = α b (α a x) at he'
    rw [(mem_fixedSubgroup _ _).mp hx] at he'
    exact he'
  · obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := W) 3 (by rw [hW]; decide)
    refine ⟨zpowers x,by rw [Nat.card_zpowers,hx],?_⟩
    intro a y hy
    have ha : fixedSubgroup (α a) = ⊥ ∨ fixedSubgroup (α a) = ⊤ := by
      by_contra! hn
      exact hm ⟨a,hn⟩
    rcases ha with ha | ha
    · have hf : MonoidHom.FixedPointFree (α a) := by
        intro z hz
        exact mem_bot.mp (ha ▸ (mem_fixedSubgroup _ _).mpr hz)
      rw [hf.coe_eq_inv_of_involutive (hinvol a)]
      exact (zpowers x).inv_mem hy
    · have he : α a y = y := (mem_fixedSubgroup _ _).mp (ha ▸ mem_top y)
      rwa [he]
end MulAut
