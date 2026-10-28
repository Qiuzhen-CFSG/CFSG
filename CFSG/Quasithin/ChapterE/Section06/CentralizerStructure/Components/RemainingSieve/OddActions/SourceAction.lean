module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceInputs

/-!
# The literal involution action used by the odd sieve

Conjugation by an involution squares to the identity. The source assertion
that L is not contained in its centralizer makes the induced automorphism
nonidentity, and therefore of order two. This uses the actual embedded action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 1.1.5(3),
printed pp.501–503, as applied in E.6.8, printed p.247.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions
variable {G : Type*} [Group G] {L : Subgroup G} {z : G} {α : MulAut L}

/-- The literal nontrivial conjugation action of a source involution has order two. -/
theorem source_action_order_two (hz : z ^ 2 = 1)
    (hact : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hne : ¬ L ≤ centralizer ({z} : Set G)) : orderOf α = 2 := by
  have hpow : α ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change ((α (α x) : L) : G) = (x : G)
    rw [hact, hact]
    calc
      z * (z * (x : G) * z⁻¹) * z⁻¹ = (z ^ 2) * (x : G) * (z ^ 2)⁻¹ := by
        simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = x := by rw [hz]; simp
  have hα : α ≠ 1 := by
    intro he
    apply hne
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    have hh := hact ⟨x, hx⟩
    rw [he] at hh
    change x = z * x * z⁻¹ at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  exact (Nat.dvd_prime (by decide : Nat.Prime 2)).mp (orderOf_dvd_of_pow_eq_one hpow)
    |>.resolve_left (fun ho => hα (orderOf_eq_one_iff.mp ho))

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions
