module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Sylow-normalizer displacements fix an odd center

An automorphism with trivial displacement on a Sylow-two normalizer modulo
that Sylow fixes the whole odd-order center. Each central displacement lies
both in the center and in the two-group, whose intersection is trivial.
The SU₃(2) Borel-core action in DGS 6.1 uses this assertion to retain, and
fix, the cubic scalar center.
-/

public noncomputable section
open Subgroup
namespace MulAut
variable {D : Type*} [Group D] [Finite D]

/-- Trivial normalizer displacement fixes every central element when the center has odd order. -/
theorem fixes_center_of_sylow_normalizer_displacements (S : Sylow 2 D)
    (a : MulAut D) (ho : Odd (Nat.card (center D)))
    (hd : ∀ x ∈ normalizer (S : Set D), x⁻¹ * a x ∈ S) :
    ∀ z ∈ center D, a z = z := by
  have hdis : Disjoint (center D) (S : Subgroup D) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k,hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  intro z hz
  have haz : a z ∈ center D := (centerCongr a ⟨z,hz⟩).property
  have hc := hdis.le_bot ⟨(center D).mul_mem ((center D).inv_mem hz) haz,
    hd z (center_le_normalizer _ hz)⟩
  exact (inv_mul_eq_one.mp (mem_bot.mp hc)).symm
end MulAut

