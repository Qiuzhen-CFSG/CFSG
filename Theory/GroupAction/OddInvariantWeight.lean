module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Fintype.Card

/-!
# A fixed point from an odd invariant weight

Replace each point by a fibre whose size is its invariant weight. The total
cardinality is odd, so a two-group fixes a point of this fibre space and hence
of the original set. The application is to half-dimensions of cubic fixed
spaces in the degree-six branch of Aschbacher--Smith G.9.4, printed p.355.
-/

public section
open scoped BigOperators
namespace MulAction
variable {D X : Type*} [Group D] [MulAction D X] [Fintype X]

theorem exists_fixed_of_odd_weight (hD : IsPGroup 2 D)
    (w : X → ℕ) (hw : ∀ (d : D) (x : X), w (d • x) = w x)
    (hs : Odd (∑ x, w x)) : ∃ x : X, ∀ d : D, d • x = x := by
  let Y := Σ x, Fin (w x)
  let : MulAction D Y := {
    smul d y := ⟨d • y.1, ⟨y.2.val, (hw d y.1).symm ▸ y.2.isLt⟩⟩
    one_smul y := by
      apply Sigma.ext (one_smul D y.1)
      exact (Fin.heq_ext_iff (congrArg w (one_smul D y.1))).mpr rfl
    mul_smul d e y := by
      apply Sigma.ext (mul_smul d e y.1)
      exact (Fin.heq_ext_iff (congrArg w (mul_smul d e y.1))).mpr rfl
      }
  have hy : Nat.card Y = ∑ x, w x := by
    rw [Nat.card_eq_fintype_card]
    simp only [Y,Fintype.card_sigma,Fintype.card_fin]
  obtain ⟨y,hyf⟩ := hD.nonempty_fixed_point_of_prime_not_dvd_card Y
    (by rw [hy, ← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hs)
  exact ⟨y.1,fun d => congrArg Sigma.fst (hyf d)⟩
end MulAction
