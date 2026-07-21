/-
Authors: OpenAI
-/

module

public import BenderSuzuki.PFchapter4section2.Basic

namespace BenderSuzuki
namespace PFchapter4section3

open PFchapter1section1 PFAppendixIII
open PFchapter4section1
open PFchapter4section2

/-!
# Basic interfaces for Peterfalvi, Part II, Chapter IV, Section 3
-/

public theorem theta_bijective_of_odd_iterate
    {E : Type*} [Finite E] (theta : E → E)
    (htheta_odd_order : ∃ r : ℕ, Odd r ∧ 0 < r ∧ ∀ x : E, theta^[r] x = x) :
    Function.Bijective theta := by
  rcases htheta_odd_order with ⟨r, _hodd, hrpos, hiter⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos) with ⟨n, rfl⟩
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hx : (theta^[n]) (theta x) = x := by
      simpa [Function.iterate_succ_apply] using hiter x
    have hy : (theta^[n]) (theta y) = y := by
      simpa [Function.iterate_succ_apply] using hiter y
    rw [← hx, ← hy, hxy]
  · intro y
    refine ⟨(theta^[n]) y, ?_⟩
    simpa [Function.iterate_succ_apply'] using hiter y

end PFchapter4section3
end BenderSuzuki



