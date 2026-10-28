module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Coordinates

/-!
# The small stabilizer of the Held order-four profile

The unique zero-count vector is 15; the two vectors of count 32 are 3 and 4.
These three vectors are independent and extend to the displayed basis with
vector 1. Thus a preserving automorphism fixes the first vector and either
fixes or swaps the next two. Only the fourth image remains to be chosen.
A kernel check of these 32 tuples, retaining triviality of the kernel, proves
that the fourth power fixes the basis. This is a computation in sixteen
vectors, not an enumeration of automorphisms of the Held representative.

Source: the literal profile calculated in `OrderFourProfile`; the argument
is elementary binary linear algebra, for the full A.3.9 solvability consumer.
-/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile
open FrattiniCoordinates

private def basis : Fin 4 → Coordinate := ![vector 15, vector 3, vector 4, vector 1]
private def evaluate (w : Fin 4 → Coordinate) (v : Coordinate) : Coordinate :=
  w 0 ^ (v.toAdd 3).val * w 1 ^ (v.toAdd 1 + v.toAdd 3).val *
    w 2 ^ (v.toAdd 2 + v.toAdd 3).val * w 3 ^ (v.toAdd 0 + v.toAdd 1).val
private theorem evaluate_basis : ∀ v : Coordinate, evaluate basis v = v := by
  decide +kernel
private theorem evaluate_map (b : MulAut Coordinate) (v : Coordinate) :
    evaluate (fun i => b (basis i)) v = b v := by
  calc
    evaluate (fun i => b (basis i)) v = b (evaluate basis v) := by
      simp only [evaluate, map_mul, map_pow]
    _ = b v := congrArg b (evaluate_basis v)

private theorem small_certificate : ∀ (d : Coordinate) (s : Bool),
    let w : Fin 4 → Coordinate := if s then ![vector 15, vector 4, vector 3, d]
      else ![vector 15, vector 3, vector 4, d]
    (∀ x, evaluate w x = 1 ↔ x = 1) → ∀ j, (evaluate w)^[4] (basis j) = basis j := by
  decide +kernel
private theorem zero_profile : ∀ v : Coordinate,
    countTable (vectorCode v) = 0 ↔ v = vector 15 := by decide +kernel
private theorem pair_profile : ∀ v : Coordinate,
    countTable (vectorCode v) = 32 ↔ v = vector 3 ∨ v = vector 4 := by decide +kernel

public theorem profile_preserving_pow_four (b : MulAut Coordinate)
    (hb : ∀ v, countTable (vectorCode (b v)) = countTable (vectorCode v)) : b ^ 4 = 1 := by
  have h15 : b (vector 15) = vector 15 := by
    apply (zero_profile _).mp
    rw [hb]
    decide +kernel
  have h3 : b (vector 3) = vector 3 ∨ b (vector 3) = vector 4 := by
    apply (pair_profile _).mp
    rw [hb]
    decide +kernel
  have h4 : b (vector 4) = vector 3 ∨ b (vector 4) = vector 4 := by
    apply (pair_profile _).mp
    rw [hb]
    decide +kernel
  have hne : b (vector 3) ≠ b (vector 4) := by
    exact fun h => (by decide +kernel : vector 3 ≠ vector 4) (b.injective h)
  have hw : ∃ s : Bool, (fun i => b (basis i)) =
      if s then ![vector 15, vector 4, vector 3, b (vector 1)]
      else ![vector 15, vector 3, vector 4, b (vector 1)] := by
    rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4
    · exact False.elim (hne (h3.trans h4.symm))
    · refine ⟨false, ?_⟩
      funext i
      fin_cases i <;> simp [basis, h15, h3, h4]
    · refine ⟨true, ?_⟩
      funext i
      fin_cases i <;> simp [basis, h15, h3, h4]
    · exact False.elim (hne (h3.trans h4.symm))
  obtain ⟨s, hs⟩ := hw
  have heval : evaluate (if s then ![vector 15, vector 4, vector 3, b (vector 1)]
      else ![vector 15, vector 3, vector 4, b (vector 1)]) = b := by
    rw [← hs]
    funext v
    exact evaluate_map b v
  have hfix := small_certificate (b (vector 1)) s
  dsimp only at hfix
  rw [heval] at hfix
  have hf := hfix (fun x => b.map_eq_one_iff)
  have hiter (r : Nat) (v : Coordinate) : b^[r] v = (b ^ r) v := by
    induction r with
    | zero => rfl
    | succ r ih => rw [Function.iterate_succ_apply', ih, pow_succ', MulAut.mul_apply]
  have hgen : ∀ j, (b ^ 4) (basis j) = basis j := by
    intro j
    rw [← hiter]
    exact hf j
  apply MulEquiv.ext
  intro v
  change (b ^ 4) v = v
  rw [← evaluate_map (b ^ 4), show (fun i => (b ^ 4) (basis i)) = basis from funext hgen]
  exact evaluate_basis v
end Held.SylowAutomorphismSolvability.OrderFourProfile
