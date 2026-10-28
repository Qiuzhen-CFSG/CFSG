module

public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.SpecificGroups.PSL3Two.AlternatingFiveObstruction
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Cubic rank of the two small binary Levi factors

The orders of PSL₂(2) and PSL₃(2) divide 6 and 168, respectively.
Neither is divisible by nine, so both groups have three-rank at most one.
This is the small Levi obstruction in the natural-plus-dual branch of
Aschbacher--Smith, 15.2.23, printed p.1117, using B.5.1(6).
-/

public section
open Subgroup
namespace BinaryLinear.SmallLeviRank

theorem two :
    primeRank 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)) ≤ 1 := by
  apply primeRank_le_one_of_square_not_dvd
  intro h
  have hd := h.trans (card_quotient_dvd_card
    (center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))))
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at hd
  norm_num [Nat.factorial] at hd

theorem three :
    primeRank 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ≤ 1 := by
  apply primeRank_le_one_of_square_not_dvd
  intro h
  have hd := h.trans Matrix.PSL3Two.card_PSL_dvd
  norm_num at hd

/-- The interior-node Levi factor for natural-plus-dual in degrees four and five. -/
theorem interior {n : ℕ} (hn : n = 4 ∨ n = 5) :
    primeRank 3 (Matrix.ProjectiveSpecialLinearGroup (Fin (n - 2)) (ZMod 2)) ≤ 1 := by
  rcases hn with rfl | rfl
  · exact two
  · exact three

end BinaryLinear.SmallLeviRank
