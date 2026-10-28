module

public import ABG.Basic

/-!
# The three main theorems of Alperin–Brauer–Gorenstein

The statements are from Chapter I, article page 3 (PDF page 4), of
`refs/latex/alperin-brauer-gorenstein.tex`. For finite simple groups with
quasi-dihedral Sylow 2-subgroups, they describe involution centralizers, group
orders, and identification with PSL₃(q), PSU₃(q), or M₁₁. The shared models and
characteristic parameters are re-exported from `ABG.Basic`.

The proof campaign follows the paper's local group theory, character theory,
and identification steps. These three endpoints remain unproved. The order
formula is an equality in ℚ, preserving the printed sign and division.
-/

namespace ABG

universe u

set_option warningAsError false in
/-- **First Main Theorem** (article p. 3): each involution centralizer is an
odd central quotient of `GL(2,q)` for `q ≡ -1 (mod 4)` or of `GU(2,q)` for
`q ≡ 1 (mod 4)`. -/
public theorem first_main_theorem
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hS : HasQuasiDihedralSylowTwoSubgroups G)
    (x : G) (hx : orderOf x = 2) :
    ∃ q d : ℕ, InvolutionCentralizerParameters x q d := by
  sorry

set_option warningAsError false in
/-- **Second Main Theorem** (article p. 3): for characteristic parameters
`q,d` and `q ≡ ε (mod 4)`, where `ε = ±1`, the group has order
`q³(q³ + ε)(q² - 1)/d` or `7920`. -/
public theorem second_main_theorem
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hS : HasQuasiDihedralSylowTwoSubgroups G)
    {q d : ℕ} (hqd : HasCharacteristicParameters G q d)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hqε : (q : ℤ) ≡ ε [ZMOD 4]) :
    (Nat.card G : ℚ) = (1 / (d : ℚ)) * (q : ℚ) ^ 3 *
      ((q : ℚ) ^ 3 + (ε : ℚ)) * ((q : ℚ) ^ 2 - 1) ∨
    Nat.card G = 7920 := by
  sorry

set_option warningAsError false in
/-- **Third Main Theorem** (article p. 3): if `q ≡ -1 (mod 4)`, then `G` is
`PSL(3,q)` or `M₁₁`; if `q ≡ 1 (mod 4)`, then `G` is `PSU(3,q)`. -/
public theorem third_main_theorem
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hS : HasQuasiDihedralSylowTwoSubgroups G)
    {q : ℕ} (hq : HasCharacteristicPower G q) :
    (q % 4 = 3 ∧ (IsPSL3 G q ∨ Nonempty (G ≃* Sporadic.Mathieu.M11))) ∨
    (q % 4 = 1 ∧ IsPSU3 G q) := by
  sorry

end ABG
