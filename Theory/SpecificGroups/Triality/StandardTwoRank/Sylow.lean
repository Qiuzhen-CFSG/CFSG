module

public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.CentralKernel
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.ElementaryPlacement
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.RadicalBounds
public import Theory.SpecificGroups.Triality.StandardTwoRank
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PrimeRankElementary

/-!
# The exact two-rank of genuine binary triality

The positive subgroup is a Sylow two-subgroup by the proved Bruhat odd
index. The square obstruction places each elementary subgroup in one of the
two concrete radicals. Its order is bounded there by q⁵: map into the carrier
and restrict to that radical. The trace-pairing bounds and the elementary
tail of order q⁵ therefore give two-rank exactly 5*n for every n > 0,
including n = 1.

The conditional reduction is retained, and its two inputs are discharged by
the concrete elementary placement and radical bounds. The lower bound and
central kernel calculation are re-exported. This computes the carrier rank;
the sharper automorphism-rank assertion in G.9 requires a separate argument.

Sources: GLS3 §§2.3–2.6 (`refs/KGroup/GLS3/chapter2.tex`), and the
triality rank used in Aschbacher–Smith G.9, printed p.356
(`refs/quasithin.pdf`).
-/

public section

open Triality.Standard.Parabolics Theory.GroupTheory
namespace Triality.Standard.TwoRank
noncomputable section

/-- Conditional upper-bound assembly from actual elementary subgroups of the
Sylow group and its two radicals. -/
theorem twoRank_le_of_radical_bounds (n : ℕ) (hn : 0 < n)
    (hcover : ∀ E : Subgroup (unipotent (binaryParameters n hn)),
      IsElementaryAbelian 2 E →
      E.map (unipotent (binaryParameters n hn)).subtype ≤ radical (binaryParameters n hn) .arms ∨
      E.map (unipotent (binaryParameters n hn)).subtype ≤ radical (binaryParameters n hn) .central)
    (hbound : ∀ a (E : Subgroup (radical (binaryParameters n hn) a)),
      IsElementaryAbelian 2 E → Nat.card E ≤ (binaryParameters n hn).q ^ 5) :
    primeRank 2 (BinaryCarrier n hn) ≤ 5 * n := by
  rw [(unipotentSylow (binaryParameters n hn) rfl).primeRank_eq]
  change primeRank 2 (unipotent (binaryParameters n hn)) ≤ 5 * n
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let : IsElementaryAbelian 2 E := hE
  let J := E.map (unipotent (binaryParameters n hn)).subtype
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.map_subtype
  have he := Nat.card_congr
    (E.equivMapOfInjective (unipotent (binaryParameters n hn)).subtype Subtype.val_injective).toEquiv
  have hb (a) (ha : J ≤ radical (binaryParameters n hn) a) : Nat.card E ≤ 2 ^ (5 * n) := by
    have h := hbound a (J.subgroupOf (radical (binaryParameters n hn) a))
      (IsElementaryAbelian.subgroupOf ha)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ha).toEquiv, ← he] at h
    simpa only [binaryParameters_q, ← pow_mul, Nat.mul_comm n 5] using h
  obtain h | h := hcover E hE
  · exact hb .arms h
  · exact hb .central h

/-- The intrinsic upper bound for genuine binary triality, including n = 1. -/
theorem twoRank_le_five_mul (n : ℕ) (hn : 0 < n) :
    primeRank 2 (BinaryCarrier n hn) ≤ 5 * n :=
  twoRank_le_of_radical_bounds n hn
    (elementary_unipotent_le_radical n hn) (binary_radical_elementary_card_le n hn)

/-- The exact two-rank of the genuine graph-field carrier ³D₄(2ⁿ),
with its elementary restriction and central quotient, for every n > 0. -/
theorem twoRank_eq_five_mul (n : ℕ) (hn : 0 < n) :
    primeRank 2 (BinaryCarrier n hn) = 5 * n :=
  Nat.le_antisymm (twoRank_le_five_mul n hn) (twoRank_ge_five_mul n hn)

end
end Triality.Standard.TwoRank
