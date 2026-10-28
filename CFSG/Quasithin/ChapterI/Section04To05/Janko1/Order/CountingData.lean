module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.Fusion

/-!
# Interfaces for the remaining Bender counting argument

`BenderPrimeData` records the numerical odd-prime local results consumed by
Bender's §4 coset argument. Its parameter is one or three: the relevant
odd centralizer factor has prime order or order fifteen, respectively.
`BenderCountData` records the three consequences (4.4)–(4.6), with the
literal number of ambient involutions, not an assumed ambient group order.

These are explicit intermediate contracts. Neither record is asserted to
exist in this module. Their independent construction belongs to the
odd-prime centralizer and coset-distribution branches. The order assembly
must discharge both before asserting the source order theorem.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, pp.225–228, especially (4.1), (4.2), and (4.4)–(4.6).
-/

namespace CFSG.Quasithin.Janko1CentralizerData

/-- The odd-prime centralizer and inversion counts needed in Bender §4.
The quantifiers concern actual ambient elements and actual Sylow subgroups. -/
public structure BenderPrimeData (G : Type*) [Group G] (d : ℕ) : Prop where
  d_cases : d = 1 ∨ d = 3
  sylow_three : ∀ P : Sylow 3 G, Nat.card P = 3
  sylow_five : ∀ P : Sylow 5 G, Nat.card P = 5
  centralizer_three : ∀ x : G, orderOf x = 3 →
    Nat.card (Subgroup.centralizer ({x} : Set G)) = if d = 1 then 6 else 30
  centralizer_five : ∀ x : G, orderOf x = 5 →
    Nat.card (Subgroup.centralizer ({x} : Set G)) = 10 * d
  inverting_three : ∀ x : G, orderOf x = 3 →
    Nat.card {t : G // orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹} = 6 * d
  commuting_three : ∀ x : G, orderOf x = 3 →
    Nat.card {t : G // orderOf t = 2 ∧ Commute t x} = 2 * d - 1
  commuting_five : ∀ x : G, orderOf x = 5 →
    Nat.card {t : G // orderOf t = 2 ∧ Commute t x} = d

/-- The output of Bender's coset distribution and fixed-point congruence.
The natural subtractions match the source because `d` is positive. -/
public structure BenderCountData (G : Type*) [Group G] (d : ℕ) where
  e : ℕ
  m : ℕ
  e_le_one : e ≤ 1
  m_le : m ≤ d + e + 1
  congruence : 5 ∣ 2 * d + 2 * m - 1
  involutions : Nat.card {x : G // orderOf x = 2} =
    7 * (1 + 8 * (4 * d + 3 * m - 1))

end CFSG.Quasithin.Janko1CentralizerData
