module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalSubgroups
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Concrete nonabelian odd-subgroup candidates in Held

The first pair consists of words in the literal ATLAS max3 generators.
The second pair consists of words in the max6 generators
`(a*b)^5*(b^2*a)` and `b`. GAP found subgroups of orders 27 and 343;
the cardinalities remain separate proof obligations.

Noncommutativity is proved here in the actual degree-2058 carrier: the
two products move point zero differently. The checks use kernel reduction,
not the external computation. Both subgroups are genuine closures of
words in the existing generators, without recognition by an abstract label.

Sources: GLS3 Table 5.3p; ATLAS `HeG1-p2058B0`, `HeG1-max3W1`, and
`HeG1-max6W1`. The programs, discovery words and provenance are retained
in `OddCubeCandidates/source`.
-/

@[expose] public section

namespace Held.OddCubeCandidates

/-- First generator of the order-27 candidate, in the literal max3 subgroup. -/
def threeFirst : He :=
  let x := a
  let y := LocalPairs.PairCoverage.localWord false
  x * y * x * y ^ (-2 : ℤ) * x * y * x * y⁻¹ * x * y ^ 2 * x * y ^ (-2 : ℤ) * x

/-- Second generator of the order-27 candidate. -/
def threeSecond : He :=
  let x := a
  let y := LocalPairs.PairCoverage.localWord false
  x * y⁻¹ * x * y ^ 2 * x * y ^ 2 * x * y * x * y * x * y⁻¹ * x * y * x * y

/-- First generator of the order-343 candidate, in the literal max6 subgroup. -/
def sevenFirst : He :=
  let x := (a * b) ^ 5 * (b ^ 2 * a)
  b⁻¹ * x * b ^ 2 * x⁻¹ * b ^ 3 * x⁻¹

/-- Second generator of the order-343 candidate. -/
def sevenSecond : He :=
  let x := (a * b) ^ 5 * (b ^ 2 * a)
  b * x * b ^ (-2 : ℤ) * x ^ 2 * b ^ (-2 : ℤ)

/-- A subgroup of the actual Held carrier; its order remains to be certified. -/
def three : Subgroup He := Subgroup.closure {threeFirst, threeSecond}

/-- A subgroup of the actual Held carrier; its order remains to be certified. -/
def seven : Subgroup He := Subgroup.closure {sevenFirst, sevenSecond}

theorem threeFirst_mem : threeFirst ∈ three :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem threeSecond_mem : threeSecond ∈ three :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem sevenFirst_mem : sevenFirst ∈ seven :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem sevenSecond_mem : sevenSecond ∈ seven :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

/-- The two concrete products differ already on point zero. -/
theorem three_mul_ne_mul : threeFirst * threeSecond ≠ threeSecond * threeFirst := by
  have hn : representation (threeFirst * threeSecond) (0 : Fin 2058) ≠
      representation (threeSecond * threeFirst) 0 := by decide +kernel
  intro he
  exact hn (congrArg (fun g => representation g 0) he)

/-- The two concrete products differ already on point zero. -/
theorem seven_mul_ne_mul : sevenFirst * sevenSecond ≠ sevenSecond * sevenFirst := by
  have hn : representation (sevenFirst * sevenSecond) (0 : Fin 2058) ≠
      representation (sevenSecond * sevenFirst) 0 := by decide +kernel
  intro he
  exact hn (congrArg (fun g => representation g 0) he)

theorem three_not_commutative : ¬ IsMulCommutative three := by
  intro h
  exact three_mul_ne_mul (isMulCommutative_iff_of_setLike.mp h
    threeFirst threeFirst_mem threeSecond threeSecond_mem)

theorem seven_not_commutative : ¬ IsMulCommutative seven := by
  intro h
  exact seven_mul_ne_mul (isMulCommutative_iff_of_setLike.mp h
    sevenFirst sevenFirst_mem sevenSecond sevenSecond_mem)

end Held.OddCubeCandidates
