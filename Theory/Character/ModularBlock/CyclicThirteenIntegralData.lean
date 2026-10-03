module

public import Theory.Character.CyclicThirteenNormalizerPeriods
public import Theory.Character.ModularBlock.CyclicThirteenOrdinaryData

/-!
# Integral restrictions before column orthogonality

The special-support construction gives four exceptional characters. Restriction
multiplicities express their values as signed local periods plus a common
integer shift, and all other characters as integer constants on the punctured
subgroup. `IntegralValues` records this intermediate conclusion.
`ColumnEquations` records the two ordinary orthogonality equations that eliminate
the shift. Neither interface assumes the desired seven-row enumeration.

Source: the exceptional-character proof underlying
Alperin--Brauer--Gorenstein, III.8, printed pp.116--117.
-/

public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.CyclicThirteen
open PrimeBlockConstruction CyclicThirteenNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- Integer restriction values, before the common shift has been eliminated. -/
structure IntegralValues (d : PrimeCongruenceBlockData 13 G) (P : Sylow 13 G)
    (s : PeriodRows (P : Subgroup G)) where
  exceptionalRows : Fin 4 ↪ d.I
  commonDegree : ℕ
  degree_pos : 0 < commonDegree
  degree : ∀ k, d.chi (exceptionalRows k) (ConjClasses.mk 1) = (commonDegree : ℂ)
  sign : ℤ
  sign_unit : sign = 1 ∨ sign = -1
  shift : ℤ
  exceptional_value : ∀ (k : Fin 4) (u : P), u ≠ 1 →
    d.chi (exceptionalRows k) (ConjClasses.mk (u : G)) =
      (shift : ℂ) + (sign : ℂ) * s.chi k (ConjClasses.mk (inclusion (P : Subgroup G) u))
  remainder : {i : d.I // i ∉ Set.range exceptionalRows} → ℤ
  remainder_value : ∀ (i : {i : d.I // i ∉ Set.range exceptionalRows}) (u : P), u ≠ 1 →
    d.chi i.val (ConjClasses.mk (u : G)) = (remainder i : ℂ)

/-- The integer equations supplied by column and degree orthogonality. -/
structure ColumnEquations {d : PrimeCongruenceBlockData 13 G} {P : Sylow 13 G}
    {s : PeriodRows (P : Subgroup G)} (v : IntegralValues d P s) where
  degree : {i : d.I // i ∉ Set.range v.exceptionalRows} → ℕ
  degree_value : ∀ i, d.chi i.val (ConjClasses.mk 1) = (degree i : ℂ)
  column : (∑ i, v.remainder i ^ 2) + 4 * v.shift ^ 2 - 2 * v.sign * v.shift = 3
  degree_sum : (∑ i, (degree i : ℤ) * v.remainder i) +
    (4 * v.shift - v.sign) * (v.commonDegree : ℤ) = 0

end ModularBlock.CyclicThirteen
