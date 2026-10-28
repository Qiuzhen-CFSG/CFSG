module

public import Theory.Character.ModularBlock.CyclicSevenIntegralRestrictions
public import Theory.Character.ModularBlock.CyclicSevenColumnEquations
public import Theory.Character.ModularBlock.CyclicSevenOrdinaryAssembly

/-!
# Construction of the five ordinary order-seven rows

A self-centralizing Sylow subgroup of order seven with automizer index two
has three local quadratic characters. Special-support induction and integral Fourier
restriction express the ambient exceptional values as signed quadratic periods
with a common integer shift. The two ordinary column equations eliminate that
shift and leave exactly two constant sign rows, including the principal row.
Every other irreducible character vanishes on the punctured Sylow subgroup.

This module assembles those results into `OrdinaryRows` directly from the local
group hypotheses, without assuming restriction data or column equations.

Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from `Theory.Character.ModularBlock.CyclicThirteenOrdinaryConstruction`,
whose source is Alperin--Brauer--Gorenstein, III.8, pp.116--117.
-/

public section

namespace ModularBlock.CyclicSeven
open PrimeBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- The five ordinary rows for a self-centralizing Sylow subgroup of order
seven with automizer index two. -/
theorem nonempty_ordinaryRows (d : PrimeCongruenceBlockData 7 G)
    (P : Sylow 7 G) (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (hindex : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 2) :
    Nonempty (OrdinaryRows d P) := by
  obtain ⟨_, ⟨s⟩⟩ := CyclicSevenNormalizer.sylow_normalizer_data P hP hC hindex
  obtain ⟨v⟩ := nonempty_integralValues d P hP s
  obtain ⟨q⟩ := v.columnEquations hP hC
  exact v.ordinaryRows q

end ModularBlock.CyclicSeven
