module

public import Theory.Character.ModularBlock.CyclicThirteenIntegralRestrictions
public import Theory.Character.ModularBlock.CyclicThirteenColumnEquations
public import Theory.Character.ModularBlock.CyclicThirteenOrdinaryAssembly

/-!
# Construction of the seven ordinary order-thirteen rows

A self-centralizing Sylow subgroup of order thirteen with automizer index three
has four local cubic characters. Special-support induction and integral Fourier
restriction express the ambient exceptional values as signed triple periods
with a common integer shift. The two ordinary column equations eliminate that
shift and leave exactly three constant sign rows, including the principal row.
Every other irreducible character vanishes on the punctured Sylow subgroup.

This module assembles those results into `OrdinaryRows` directly from the local
group hypotheses, without assuming restriction data or column equations.

Source: the exceptional-character argument underlying
Alperin--Brauer--Gorenstein, III.8, printed pp.116--117.
-/

public section

namespace ModularBlock.CyclicThirteen
open PrimeBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- The seven ordinary rows for a self-centralizing Sylow subgroup of order
thirteen with automizer index three. -/
theorem nonempty_ordinaryRows (d : PrimeCongruenceBlockData 13 G)
    (P : Sylow 13 G) (hP : Nat.card P = 13)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (hindex : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 3) :
    Nonempty (OrdinaryRows d P) := by
  obtain ⟨_, ⟨s⟩⟩ := CyclicThirteenNormalizer.sylow_normalizer_data P hP hC hindex
  obtain ⟨v⟩ := nonempty_integralValues d P hP s
  obtain ⟨q⟩ := v.columnEquations hP hC
  exact v.ordinaryRows q

end ModularBlock.CyclicThirteen
