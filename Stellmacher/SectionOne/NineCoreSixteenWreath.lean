module

public import Stellmacher.SectionOne.NineCoreCanonicalGeneration
public import Stellmacher.SectionOne.NineCoreWreathCounting

/-!
# Wreath recognition for the faithful order-sixteen nine-core action

Under the Section One hypotheses, an order-nine odd core supplementing a
Sylow two-subgroup with a unique maximal overgroup, together with an
elementary subgroup of order four, identifies the group acting faithfully
on an elementary module of order sixteen with the literal SL₂(2) wreath C₂.

The faithful action proves nontriviality of the canonical offender and then
canonical generation. Comparing the odd-core and canonical-product cardinal
formulas gives two canonical factors, to which wreath recognition applies.
No offender, canonical-generation, or model hypothesis is added.

Source: Stellmacher (9.1)(8), printed p.47 / PDF page 37 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionOne

universe u

public theorem nineCore_sixteen_wreath
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (R : Sylow 2 K)
    (hgen : oddCore K ⊔ (R : Subgroup K) = ⊤)
    (hunique : IsUniqueMaximalContaining (R : Subgroup K) ⊤)
    (hVcard : Nat.card V = 16) (hoddcard : Nat.card (oddCore K) = 9)
    (X : Subgroup K) (hX : IsElementaryAbelian 2 X) (hXcard : Nat.card X = 4) :
    Nonempty (K ≃* Later.SL2TwoWreathC2) := by
  exact nineCore_wreath_of_canonical_generation h R hgen hunique hoddcard
    (nineCore_canonical_generation h R hgen hunique hVcard hoddcard X hX hXcard)

end Stellmacher.SectionOne
