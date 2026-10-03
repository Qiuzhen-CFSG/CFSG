module

public import Stellmacher.SectionOne.NineCoreOffenderExistence

/-!
# Canonical offender generation for the faithful nine-core action

The faithful order-nine action supplies a nontrivial canonical offender.
The group-theoretic generation step then shows that its normal closure,
`oneE`, supplements the Sylow two-subgroup. This is the generation input
for the order-sixteen nine-core wreath recognition.
-/

namespace Stellmacher.SectionOne

universe u

public theorem nineCore_canonical_generation
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (R : Sylow 2 K)
    (hgen : oddCore K ⊔ (R : Subgroup K) = ⊤)
    (hunique : IsUniqueMaximalContaining (R : Subgroup K) ⊤)
    (hVcard : Nat.card V = 16) (hoddcard : Nat.card (oddCore K) = 9)
    (X : Subgroup K) (hX : IsElementaryAbelian 2 X) (hXcard : Nat.card X = 4) :
    oneE (V := V) (R : Subgroup K) ⊔ (R : Subgroup K) = ⊤ := by
  exact nineCore_canonical_generation_of_oneJ_ne_bot h R hgen hunique hoddcard
    (nineCore_oneJ_ne_bot h R hgen hunique hVcard hoddcard X hX hXcard)

#print axioms nineCore_canonical_generation

end Stellmacher.SectionOne
