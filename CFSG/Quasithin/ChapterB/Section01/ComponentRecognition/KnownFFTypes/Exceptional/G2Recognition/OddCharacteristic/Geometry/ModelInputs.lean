module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.G2Recognition.OddCharacteristic.Inputs
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Model geometry contracts for odd-field G₂

These are the remaining intrinsic model obligations for the rank and generation
argument. They are propositions to prove, not instances or imported assumptions.
The conjugators in `InnerConjugateBound` belong to the original group. This is
essential when lifting them to a particular representation normalizer.

The rank route uses elementary two-subgroups of order at most eight and a
cyclic outer quotient. In characteristic three the latter includes the
exceptional root-length-changing automorphism; it is not merely the coefficient
field group (GLS III, Theorem 2.5.12(e)). The generation contract is the proposed
sufficient bound for Guralnick–Malle, Classification of 2F-modules I, §2 and
Proposition 4.6. That proposition is not a proof of the uniform contract.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.G2Odd.Geometry
open Subgroup
universe v

/-- Generation by a prescribed number of conjugates under inner automorphisms,
for all nonidentity involutions of the full automorphism group. -/
def InnerConjugateBound (S : Type*) [Group S] (n : ℕ) : Prop :=
  ∀ t : MulAut S, t ≠ 1 → t ^ 2 = 1 →
    ∃ g : Fin n → S, (MulAut.conj : S →* MulAut S).range ≤
      closure (Set.range fun i => MulAut.conj (g i) * t * (MulAut.conj (g i))⁻¹)

/-- The actual odd octonion group has elementary two-subgroups of order at most eight. -/
def ModelElementaryTwoBound : Prop :=
  ∀ (F : Type v) [Field F] [Finite F], 2 < Nat.card F → ringChar F ≠ 2 →
    ∀ E : Subgroup (Atlas.G2.Model F), IsElementaryAbelian 2 E → Nat.card E ≤ 8

/-- The full outer quotient is cyclic, including the characteristic-three graph case. -/
def ModelOuterCyclic : Prop :=
  ∀ (F : Type v) [Field F] [Finite F], 2 < Nat.card F → ringChar F ≠ 2 →
    IsCyclic (MulAut.Outer (Atlas.G2.Model F))

/-- The uniform model generation obligation; no linear representation or cover is an input. -/
def ModelEightConjugateBound : Prop :=
  ∀ (F : Type v) [Field F] [Finite F], 3 < Nat.card F → ringChar F ≠ 2 →
    InnerConjugateBound (Atlas.G2.Model F) 8

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.G2Odd.Geometry
