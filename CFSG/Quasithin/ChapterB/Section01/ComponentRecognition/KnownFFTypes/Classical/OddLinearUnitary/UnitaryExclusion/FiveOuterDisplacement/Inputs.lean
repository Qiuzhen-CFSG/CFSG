module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.SourceInputs

/-!
# Independent inputs to the small PSU₃(5) outer-involution calculation

The group input constructs an inverted element in the actual projective
unitary model. The module input bounds displacement on the original module
for every element whose image in the central quotient has order seven.
These are independent obligations, not asserted source theorems.

The quotient-image formulation is deliberate. A lift of an inverted element
need not be inverted in the central cover. Its commutator with the ambient
involution maps to the inverse square of that element. This still has order
seven, and the literal commutator rank bound applies before taking a quotient.
Thus the assembly needs no identification of the cover with its quotient and
no assertion that a chosen lift has order seven.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11, used in Aschbacher–Smith K.2, printed p.453. The module
input must prove the necessary small-degree and field-of-definition facts;
absolute irreducibility is not an input.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

universe u v

/-- The concrete group calculation, with no representation hypothesis.
Simplicity is inherited from the source's quasisimple central quotient. -/
def FiveModelOuterSevenInversion : Prop :=
  ∀ {F : Type} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    [IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)],
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
      ∀ a : MulAut (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J),
        a ^ 2 = 1 → (¬ ∃ s, a = MulAut.conj s) →
          ∃ s, orderOf s = 7 ∧ a s = s⁻¹

/-- The representation calculation on all source covers. It concerns every
lift of a projective order-seven element, not just order-seven lifts. -/
def FiveSmallModuleProjectiveSevenBound : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L],
    SourceHypotheses ρ L 5 → 20 ≤ Module.finrank (ZMod 2) V →
      Module.finrank (ZMod 2) V ≤ 24 →
      ∀ x : L, orderOf (QuotientGroup.mk' (center L) x) = 7 →
        18 ≤ fixedCodim (ρ.comp L.subtype) (zpowers x)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
