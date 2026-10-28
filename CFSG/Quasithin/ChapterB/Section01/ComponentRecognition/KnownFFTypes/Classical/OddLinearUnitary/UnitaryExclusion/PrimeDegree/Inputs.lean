module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.SourceInputs
public import Theory.GroupTheory.PGroup.RationalExtraspecial

/-!
# Local geometric inputs for the odd PSU₃ degree bound

The root geometry and prime-to-p order of the covering center are independent
obligations. The first concerns only the genuine projective matrix model;
the second retains the arbitrary source central cover. Neither input assumes
a representation dimension or any form of the requested degree inequality.

These are the remaining local inputs to the extraspecial proof of the bound
used in Guralnick–Malle, Classification of 2F-modules I, Proposition 4.3,
and Aschbacher–Smith K.2, printed p.453. PrimeDegree owns their final assembly.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
universe u v

/-- The concrete odd-prime PSU₃ root configuration. This is group geometry;
no representation or degree conclusion appears in the contract. -/
@[expose] def PrimeDegreeRootGeometry : Prop :=
  ∀ (F : Type) [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {p : ℕ}, p.Prime → 3 < p → Nat.card F = p ^ 2 →
    (∀ x, J.conj x = x ^ p) →
    HasRationalExtraspecialSubgroup
      (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) p

/-- The only covering-theoretic input to the local degree argument. The
universal PSU₃ cover producer can discharge it; no cover is silently replaced
by the special matrix group. -/
@[expose] def PrimeDegreeCenterCoprime : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L]
    {p : ℕ}, SourceHypotheses ρ L p → 3 < p → Nat.Coprime p (Nat.card (center L))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
