module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts
public import Mathlib.RingTheory.Idempotents
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Two local inputs for the degree-fourteen binary obstruction

For a subgroup P of order 25, let e be its norm in the literal binary group
algebra. Since 25 = 1 in F₂, this norm is an idempotent and its image on a
representation is the P-fixed space. A faithful fourteen-dimensional binary
module should have P-fixed dimension two: a normalizing element of order three
acting without nonidentity fixed points on P, together with coefficient Frobenius,
forces every nontrivial P-weight orbit to contribute at least twelve dimensions.

The required independent finite-algebra calculation excludes a surjection from eF₂[J₂]e
onto M₂(F₂). Such a surjection would follow from absolute irreducibility and
the two-dimensional P-fixed space, by compressing the full endomorphism algebra.
These are unproved contracts for that route, not assertions about a catalogue.
Their assembly remains with `FourteenTraceSeparation`.

Sources: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
p.16; the degree-fourteen entry in corrected Hiss--Malle Table 2. The ATLAS
5²:D₁₂ subgroup gives the proposed local restriction argument. The J₂ data in
GAP CTblLib 1.3.11 (`ctoconja.tbl`, `ctbconja.tbl`) motivates the corner
calculation; no table entry is used as a proof here.
-/

public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
open Sporadic.LeechRelated.J2

/-- The actual subgroup norm in the binary group algebra. -/
@[expose] def fiveNorm (P : Subgroup Carrier) : MonoidAlgebra (ZMod 2) Carrier := by
  classical
  letI := Fintype.ofFinite P
  exact ∑ g : P, MonoidAlgebra.single (g : Carrier) 1

/-- A concrete local subgroup and its required fixed-space calculation.
Absolute irreducibility is deliberately not needed for this restriction. -/
@[expose] def FiveFixedSpaceTwo : Prop :=
  ∃ P : Subgroup Carrier, Nat.card P = 25 ∧
    ∀ σ : Representation (ZMod 2) Carrier (Fin 14 → ZMod 2),
      Function.Injective σ →
        Module.finrank (ZMod 2) (invariants (σ.comp P.subtype)) = 2

/-- The finite corner-algebra obstruction. The idempotence proof is explicit;
it will follow from the order-25 hypothesis in the final assembly. -/
@[expose] def FiveCornerExclusion : Prop :=
  ∀ (P : Subgroup Carrier), Nat.card P = 25 →
    ∀ (he : IsIdempotentElem (fiveNorm P))
      (f : he.Corner →+* Matrix (Fin 2) (Fin 2) (ZMod 2)),
      ¬ Function.Surjective f

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
