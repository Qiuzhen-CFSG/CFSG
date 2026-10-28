module

public import Theory.SpecificGroups.ReeF4.Model
public import Theory.GroupTheory.Covering
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Field.ZMod

/-!
# The Ree involution estimate needed for F-modules

For q = 2^(2m+1), the two involution classes have fixed-space codimension
at least 10 on the 26-dimensional modules. Tensor products and scalar descent
must supply the binary-weighted lower bound for every faithful irreducible
module of every quasisimple central cover. The proposition below states that
remaining estimate; no theorem asserting it is provided here.

The restriction of an absolutely irreducible ambient action need only be
irreducible, so the contract deliberately does not require absolute
irreducibility. The central quotient is identified with the literal model.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Lemmas 8.7--8.8,
internal pp.57--58. Only the F inequality is needed by the consumer.
-/

@[expose] public section
namespace ReeF4
open Subgroup Representation Theory.GroupTheory
universe u v

/-- The missing involution estimate, including central covers and scalar descent.
This is a mathematical input specification, not a proved model fact. -/
def CoverInvolutionBound (m : ℕ) : Prop :=
  ∀ (L : Type u) [Group L] [Finite L] [IsQuasisimple L],
    Nonempty (L ⧸ center L ≃* Model m) →
    ∀ (E W : Type v) [Field E] [Finite E] [Algebra (ZMod 2) E] [CharP E 2]
      [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (σ : Representation E L W),
      IsIrreducible σ → Function.Injective σ →
      ∀ t : L, t ≠ 1 → t ^ 2 = 1 →
        10 * (2 * m + 1) ≤ Module.finrank (ZMod 2) E *
          Module.finrank E (W ⧸ invariants (σ.comp (zpowers t).subtype))

end ReeF4
