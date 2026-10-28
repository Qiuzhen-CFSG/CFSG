module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.Forms
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.RootPlacement

/-!
# Graph-centralizer normalization for the SL₃ adjoint action

The actual outer-image hypothesis selects a graph actor. Its involution equation
forces a symmetric matrix, and finite binary ternary congruence puts that actor
in the literal Gram-transpose coordinates. Inner-diagonal involutions have actual
determinant-one involutory representatives, so no diagonal ambiguity is hidden
in this selection. These results include the two smallest binary fields.

Commuting involutory lifts in the graph centralizer preserve its Gram matrix.
An explicit isometry places all these lifts in one upper root group. The proved
`GraphCentralizer.root_placement` and coordinate parameterization therefore
supply the exact published `GraphForms` contract: one common coordinate change,
an injective parameter homomorphism, and an actor with parameter `(0,1)`.

`graph_forms` discharges the graph-normalization input of
`Outer.adjoint_estimate_of_forms`. Actual operator coverage is the explicit
`HasStandardAction` input of `GraphForms` and remains with that source assembly's
independent producer; no further normal-form premise is needed here.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8,
step 3A, author manuscript p.27; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

@[expose] public noncomputable section
open Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint
variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V)

/-- Actual standard adjoint operators on an elementary outer actor admit one
common graph/root coordinate form, including binary degrees one and two. -/
theorem graph_forms : GraphForms B σ :=
  GraphCentralizer.graph_forms_of_rootPlacement B σ (GraphCentralizer.root_placement B σ)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint
