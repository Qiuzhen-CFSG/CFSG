module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.Descent
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.Coordinates

/-!
# Structural prerequisites for the outer adjoint estimate

Two independent statements remain after actual adjoint descent. The first
identifies each Schur-linear involution with matrix conjugation or conjugation
after transpose. The second simultaneously normalizes an elementary actor
with these operator forms, using the graph centralizer and its root groups.
The latter can be proved with the former as an explicit hypothesis.

Neither statement is asserted here. In particular an abstract automorphism
factorization alone does not establish the operator identities below.
Their source assembly is `Outer.adjoint_estimate_of_forms`; it must discharge
both statements before giving the unconditional adjoint estimate.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8,
step 3A, author manuscript p.27; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint
variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- An actual inner-diagonal or graph operator on the adjoint space. This is
an equality of operators through the specified representation equivalence. -/
def HasStandardAction (e : σ.Equiv (binaryRep B)) (t : linearNormalizer σ) : Prop :=
  ∃ g : GL (Fin 3) B.Carrier,
    (∀ v : V, LinearMap.toMatrix' (e (t.val.val v)).val =
      g.val * LinearMap.toMatrix' (e v).val * (g⁻¹).val) ∨
    (∀ v : V, LinearMap.toMatrix' (e (t.val.val v)).val =
      g.val * (LinearMap.toMatrix' (e v).val).transpose * (g⁻¹).val)

/-- The missing operator coverage, only for involutions linear over the
component Schur field. Field and scalar contributions must be eliminated. -/
def InvolutionForms : Prop :=
  ∀ (e : σ.Equiv (binaryRep B)) (t : linearNormalizer σ),
    t ^ 2 = 1 → SchurNormalizer.IsSchurLinear σ t → HasStandardAction B σ e t

/-- The independent graph-centralizer reduction, taking actual matrix forms
as an explicit premise. It must supply the single common coordinate change
and the injective group parameterization used by `GraphForm.estimate`. -/
def GraphForms : Prop :=
  ∀ (e : σ.Equiv (binaryRep B)) (A : Subgroup (linearNormalizer σ)),
    IsElementaryTwo A → ¬ A.map (linearNormalizer σ).subtype ≤ actionImage σ →
    (∀ t ∈ A, HasStandardAction B σ e t) →
    Nonempty (GraphForm B (normalizerRepresentation σ) A)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint
