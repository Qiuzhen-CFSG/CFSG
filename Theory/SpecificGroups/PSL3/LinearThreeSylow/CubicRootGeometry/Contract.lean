module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupAction.Defs
public import Mathlib.GroupTheory.Sylow

/-!
# Interface for cubic root calculations in PSL₃(F₄)

These are the two intrinsic calculations needed by central-cover lifting:
a normal four-subgroup of a Sylow two-subgroup is its centre, and an outer
cubic linear automorphism fixing this centre has exactly that fixed subgroup
and full commutator subgroup on the Sylow group. All maps are literal matrix
automorphisms; the Sylow subgroup may be any conjugate.

This record specifies an output to prove, not an assumed property of a
projective marking. Its producer is the CubicRootGeometry extension; the
source application is Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F]

/-- Intrinsic outputs, to be constructed for fields of order four. -/
structure FourSylowRootCalculations : Prop where
  normal_four : ∀ (P : Sylow 2 PSL(3,F)) (W : Subgroup PSL(3,F)),
    W ≤ P → (P : Subgroup PSL(3,F)) ≤ normalizer (W : Set PSL(3,F)) →
    Nat.card W = 4 → W = (center P).map (P : Subgroup PSL(3,F)).subtype
  cubic : ∀ (P : Sylow 2 PSL(3,F)) (a : Matrix.GeneralLinearGroup (Fin 3) F),
    let δ := Matrix.PSL3.OuterSolvable.linearConj F a
    let Z := (center P).map (P : Subgroup PSL(3,F)).subtype
    δ ∉ MulAut.innerSubgroup PSL(3,F) → δ ^ 3 = 1 →
    (P : Subgroup PSL(3,F)).map δ.toMonoidHom = P →
    Z ≤ δ.fixedSubgroup →
    (P : Subgroup PSL(3,F)) ⊓ δ.fixedSubgroup = Z ∧
      commutatorSubgroup (zpowers δ) PSL(3,F) (P : Subgroup PSL(3,F)) = P

end Matrix.PSL3.LinearThree
