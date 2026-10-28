module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.FixedQuotient
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Odd

/-!+# From cocode actions to the code quotient fixed space

The equivariant duality constructions supply every input to the fixed-quotient
argument, on the same literal fixed line, commutator and constructed six-space.
The native M22 cubic displacement theorem discharges the remaining numerical
premise: every native order-three element moves exactly six code dimensions.
The commuting actor, transvection ranks and intersection calculation are those
proved in `FixedQuotient`; no code conclusion is assumed here.

The remaining inputs are precisely the cocode action witnesses of H.15.2 and
the earlier M24/H.14 restriction and fixed-space facts. Finite dimensionality
of the marked conjugation module follows from its cocode axis equivalence.

Source: Aschbacher--Smith, H.16.4(5), printed p.403, with H.13's native
displacement calculation, combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
namespace MathieuCode.Hexad.ChiefFlag.Actions.CocodeActionData
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The independently proved dual code actions, in the interface consumed by
the cubic argument. Both section representations use the literal fixed line
inside the actual coinvariant kernel. -/
def fixedQuotientActions [FiniteDimensional (ZMod 2) E] (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    FixedQuotientData.Actions E where
  six := D.codeSix
  five_le_six := D.five_le_six
  six_dim := D.codeSix_finrank h h24
  transvections_faithful := D.codeAction_faithful h h24
  transvections_full := D.codeAction_full h h24
  conjugation := D.kernelRepresentation
  kernelMarking := D.kernelMarking
  kernelMarking_equivariant := D.kernelMarking_equivariant
  middleEquiv := D.middleEquiv h h24
  middleEquiv_equivariant := D.middleEquiv_equivariant h h24
  quotientMap := D.quotientMap
  quotientMap_surjective := D.quotientMap_surjective
  quotientMap_ker := D.quotientMap_ker
  coreEquiv := D.quotientCoreEquiv
  coreEquiv_equivariant := D.quotientCoreEquiv_equivariant

/-- The fixed space on V/V1 is exactly the image of the independently defined
commutator V5. The order-three displacement premise is discharged by the
checked native theorem, including its actual point-count calculation. -/
theorem fixedCodeQuotient_eq (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    fixedCodeQuotient = commutatorImage := by
  let : FiniteDimensional (ZMod 2) E := D.axisEquiv.finiteDimensional
  apply fixedCodeQuotient_eq_commutatorImage (D.fixedQuotientActions h h24) h h24
  intro u hu
  exact (m22_cubic_code_displacement (Subgroup.zpowers u)
    ((Nat.card_zpowers u).trans hu)).ge

end MathieuCode.Hexad.ChiefFlag.Actions.CocodeActionData
