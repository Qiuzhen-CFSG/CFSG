module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.Restriction
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.RepresentationTheory.Induced

/-!
# The native point map and the binary adjoint induction

The point map is SL(3,4) → PSL(3,4) ≃ M22₀ → M22, with the actual
stabilizer comparison. The local model is conjugation on trace-zero
endomorphisms of F₄³, restricted to F₂. Induction along this map keeps the
central quotient and the native M22 marking explicit.

These are concrete models for the sixteen-dimensional branch in the degree
gap underlying Guralnick–Malle I, Proposition 5.1, pp.15–16. Their definition
does not assert that the induced module has no small simple quotient.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule

/-- The literal central quotient followed by the inverse point comparison. -/
def pointSL : Matrix.PSL3Four.SL →*
    MulAction.stabilizer M22 (0 : Fin 22) :=
  (MathieuCode.m22PointStabilizerEquiv 0).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center Matrix.PSL3Four.SL))

theorem pointSL_surjective : Function.Surjective pointSL :=
  (MathieuCode.m22PointStabilizerEquiv 0).symm.surjective.comp
    (QuotientGroup.mk'_surjective _)

/-- The actual inclusion into M22, after the central quotient. -/
def pointSLMap : Matrix.PSL3Four.SL →* M22 :=
  (MulAction.stabilizer M22 (0 : Fin 22)).subtype.comp pointSL

instance fieldBinaryAlgebra : Algebra (ZMod 2) Matrix.PSL3Four.F := ZMod.algebra _ 2

/-- Trace-zero endomorphisms of the actual three-space over F₄. -/
abbrev Adjoint : Type := SL3.BinaryDefiningFactors.AdjointSpace Matrix.PSL3Four.F

/-- Binary restriction of the actual eight-dimensional adjoint action. -/
def adjointBinary : Representation (ZMod 2) Matrix.PSL3Four.SL Adjoint :=
  restrictScalars (k := ZMod 2)
    (SL3.BinaryDefiningFactors.factorRep (RingHom.id Matrix.PSL3Four.F) .adjoint)

/-- The local adjoint model has binary dimension sixteen. -/
theorem finrank_adjoint : Module.finrank (ZMod 2) Adjoint = 16 := by
  let : Module.Free Matrix.PSL3Four.F Adjoint :=
    Module.Free.of_divisionRing Matrix.PSL3Four.F Adjoint
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Matrix.PSL3Four.F)
  rw [Matrix.PSL3Four.card_F, Nat.card_zmod] at hcard
  have hfield : Module.finrank (ZMod 2) Matrix.PSL3Four.F = 2 :=
    (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hcard).symm
  rw [← Module.finrank_mul_finrank (ZMod 2) Matrix.PSL3Four.F Adjoint,
    hfield, SL3.BinaryDefiningFactors.finrank_adjointSpace]

/-- Induction through the native point stabilizer, retaining the central kernel. -/
abbrev InducedAdjoint := IndV pointSLMap adjointBinary

/-- The native M22 action on the induced adjoint module. -/
def inducedAdjoint : Representation (ZMod 2) M22 InducedAdjoint :=
  Representation.ind pointSLMap adjointBinary

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule
