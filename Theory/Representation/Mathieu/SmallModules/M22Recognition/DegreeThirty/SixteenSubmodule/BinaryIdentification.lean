module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.Absolute
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.BinaryIdentification.AdjointBaseChange
public import Theory.Representation.SL3.BinaryFieldDescent
public import Theory.Representation.SL3.BinaryFieldDescent.Fields

/-!
# Binary identification of the sixteen-dimensional adjoint constituent

The exact Schur-orbit theorem gives quadratic Schur field and one adjoint
factor. Removing the trivial tensor factors retains the coefficient embedding
of the surviving factor, including its possible Frobenius twist. Identify
the actual Schur field with F₄ compatibly with that embedding, compare the
scalar extension of the concrete adjoint action, and descend the resulting
intertwining equivalence. Restriction of scalars then recovers the original
binary action on its original carrier.

The final theorem uses the literal point-stabilizer map to supply the local
identification needed by the independent induced-module filtration argument.
No absolute irreducibility over F₂ is assumed.

Source: GLS III, 2.8.6, Remark 2.8.8 and 2.8.10(c), feeding the M22 degree gap
in Guralnick–Malle I, Proposition 5.1, pp.15–16.
-/

open scoped MonoidAlgebra TensorProduct
open Representation Sporadic.Mathieu
open Representation.SL3.BinaryDefiningFactors
open Representation.BinaryFieldDescent
public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule

private theorem single_adjoint_word {K : Type*} [Field K] [CharP K 2]
    (ι : Matrix.PSL3Four.F →+* K) (w : List Factor)
    (hw : w = [.adjoint, .trivial] ∨ w = [.trivial, .adjoint]) :
    ∃ ι' : Matrix.PSL3Four.F →+* K,
      Nonempty ((wordRep ι w).Equiv (factorRep ι' .adjoint)) := by
  rcases hw with rfl | rfl
  · refine ⟨ι, ⟨?_⟩⟩
    exact (BinaryFieldDescent.tensorEquiv (.refl (factorRep ι .adjoint))
      (Representation.TensorProduct.rid K (Representation.trivial K Matrix.PSL3Four.SL K))).trans
        (Representation.TensorProduct.rid K (factorRep ι .adjoint))
  · refine ⟨(frobenius K 2).comp ι, ⟨?_⟩⟩
    exact (Representation.TensorProduct.lid K _).trans (Representation.TensorProduct.rid K _)

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  (τ : Representation (ZMod 2) Matrix.PSL3Four.SL W) [τ.IsIrreducible]

/-- Every irreducible binary SL₃(4)-representation of degree sixteen is the
restriction of the actual trace-zero conjugation action over F₄. -/
theorem equiv_adjointBinary (hd : Module.finrank (ZMod 2) W = 16) :
    Nonempty (τ.Equiv adjointBinary) := by
  obtain ⟨hs, ι, w, hw, ⟨ea⟩⟩ := absolute_adjoint_orbit τ hd
  obtain ⟨ι', ⟨ew⟩⟩ := single_adjoint_word ι w hw
  let : Algebra Matrix.PSL3Four.F (SplittingField τ) := ι'.toAlgebra
  have hcard : Nat.card Matrix.PSL3Four.F = Nat.card (EndField τ) := by
    let : Module.Finite (ZMod 2) (EndField τ) := Module.Finite.of_finite
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := EndField τ)
    change Nat.card (EndField τ) = Nat.card (ZMod 2) ^ Representation.schurDegree 2 τ at he
    rw [he, hs, Nat.card_zmod, Matrix.PSL3Four.card_F]
    decide
  obtain ⟨e, he⟩ := FiniteField.exists_compatible_equiv_of_card_eq
    (algebraMap (EndField τ) (SplittingField τ)) ι' hcard
  let := scalarModule τ e
  let : Finite W := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) W)
  let : Module.Finite Matrix.PSL3Four.F W := Module.Finite.of_finite
  let eS := scalarExtensionEquiv τ e he
  let eA := adjointBaseChange
    (F := Matrix.PSL3Four.F) (K := SplittingField τ)
  obtain ⟨ed⟩ := equiv_of_extendScalars (K := SplittingField τ) (scalarRep τ e)
    (factorRep (RingHom.id Matrix.PSL3Four.F) .adjoint)
    ⟨eS.symm.trans (ea.trans (ew.trans eA.symm))⟩
  simpa only [restrict_scalarRep, adjointBinary] using
    Nonempty.intro (restrictBinaryEquiv (W := Adjoint) ed)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Identify a sixteen-dimensional irreducible point submodule after inflation
through the central quotient and the literal `m22PointStabilizerEquiv 0`.
This supplies the equivalence premise of `impossible_of_equiv_of_filtration`. -/
theorem point_submodule_equiv_adjointBinary (σ : Representation (ZMod 2) M22 V)
    (S : Subrepresentation (pointRestriction σ)) [S.toRepresentation.IsIrreducible]
    (hd : Module.finrank (ZMod 2) S.toSubmodule = 16) :
    Nonempty (Representation.Equiv (S.toRepresentation.comp pointSL) adjointBinary) := by
  let : IsIrreducible (S.toRepresentation.comp pointSL) :=
    (irreducible_comp_surjective_iff pointSL pointSL_surjective S.toRepresentation).mpr
      inferInstance
  exact equiv_adjointBinary _ hd

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule
