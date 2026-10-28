module
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.TraceCompleteness
public import Theory.Representation.JankoTwo.SixDimensionalCertificate.ScalarDescent
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Algebra.Tower

/-!
# Recognizing the actual binary twelve-dimensional Hall--Janko actions

A simple constituent of the scalar extension of the original binary action
is faithful by coefficient projection and irreducibility. The complete native
spectrum and its degree lower bound force that constituent to have degree six.
The checked degree-six comparison then descends to the actual marked natural
G2(4) action. Its proved involutory-extension equivalence handles the full
permutation extension, with its specified coefficient Frobenius.

Only simplicity inherited from the original central quotient is retained.
Source: Aschbacher--Smith K.4.5, printed p.460, and GM02 Proposition 5.1.
-/

public noncomputable section
open scoped TensorProduct
open Representation
namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding
universe u


set_option backward.isDefEq.respectTransparency false in
/-- Recognition preserves the actual binary action and the constructed carrier embedding. -/
theorem binary_equiv_marked_of_finrank_twelve [IsSimpleGroup Carrier]
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) Carrier W) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) W = 12) :
    Nonempty (RepEquiv σ markedEmbedding.innerRepresentation) := by
  let E := AlgebraicClosure (ULift.{u} F)
  let τ := extendScalars E σ
  have hdim : Module.finrank E (E ⊗[ZMod 2] W) = 12 := by
    simpa only [Module.finrank_baseChange] using hd
  let : Nontrivial (E ⊗[ZMod 2] W) := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank E (E ⊗[ZMod 2] W))
  obtain ⟨S, hiS⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional τ
  let := hiS
  let : Nontrivial S.toSubmodule := Subrepresentation.irreducible_module_nontrivial S.toRepresentation
  let j : S.toRepresentation.IntertwiningMap τ :=
    ⟨S.toSubmodule.subtype, fun _ => by ext v; rfl⟩
  let jB := j.toLinearMap.restrictScalars (ZMod 2)
  have hjB : jB ≠ 0 := by
    intro hz
    obtain ⟨v,hv⟩ := exists_ne (0 : S.toSubmodule)
    exact hv (Subtype.ext (LinearMap.congr_fun hz v))
  have hfB := ScalarConstituents.faithful_of_nonzero_scalar_map σ hf
    (restrictScalars (k := ZMod 2) S.toRepresentation) jB hjB
    (fun g v => by rfl)
  have hfS : Function.Injective S.toRepresentation := by
    intro a b hab
    apply hfB
    ext v
    exact congrArg Subtype.val (LinearMap.congr_fun hab v)
  have hdS : Module.finrank E S.toSubmodule ≤ 12 :=
    (Submodule.finrank_le S.toSubmodule).trans_eq hdim
  have hs := Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.closedSmallDegreeSpectrum
    E S.toSubmodule S.toRepresentation (by omega)
  have hl := Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.five_le_finrank_of_faithful (K := E) (U := S.toSubmodule)
    S.toRepresentation hfS
  have h6 : Module.finrank E S.toSubmodule = 6 := by omega
  exact binary_equiv_marked_of_faithful_six_constituent (E := E) (U := S.toSubmodule) σ S.toRepresentation hfS h6 j
    Subtype.val_injective


/-- The full extension is identified with its literal semilinear natural action. -/
theorem outer_equiv_marked_of_finrank_twelve [IsSimpleGroup Carrier]
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) ExceptionalParabolics.Extension W)
    [IsIrreducible (σ.comp ExceptionalParabolics.intoExtension)]
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) W = 12) :
    Nonempty (RepEquiv σ markedEmbedding.outerRepresentation) := by
  obtain ⟨e⟩ := binary_equiv_marked_of_finrank_twelve
    (σ.comp ExceptionalParabolics.intoExtension)
    (hf.comp ExceptionalParabolics.SecondParabolic.intoExtension_injective) hd
  let : IsIrreducible markedEmbedding.innerRepresentation := markedEmbedding_innerRepresentation_irreducible
  exact markedEmbedding.exists_outer_equivalence σ e

end Sporadic.LeechRelated.J2.G2FourModule.Embedding
