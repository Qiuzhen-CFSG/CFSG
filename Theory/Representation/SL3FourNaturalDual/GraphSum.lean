module

public import Theory.Representation.SL3FourNaturalDual.Markings
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Mathlib.LinearAlgebra.Projection

/-!
# Coordinates from a natural summand and its graph translate

An internal direct sum of a natural SL₃(4) summand and its translate by a
linear–graph actor has the concrete natural-plus-dual action. The coordinate
map is constructed by adding the two embeddings. A general GL₃(4) factor in
the graph action is absorbed into the second coordinate; the actor need not
be an involution or a pure inverse transpose. The resulting marking retains
the specified homomorphism from the actual special linear matrix group.

The existence and complementarity of the natural summand are separate inputs.
In the source application they must be obtained from B.4.5 and F.9.18, with
central fixed spaces treated before replacing the hatted module by Ũ_H.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.955 (PDF p.972),
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual
open Matrix

/-- Binary restriction of the actual invertible matrix action. -/
def matrixCoordinates (c : GeneralLinearGroup (Fin 3) F) : W ≃ₗ[ZMod 2] W :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv (GeneralLinearGroup.toLin c)).restrictScalars
    (ZMod 2)

lemma matrixCoordinates_apply (c : GeneralLinearGroup (Fin 3) F) (w : W) :
    matrixCoordinates c w = c.val.mulVec w := rfl

lemma natural_linearConj (c : GeneralLinearGroup (Fin 3) F) (g : SL) (w : W) :
    natural (PSL3.OuterSolvable.linearConjSL F c g) (matrixCoordinates c w) =
      matrixCoordinates c (natural g w) := by
  have h := congrArg Units.val (PSL3.OuterSolvable.linearConjSL_toGL F c g)
  change (PSL3.OuterSolvable.linearConjSL F c g).val = c.val * g.val * (c⁻¹).val at h
  change (PSL3.OuterSolvable.linearConjSL F c g).val.mulVec (c.val.mulVec w) =
    c.val.mulVec (g.val.mulVec w)
  rw [h, Matrix.mulVec_mulVec]
  have hc : (c⁻¹).val * c.val = 1 := congrArg Units.val (inv_mul_cancel c)
  rw [mul_assoc, hc, mul_one, Matrix.mulVec_mulVec]

variable {J U : Type*} [Group J] [AddCommGroup U] [Module (ZMod 2) U]

/-- The action of t identifies a subspace with its actual image. -/
def translateEquiv (ρ : Representation (ZMod 2) J U) (t : J)
    (I : Submodule (ZMod 2) U) : I ≃ₗ[ZMod 2] I.map (ρ t) :=
  Submodule.equivMapOfInjective (ρ t)
    (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t)).injective I

/-- Add the natural embedding and its corrected translate. -/
def graphSumEquiv (ρ : Representation (ZMod 2) J U) (t : J)
    (I : Submodule (ZMod 2) U) (e : I ≃ₗ[ZMod 2] W)
    (c : GeneralLinearGroup (Fin 3) F) (hI : IsCompl I (I.map (ρ t))) : V ≃ₗ[ZMod 2] U :=
  (e.symm.prodCongr (((matrixCoordinates c).trans e.symm).trans (translateEquiv ρ t I))).trans
    (I.prodEquivOfIsCompl (I.map (ρ t)) hI)

lemma graphSumEquiv_apply (ρ : Representation (ZMod 2) J U) (t : J)
    (I : Submodule (ZMod 2) U) (e : I ≃ₗ[ZMod 2] W)
    (c : GeneralLinearGroup (Fin 3) F) (hI : IsCompl I (I.map (ρ t))) (v : V) :
    graphSumEquiv ρ t I e c hI v =
      (e.symm v.1 : U) + ρ t (e.symm (matrixCoordinates c v.2) : U) := rfl

lemma graphSumEquiv_equivariant (ρ : Representation (ZMod 2) J U) (a : SL →* J) (t : J)
    (I : Submodule (ZMod 2) U) (e : I ≃ₗ[ZMod 2] W)
    (c : GeneralLinearGroup (Fin 3) F) (hI : IsCompl I (I.map (ρ t)))
    (he : ∀ g w, ρ (a g) (e.symm w : U) = (e.symm (natural g w) : U))
    (ht : ∀ g, a g * t = t * a (PSL3.OuterSolvable.linearConjSL F c
      (SpecialLinearGroup.inverseTranspose g))) (g : SL) (v : V) :
    ρ (a g) (graphSumEquiv ρ t I e c hI v) =
      graphSumEquiv ρ t I e c hI (representation g v) := by
  rw [graphSumEquiv_apply, map_add, he, graphSumEquiv_apply]
  change (e.symm (natural g v.1) : U) +
    ρ (a g) (ρ t (e.symm (matrixCoordinates c v.2) : U)) =
    (e.symm (natural g v.1) : U) +
      ρ t (e.symm (matrixCoordinates c (dualCoordinates g v.2)) : U)
  congr 1
  have haction : ρ (a g) * ρ t =
      ρ t * ρ (a (PSL3.OuterSolvable.linearConjSL F c
        (SpecialLinearGroup.inverseTranspose g))) := by
    rw [← ρ.map_mul, ← ρ.map_mul, ht]
  change (ρ (a g) * ρ t) (e.symm (matrixCoordinates c v.2) : U) = _
  rw [haction]
  change ρ t (ρ (a (PSL3.OuterSolvable.linearConjSL F c
    (SpecialLinearGroup.inverseTranspose g))) (e.symm (matrixCoordinates c v.2) : U)) = _
  rw [he, natural_linearConj]
  rfl

/-- Construct the full equivariant marking from the two internal summands. -/
def graphSumMarking (ρ : Representation (ZMod 2) J U) (a : SL →* J) (t : J)
    (I : Submodule (ZMod 2) U) (e : I ≃ₗ[ZMod 2] W)
    (c : GeneralLinearGroup (Fin 3) F) (hI : IsCompl I (I.map (ρ t)))
    (he : ∀ g w, ρ (a g) (e.symm w : U) = (e.symm (natural g w) : U))
    (ht : ∀ g, a g * t = t * a (PSL3.OuterSolvable.linearConjSL F c
      (SpecialLinearGroup.inverseTranspose g))) : LinearMarking ρ where
  actor := a
  coordinates := (graphSumEquiv ρ t I e c hI).symm
  equivariant g u := by
    apply (graphSumEquiv ρ t I e c hI).injective
    rw [LinearEquiv.apply_symm_apply,
      ← graphSumEquiv_equivariant ρ a t I e c hI he ht,
      LinearEquiv.apply_symm_apply]

end Representation.SL3FourNaturalDual
