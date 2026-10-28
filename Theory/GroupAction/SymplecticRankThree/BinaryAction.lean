module
public import Theory.GroupAction.SymplecticRankThree.BinaryCoordinates
public import Theory.SpecificGroups.PSp4Three.MatrixModel
public import Theory.SpecificGroups.SymplecticFour.Flag

/-!
# Faithful symplectic coordinates for binary polarity designs

A fifteen-point polarity design with three points on every line reconstructs
a four-dimensional vector space over F₂. Its incidence relation is the zero
relation of a nondegenerate alternating form. Every faithful incidence action
therefore embeds in the full symplectic group, with explicit equivariance on
the reconstructed point vectors.

The proof uses the binary row-span reconstruction in `BinaryPolarGeometry`
and the alternating-form isometry from `PSp4Three.MatrixModel`. The matrix
transport follows the conjugation construction in
`SymplecticFour.TransvectionRecognition.TraceModelConjugacy`, using only
the narrow form and matrix interfaces.

Source: Higman, Finite permutation groups of rank 3 (1964), Theorem 2(i),
pp.154–155; this supplies the binary coordinatization step directly.
-/

public noncomputable section
open Theory.LinearAlgebra
open Matrix
open Theory.SpecificGroups.SymplecticFour
namespace Theory.GroupAction.SymplecticRankThree.PolarityDesign
variable {Ω G : Type*} [Finite Ω] [Group G] [MulAction G Ω] [FaithfulSMul G Ω]
variable (D : PolarityDesign Ω 2)
variable (hline : ∀ a b, a ≠ b → (D.line a b).ncard = 3)
variable (hdegree : Nat.card Ω = 15)
variable (hact : ∀ (g : G) a b, D.incident (g • a) (g • b) ↔ D.incident a b)
include hline hdegree hact

/-- A faithful action on the binary design has faithful symplectic coordinates. -/
theorem binary_action_embedding :
    ∃ E : BinaryPolarGeometry.Space D.incident ≃ₗ[ZMod 2] Vector (ZMod 2),
    ∃ j : G →* Sp (ZMod 2), Function.Injective j ∧
      (∀ g x, E (BinaryPolarGeometry.point D.incident (g • x)) =
        j g • E (BinaryPolarGeometry.point D.incident x)) ∧
      (∀ x y, form (ZMod 2) (E (BinaryPolarGeometry.point D.incident x))
        (E (BinaryPolarGeometry.point D.incident y)) = 0 ↔ D.incident x y) := by
  let d := D.binaryPolarData hline hdegree
  let ρ := BinaryPolarGeometry.Data.representation hact
  have hf : Function.Injective ρ := d.representation_injective hact
  have hd := D.binary_space_finrank hline hdegree
  obtain ⟨e⟩ := Matrix.PSp4Three.exists_isometry 2 d.form d.form_alternating d.form_nondegenerate hd
  let σ : Representation (ZMod 2) G (Vector (ZMod 2)) :=
    e.toLinearEquiv.conjRingEquiv.toMonoidHom.comp ρ
  let f := LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp σ
  have hpres (g : G) : f g ∈ Matrix.symplecticGroup (Fin 2) (ZMod 2) := by
    apply Matrix.PSp4Three.mem_iff_preserves.mpr
    intro v w
    change Matrix.PSp4Three.form ((LinearMap.toMatrix' (σ g))*ᵥv)
      ((LinearMap.toMatrix' (σ g))*ᵥw) = _
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    change Matrix.PSp4Three.form (e (ρ g (e.symm v))) (e (ρ g (e.symm w))) = _
    rw [e.map_app, d.form_invariant hact]
    exact (e.map_app (e.symm w) (e.symm v)).symm.trans (by simp)
  let j : G →* Sp (ZMod 2) := f.codRestrict _ hpres
  have hj : Function.Injective j := by
    intro a b hab
    apply hf
    apply e.toLinearEquiv.conjRingEquiv.injective
    apply LinearMap.toMatrixAlgEquiv'.injective
    exact congrArg Subtype.val hab
  have heq (g : G) (v : BinaryPolarGeometry.Space D.incident) :
      e (ρ g v) = j g • e v := by
    change e (ρ g v) = LinearMap.toMatrix' (σ g)*ᵥe v
    rw [LinearMap.toMatrix'_mulVec]
    change e (ρ g v) = e (ρ g (e.symm (e v)))
    exact congrArg (fun z => e (ρ g z)) (e.toLinearEquiv.symm_apply_apply v).symm
  refine ⟨e.toLinearEquiv,j,hj,?_,?_⟩
  · intro g x
    rw [← BinaryPolarGeometry.Data.representation_point hact]
    exact heq g _
  · intro x y
    change Matrix.PSp4Three.form (e (BinaryPolarGeometry.point D.incident x))
      (e (BinaryPolarGeometry.point D.incident y)) = 0 ↔ D.incident x y
    rw [e.map_app]
    exact d.orthogonal_iff x y

end Theory.GroupAction.SymplecticRankThree.PolarityDesign
