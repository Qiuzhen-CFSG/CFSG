module

public import Theory.AlgebraicGroup.Tori.CentralMaximalNilpotent.TorusFree.BorelCentralizer.CompleteOrbit
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy
public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer

/-!
# The centralizer of a Borel subgroup is central

For a connected affine algebraic group over an algebraically closed field,
`C_G(B)` lies in `Z(G)`. A complete geometric Borel model and Borel conjugacy
supply a complete transitive action with point stabilizer exactly the given
Borel. An element centralizing that Borel is fixed by this stabilizer for the
regular conjugation action. The diagonal-orbit argument in `CompleteOrbit`
then proves that it is fixed by every group element.

All morphisms used in the completeness argument are actual scheme morphisms.
The model's equivariant equivalence on rational points is used only to identify
the stabilizer and prove transitivity, never to assert regular quotient descent.

Source: Borel, *Linear Algebraic Groups*, §11.4(2), with the complete Borel
space and conjugacy from §11.1 (`refs/KGroup/Bor1/Chapter4.tex`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Theory.AlgebraicGroup.TorusFree

open Variety.Geometric Bor1 BorelGeometricConjugacy

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

private noncomputable def conjugationPairMorphism (G : Variety k) [AlgebraicGroup G] :
    Variety.Morphism (Variety.prod G G) G :=
  (AlgebraicGroup.mulMorphism G).comp
    ((AlgebraicGroup.mulMorphism G).pair
      ((AlgebraicGroup.invMorphism G).comp (Variety.Morphism.fst G G)))

private noncomputable def conjugationAction (G : Variety k) [AlgebraicGroup G] :
    MorphicAction G (ofAffine G) where
  smul g y := (affinePointEquiv G).symm (g * affinePointEquiv G y * g⁻¹)
  one_smul y := by
    change (affinePointEquiv G).symm (1 * affinePointEquiv G y * 1⁻¹) = y
    simp only [one_mul, inv_one, mul_one, Equiv.symm_apply_apply]
  mul_smul g h y := by
    change (affinePointEquiv G).symm ((g * h) * affinePointEquiv G y * (g * h)⁻¹) =
      (affinePointEquiv G).symm (g * affinePointEquiv G
        ((affinePointEquiv G).symm (h * affinePointEquiv G y * h⁻¹)) * g⁻¹)
    rw [Equiv.apply_symm_apply]
    congr 1
    group
  actionMorphism := ofAffineProductMorphism (conjugationPairMorphism G)
  actionMorphism_apply g y := by
    apply (affinePointEquiv G).injective
    rw [affinePointEquiv_ofAffineProductMorphism_prodPoint]
    simp only [Equiv.apply_symm_apply]
    rfl

/-- Borel §11.4(2): in a connected affine algebraic group over an algebraically
closed field, every element centralizing a Borel subgroup is central. -/
public theorem borel_centralizer_le_center
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) :
    B.centralizer.toSubgroup ≤ Subgroup.center (Variety.Point G) := by
  obtain ⟨B₀, hB₀, ⟨M⟩⟩ := exists_borel_completeModel B hB
  obtain ⟨t, ht⟩ := conjugacy hB₀ hB
  let x : Point M.variety := M.pointEquiv.symm (borelHomogeneousSpace.projection B₀ t)
  have htrans (z : Point M.variety) :
      ∃ g : Variety.Point G, M.action.toMulAction.smul g x = z := by
    obtain ⟨s, hs⟩ := borelHomogeneousSpace.projection_surjective B₀ (M.pointEquiv z)
    refine ⟨s * t⁻¹, M.pointEquiv.injective ?_⟩
    rw [M.equivariant]
    change (s * t⁻¹) • (M.pointEquiv (M.pointEquiv.symm
      (borelHomogeneousSpace.projection B₀ t))) = M.pointEquiv z
    rw [Equiv.apply_symm_apply, ← borelHomogeneousSpace.projection_mul,
      inv_mul_cancel_right]
    exact hs
  have hstab (b : Variety.Point G) (hb : M.action.toMulAction.smul b x = x) :
      b ∈ B.toSubgroup := by
    rw [ht]
    apply (projectivization_fixed_iff_mem_conjugate B₀ t b).mp
    have hp := congrArg M.pointEquiv hb
    rw [M.equivariant] at hp
    change b • M.pointEquiv (M.pointEquiv.symm (borelHomogeneousSpace.projection B₀ t)) =
      M.pointEquiv (M.pointEquiv.symm (borelHomogeneousSpace.projection B₀ t)) at hp
    rw [Equiv.apply_symm_apply] at hp
    exact congrArg (fun q : borelHomogeneousSpace B₀ => (q : borelPluckerAmbient B₀)) hp
  intro z hz
  have hfix (b : Variety.Point G) (hb : M.action.toMulAction.smul b x = x) :
      (conjugationAction G).toMulAction.smul b ((affinePointEquiv G).symm z) =
        (affinePointEquiv G).symm z := by
    apply (affinePointEquiv G).injective
    change affinePointEquiv G ((affinePointEquiv G).symm
      (b * affinePointEquiv G ((affinePointEquiv G).symm z) * b⁻¹)) =
        affinePointEquiv G ((affinePointEquiv G).symm z)
    simp only [Equiv.apply_symm_apply]
    have hcomm := (Subgroup.mem_centralizer_iff.mp hz) b (hstab b hb)
    rw [hcomm, mul_inv_cancel_right]
  have hall := M.action.fixed_on_affine_of_complete_transitive
    (conjugationAction G) hG M.complete x htrans ((affinePointEquiv G).symm z) hfix
  apply Subgroup.mem_center_iff.mpr
  intro g
  have heq := congrArg (affinePointEquiv G) (hall g)
  change affinePointEquiv G ((affinePointEquiv G).symm
    (g * affinePointEquiv G ((affinePointEquiv G).symm z) * g⁻¹)) =
      affinePointEquiv G ((affinePointEquiv G).symm z) at heq
  simp only [Equiv.apply_symm_apply] at heq
  exact (mul_inv_eq_iff_eq_mul).mp heq

end Theory.AlgebraicGroup.TorusFree
