module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry
public import Theory.GroupTheory.SimpleSectionSolvableReduction.Model
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers.Dimension
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers.Coordinates

/-!
# Reduction of isotropic stabilizers to two coordinate calculations

Every nonzero totally isotropic subspace of the identity Hermitian four-space
is a line or a plane. Given actual stabilizer equivalences to the hyperbolic
coordinate models, solvability transports in the line case. In the plane case,
the solvable normal subgroup is pulled back along the equivalence, and the
induced quotient equivalence preserves the specified A₆ model.

The assembly theorem is conditional: coordinate transport, point solvability,
and the plane quotient must all be proved before it supplies the isotropic
stabilizer result. It does not assert a parabolic table or identify a group from
its order. Source obligation: the reducible-subgroup case of condition K for
Aschbacher–Smith, Theorem 0.1.2(4), printed pp.4 and 482 of `refs/quasithin.pdf`;
classical unitary conventions in GLS3, chapter 2.
-/

open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers

private def transportSolvableKernelModel
    {G H S : Type*} [Group G] [Group H] [Group S]
    (e : G ≃* H) (m : Group.SolvableKernelModel H S) :
    Group.SolvableKernelModel G S := by
  letI := m.normal
  letI := m.solvable
  let K := m.kernel.comap e.toMonoidHom
  let f : K →* m.kernel :=
    (e.toMonoidHom.comp K.subtype).codRestrict m.kernel (fun x => x.property)
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  refine ⟨K, inferInstance, Group.isSolvable_of_isSolvable_injective (f := f) hf, ?_⟩
  exact (QuotientGroup.congr K m.kernel e
    (Subgroup.map_comap_eq_self_of_surjective e.surjective m.kernel)).trans m.quotientEquiv

/-- Conditional assembly of the point and plane calculations for every isotropic subspace. -/
theorem stabilizer_alternative_of_coordinate_models
    (hpoint : Group.IsSolvable coordinatePointStabilizer)
    (hplane : Nonempty (Group.SolvableKernelModel coordinatePlaneStabilizer
      (alternatingGroup (Fin 6))))
    (hpointTransport : ∀ W : Submodule FiniteField.Nine (Space 4),
      W ≤ orthogonal W → Module.finrank FiniteField.Nine W = 1 →
        Nonempty (projectiveStabilizer W ≃* coordinatePointStabilizer))
    (hplaneTransport : ∀ W : Submodule FiniteField.Nine (Space 4),
      W ≤ orthogonal W → Module.finrank FiniteField.Nine W = 2 →
        Nonempty (projectiveStabilizer W ≃* coordinatePlaneStabilizer))
    (W : Submodule FiniteField.Nine (Space 4)) (hW0 : W ≠ ⊥) (_hWtop : W ≠ ⊤)
    (hW : W ≤ orthogonal W) :
    Group.IsSolvable (projectiveStabilizer W) ∨
      Nonempty (Group.SolvableKernelModel (projectiveStabilizer W)
        (alternatingGroup (Fin 6))) := by
  rcases finrank_one_or_two W hW0 hW with hd | hd
  · obtain ⟨e⟩ := hpointTransport W hW hd
    let := hpoint
    exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · obtain ⟨e⟩ := hplaneTransport W hW hd
    obtain ⟨m⟩ := hplane
    exact Or.inr ⟨transportSolvableKernelModel e m⟩

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers
