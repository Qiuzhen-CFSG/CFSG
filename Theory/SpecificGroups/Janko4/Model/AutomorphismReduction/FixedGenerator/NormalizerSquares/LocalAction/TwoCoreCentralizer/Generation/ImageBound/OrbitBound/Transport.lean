module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound.Geometry

/-!
# Transport from the homology orbit to the coordinate sum graph

A linear coordinate equivalence identifying the actual distinguished orbit
with the listed columns lets every orbit-preserving linear automorphism
permute the graph. The checked spanning theorem makes this action faithful.
Thus the graph automorphism bound transfers to the entire linear stabilizer.
The coordinate identification and the finite graph bound remain separate
premises until the certificate modules discharge them.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation
namespace OrbitGeometry

variable (e : NaturalHomology ≃ₗ[ZMod 2] CoordinateSpace)
  (ho : IsOrbitCoordinates e)

private noncomputable def vertexEquiv : Vertex ≃ distinguishedOrbit :=
  Equiv.ofBijective
    (fun i => ⟨e.symm (vector i), (ho _).mpr (by simp only [e.apply_symm_apply]; exact ⟨i, rfl⟩)⟩)
    ⟨by
      intro i j h
      apply vector_injective
      exact e.symm.injective (congrArg Subtype.val h),
     by
      rintro ⟨v, hv⟩
      obtain ⟨i, hi⟩ := (ho v).mp hv
      refine ⟨i, Subtype.ext ?_⟩
      exact e.injective (by simpa only [e.apply_symm_apply] using hi)⟩

private theorem vertexEquiv_coordinate (i : Vertex) :
    e ((vertexEquiv e ho i).val) = vector i := e.apply_symm_apply _

private theorem vertexEquiv_symm_coordinate (v : distinguishedOrbit) :
    vector ((vertexEquiv e ho).symm v) = e v.val := by
  rw [← vertexEquiv_coordinate e ho, Equiv.apply_symm_apply]

private def orbitPerm (u : orbitLinearStabilizer) : Equiv.Perm distinguishedOrbit where
  toFun v := ⟨(u.val : Module.End (ZMod 2) NaturalHomology) v.val,
    (u.property v.val).mp v.property⟩
  invFun v := ⟨(↑u.val⁻¹ : Module.End (ZMod 2) NaturalHomology) v.val,
    ((u⁻¹).property v.val).mp v.property⟩
  left_inv v := by
    apply Subtype.ext
    change (↑u.val⁻¹ : Module.End (ZMod 2) NaturalHomology)
      ((u.val : Module.End (ZMod 2) NaturalHomology) v.val) = v.val
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  right_inv v := by
    apply Subtype.ext
    change (u.val : Module.End (ZMod 2) NaturalHomology)
      ((↑u.val⁻¹ : Module.End (ZMod 2) NaturalHomology) v.val) = v.val
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]

private noncomputable def vertexPerm (u : orbitLinearStabilizer) : Equiv.Perm Vertex :=
  (vertexEquiv e ho).trans ((orbitPerm u).trans (vertexEquiv e ho).symm)

private def coordinateLinear (u : orbitLinearStabilizer) : Module.End (ZMod 2) CoordinateSpace :=
  e.toLinearMap.comp ((u.val : Module.End (ZMod 2) NaturalHomology).comp e.symm.toLinearMap)

private theorem vertexPerm_vector (u : orbitLinearStabilizer) (i : Vertex) :
    vector (vertexPerm e ho u i) = coordinateLinear e u (vector i) := by
  change vector ((vertexEquiv e ho).symm (orbitPerm u (vertexEquiv e ho i))) = _
  rw [vertexEquiv_symm_coordinate]
  rfl

private theorem coordinateLinear_injective (u : orbitLinearStabilizer) :
    Function.Injective (coordinateLinear e u) := by
  intro x y h
  have he := e.injective h
  change (u.val : Module.End (ZMod 2) NaturalHomology) (e.symm x) =
    (u.val : Module.End (ZMod 2) NaturalHomology) (e.symm y) at he
  have hi := congrArg (fun v => (↑u.val⁻¹ : Module.End (ZMod 2) NaturalHomology) v) he
  simp only [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] at hi
  exact e.symm.injective hi

private theorem vertexPerm_mem (u : orbitLinearStabilizer) :
    vertexPerm e ho u ∈ preservingGroup := by
  intro i j
  rw [adj_iff, adj_iff]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨l, rfl⟩ := (vertexPerm e ho u).surjective k
    refine ⟨l, coordinateLinear_injective e u ?_⟩
    rw [map_add, ← vertexPerm_vector e ho, ← vertexPerm_vector e ho,
      ← vertexPerm_vector e ho]
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨vertexPerm e ho u k, ?_⟩
    rw [vertexPerm_vector, vertexPerm_vector, vertexPerm_vector, hk, map_add]

/-- Every linear stabilizer element induces an automorphism of the full sum graph. -/
noncomputable def toGraphAutomorphism (u : orbitLinearStabilizer) : preservingGroup :=
  ⟨vertexPerm e ho u, vertexPerm_mem e ho u⟩

/-- Spanning makes the action on the sum graph faithful. -/
theorem toGraphAutomorphism_injective : Function.Injective (toGraphAutomorphism e ho) := by
  intro u v h
  have hp : vertexPerm e ho u = vertexPerm e ho v := congrArg Subtype.val h
  have hl : coordinateLinear e u = coordinateLinear e v := by
    apply LinearMap.ext_on_range span_vectors
    intro i
    rw [← vertexPerm_vector e ho, ← vertexPerm_vector e ho, hp]
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro x
  have he := LinearMap.congr_fun hl (e x)
  change e ((u.val : Module.End (ZMod 2) NaturalHomology) (e.symm (e x))) =
    e ((v.val : Module.End (ZMod 2) NaturalHomology) (e.symm (e x))) at he
  simpa only [e.symm_apply_apply] using e.injective he

include e ho in
/-- The graph bound applies to the entire orbit linear stabilizer. -/
theorem orbitLinearStabilizer_card_le_graph :
    Nat.card orbitLinearStabilizer ≤ Nat.card preservingGroup :=
  Nat.card_le_card_of_injective (toGraphAutomorphism e ho) (toGraphAutomorphism_injective e ho)

end OrbitGeometry


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation
