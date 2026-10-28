module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Generators
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Transport
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.ActionIdentification
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations

/-!
# Assembling the two binary vertex filtrations

The coordinate action uses explicit checked permutations and explicit words
in the actual derived group. A coordinate equivalence which intertwines the
two generators intertwines every word. Together with generation of the whole
derived group, it transports the checked coordinate filtrations to the literal
parabolic permutation modules. The imported action and coordinate certificates
discharge those premises for both vertices, giving the filtrations required by
Aschbacher–Smith G.7.2(3), printed p.348 (PDF p.359).
-/

@[expose] public section

namespace G2DerivedPermutationFiltration
open VertexCoordinates

/-- Checking equivariance on the two free generators suffices. -/
theorem vertex_word_equivariance (i : Fin 2) (e : Fin 63 ≃ Vertex i)
    (he : ∀ j x, e (generator i j x) = vertexPerm i (groupGenerator j) (e x))
    (g : WordGroup) (x : Fin 63) :
    e (wordPerm i g x) = vertexPerm i (groupHom g) (e x) := by
  induction g using FreeGroup.induction_on generalizing x with
  | C1 => simp
  | of j => simpa using he j x
  | inv_of j ih =>
    apply (vertexPerm i (groupHom (FreeGroup.of j))).injective
    simp only [map_inv, Equiv.Perm.inv_def]
    rw [← ih, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  | mul a b ha hb =>
    simpa only [map_mul, Equiv.Perm.mul_apply] using (ha (wordPerm i b x)).trans
      (congrArg (vertexPerm i (groupHom a)) (hb x))

/-- Conditional assembly from an actual coordinate identification and a
verified filtration. The generation and coordinate-filtration premises must
both be discharged before obtaining the unconditional vertex theorem. -/
theorem vertex_factorDegreeFiltration_of_coordinates (i : Fin 2)
    (hsurj : Function.Surjective groupHom) (e : Fin 63 ≃ Vertex i)
    (he : ∀ j x, e (generator i j x) = vertexPerm i (groupGenerator j) (e x))
    (h : Representation.FactorDegreeFiltration allowedDegrees (representation i)) :
    Representation.FactorDegreeFiltration allowedDegrees (vertexRepresentation i) := by
  let el : Space ≃ₗ[ZMod 2] BinaryPermutation.Full (Vertex i) :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm
  apply h.transport groupHom hsurj (vertexRepresentation i) el
  intro g v
  ext y
  change v ((wordPerm i g).symm (e.symm y)) =
    v (e.symm ((vertexPerm i (groupHom g)).symm y))
  congr 1
  apply e.injective
  rw [e.apply_symm_apply]
  apply (vertexPerm i (groupHom g)).injective
  rw [Equiv.apply_symm_apply, ← vertex_word_equivariance i e he,
    Equiv.apply_symm_apply, e.apply_symm_apply]

/-- The certified coordinate filtrations are the actual filtrations on both
parabolic coset modules. -/
theorem vertex_factorDegreeFiltration (i : Fin 2) :
    Representation.FactorDegreeFiltration allowedDegrees (vertexRepresentation i) := by
  apply vertex_factorDegreeFiltration_of_coordinates i groupHom_surjective
    (Equiv.ofBijective (vertex i) (vertex_bijective i))
  · intro j x
    exact vertex_generator_action i j x
  · exact VertexCoordinates.coordinate_factorDegreeFiltration i

end G2DerivedPermutationFiltration
