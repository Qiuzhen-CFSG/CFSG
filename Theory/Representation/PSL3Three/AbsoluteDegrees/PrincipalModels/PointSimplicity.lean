module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.PointSimplicity.Basis
public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.PointSimplicity.Density
public import Theory.Representation.JacobsonDensity

/-!
# Absolute simplicity of the PSL₃(3) point augmentation module

The basis `eᵢ + e₁₂` identifies the literal thirteen-point augmentation
representation with the two checked binary actor matrices. A polynomial
rank-one operator and its spanning row and column word orbits prove full
matrix-algebra density. Casting the checked identities proves density over
every characteristic-two field, so the native representation is irreducible
without an algebraic-closure or character-table hypothesis.

This supplies the degree-twelve simplicity input to
`principalModelsExist_of_geometric_irreducibility`. The independent degree-26
input remains with that assembly's other branch. Source application:
Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.2,
manuscript pp.9--10.
-/

public section

open scoped BigOperators Matrix
namespace Representation.PSL3Three.AbsoluteDegrees.PrincipalModels
namespace PointSimplicity

set_option backward.isDefEq.respectTransparency false in
lemma binary_action (a : Fin 2) : A a = fun i j =>
    (if Coordinates.pointImage a j.castSucc = i.castSucc then (1 : ZMod 2) else 0) +
    (if Coordinates.pointImage a 12 = i.castSucc then 1 else 0) := by
  fin_cases a <;> decide +kernel

variable (F : Type*) [Field F] [CharP F 2]
lemma action_matrix (a : Fin 2) :
    LinearMap.toMatrixAlgEquiv (pointBasis F)
      ((pointCore F).toRepresentation (Coordinates.actor a)) = castMatrix F (A a) := by
  ext i j
  rw [action_entry]
  change _ = (ZMod.castHom (dvd_refl 2) F) (A a i j)
  rw [binary_action]
  simp only [map_add]
  split_ifs <;> simp

lemma point_action_dense :
    Algebra.adjoin F (Set.range (pointCore F).toRepresentation) = ⊤ := by
  let Q := Algebra.adjoin F (Set.range (pointCore F).toRepresentation)
  let T := LinearMap.toMatrixAlgEquiv (pointBasis F)
  have hQ : Q.comap T.symm.toAlgHom = ⊤ := by
    apply field_dense F
    intro a
    change T.symm (castMatrix F (A a)) ∈ Q
    rw [← action_matrix, AlgEquiv.symm_apply_apply]
    exact Algebra.subset_adjoin (Set.mem_range_self (Coordinates.actor a))
  apply top_unique
  intro f _
  have h : T f ∈ Q.comap T.symm.toAlgHom := by rw [hQ]; trivial
  change T.symm (T f) ∈ Q at h
  simpa only [AlgEquiv.symm_apply_apply] using h

end PointSimplicity

/-- The native thirteen-point augmentation representation of PSL₃(3) is
irreducible over every characteristic-two field, in arbitrary universes. -/
theorem pointCore_isIrreducible (F : Type*) [Field F] [CharP F 2] :
    Representation.IsIrreducible (pointCore F).toRepresentation := by
  let : Nontrivial (pointCore F).toSubmodule :=
    (PointSimplicity.coordinates F).symm.injective.nontrivial
  exact Representation.irreducible_of_jacobson_density_surjective _
    (PointSimplicity.point_action_dense F)

end Representation.PSL3Three.AbsoluteDegrees.PrincipalModels
