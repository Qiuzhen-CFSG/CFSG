module

public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import Theory.GroupAction.RegularWreathFunctionModule
public import Theory.Representation.FourGroupMatrixCoordinates

/-!
# The natural action input to Section 15.3

The orthogonal alternative of 15.1.3 acts on the direct sum of two definite
binary planes. We express that input by compatible actor and vector maps to
the literal matrix-and-coordinate-permutation action. Surjectivity refers to
the actor map from `M`; its kernel is proved to be exactly `C_M(V)`.

This interface is an earlier-theorem input, to be constructed by 15.1.3's
owner. It contains no normalizer, uniqueness, residual, or Thompson-subgroup
conclusions from 15.3.2–12. In particular an abstract wreath isomorphism
without the compatibility equation does not inhabit it.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.1.3(2)
and the plane decomposition following 15.3.4, printed pp.1086 and 1121–1122.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03

open Subgroup

abbrev OrthogonalPlaneActor := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
abbrev OrthogonalPlaneIndex := Multiplicative (ZMod 2)
abbrev OrthogonalPlaneVector := Multiplicative (Fin 2 → ZMod 2)
abbrev OrthogonalActor := RegularWreathProduct OrthogonalPlaneActor OrthogonalPlaneIndex
abbrev OrthogonalVector := OrthogonalPlaneIndex → OrthogonalPlaneVector

/-- The natural action, with both of its constituent actions fixed explicitly. -/
@[instance_reducible] def orthogonalAction : MulDistribMulAction OrthogonalActor OrthogonalVector :=
  letI := FourGroupMatrixCoordinates.naturalAction
  RegularWreathProduct.functionModule _ _ _

/-- The supported coordinate plane indexed by `i`. -/
def orthogonalCoordinatePlane (i : OrthogonalPlaneIndex) : Subgroup OrthogonalVector where
  carrier v := ∀ j, j ≠ i → v j = 1
  one_mem' := by intro j hj; rfl
  mul_mem' := by intro a b ha hb j hj; change a j * b j = 1; rw [ha j hj, hb j hj, one_mul]
  inv_mem' := by intro a ha j hj; change (a j)⁻¹ = 1; rw [ha j hj, inv_one]

variable {G : Type*} [Group G]

/-- The genuine natural rank-four input, with the exact conjugation action. -/
structure NaturalOrthogonalAction (M V : Subgroup G) where
  normalizes : M ≤ normalizer (V : Set G)
  coordinates : V ≃* OrthogonalVector
  actor : M →* OrthogonalActor
  onto : Function.Surjective actor
  compatible : letI := orthogonalAction
    ∀ (m : M) (v : V),
      coordinates (V.normalizerMonoidHom ⟨m, normalizes m.property⟩ v) =
        actor m • coordinates v

/-- The definite planes in the ambient group, determined by the action coordinates. -/
def NaturalOrthogonalAction.plane {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (i : OrthogonalPlaneIndex) : Subgroup G :=
  ((orthogonalCoordinatePlane i).comap d.coordinates.toMonoidHom).map V.subtype

/-- Compatibility identifies the actor kernel with the actual centralizer in `M`. -/
theorem NaturalOrthogonalAction.ker_actor {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) :
    d.actor.ker = (centralizer (V : Set G)).subgroupOf M := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := FourGroupMatrixCoordinates.naturalAction_faithful
  let _ := orthogonalAction
  let : FaithfulSMul OrthogonalActor OrthogonalVector :=
    RegularWreathProduct.functionModule_faithful _ _ _
  ext m
  constructor
  · intro hm v hv
    have h := d.compatible m ⟨v, hv⟩
    rw [show d.actor m = 1 from hm, one_smul] at h
    have hc := congrArg V.subtype (d.coordinates.injective h)
    change (m : G) * v * (m : G)⁻¹ = v at hc
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  · intro hm
    change d.actor m = 1
    apply FaithfulSMul.eq_of_smul_eq_smul (α := OrthogonalVector)
    intro w
    obtain ⟨v, rfl⟩ := d.coordinates.surjective w
    rw [one_smul, ← d.compatible]
    congr 1
    apply Subtype.ext
    change (m : G) * (v : G) * (m : G)⁻¹ = v
    exact mul_inv_eq_iff_eq_mul.mpr ((hm v v.property).symm)

/-- The vector coordinate map gives the required order sixteen. -/
theorem NaturalOrthogonalAction.card_vector {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) : Nat.card V = 16 := by
  rw [Nat.card_congr d.coordinates.toEquiv]
  norm_num [OrthogonalVector, OrthogonalPlaneIndex, OrthogonalPlaneVector,
    Nat.card_eq_fintype_card]

end CFSG.Quasithin.Chapter15.Section03

end
