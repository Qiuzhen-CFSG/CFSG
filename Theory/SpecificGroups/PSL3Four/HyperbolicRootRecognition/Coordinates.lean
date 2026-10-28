module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.Reflections
public import Theory.GroupTheory.PGroup.HyperbolicFactors

/-!
# Coordinates retaining the original hyperbolic factors and generators

This intermediate witness records an actual multiplicative normal form, with
both central and noncentral generators and both original factor memberships.
Its construction is provided by IntrinsicCoordinates. The reflection reduction
then uses these literal coordinates on the original quotient actions.
Source: Aschbacher, *Sporadic Groups* (1994), proof of 45.3, pp.242–243.
-/

@[expose] public section
namespace Theory.GroupTheory.HyperbolicRecognition

structure MarkedCoordinates {K : Type*} [Group K] (F : HyperbolicFactors K)
    (P : HyperbolicFrame F.A F.z) (Q : HyperbolicFrame F.B F.u) where
  matrix : Cross
  equiv : K ≃* Word matrix
  map_z : equiv (F.z : K) = centralWord matrix cz
  map_u : equiv (F.u : K) = centralWord matrix cu
  map_a : equiv P.a = lift matrix va
  map_b : equiv P.b = lift matrix vb
  map_c : equiv Q.a = lift matrix vc
  map_d : equiv Q.b = lift matrix vd
  first_mem : ∀ x : K, x ∈ F.A ↔ (equiv x).vector.2 = 0
  second_mem : ∀ x : K, x ∈ F.B ↔ (equiv x).vector.1 = 0

end Theory.GroupTheory.HyperbolicRecognition
