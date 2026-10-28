module

public import Theory.AlgebraicGroup.Automorphisms.FiniteKernel
public import Theory.AlgebraicGroup.Automorphisms.Steinberg
public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
public import Theory.AlgebraicGroup.Solvable.Basic

/-!
# Steinberg restriction to the closed derived subgroup

Steinberg's proof of Theorem 10.4 restricts the original endomorphism `sigma`
to the penultimate term of the derived series.  In the first nontrivial step
this is the Zariski closure of the abstract commutator subgroup.  The source
does not require an arbitrary inner twist here; inner twists are compared with
the original endomorphism only later, in Corollary 10.9, after Lang
surjectivity is already proved.

The module therefore exposes the source-faithful untwisted restriction.  The
closed derived subgroup is connected for connected ambient groups, normal, and
solvable when the ambient rational-point group is solvable.  For connected
nontrivial solvable groups it also has strictly smaller dimension: solvability
makes the commutator closure proper, while connectedness and the closed-subgroup
dimension criterion rule out equal dimension.  Any algebraic-group endomorphism
preserves it.  If the ambient endomorphism is Steinberg, then its restriction is
again Steinberg: the restricted kernel and fixed-point subtype both inject into
the corresponding ambient subtypes, and finite-kernel surjectivity on connected
groups gives point-surjectivity of the restricted endomorphism.

This is the contract used by the solvable Lang induction in GLS3, Chapter 2,
Theorem 2.1.1, via Steinberg, Theorem 10.4.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

open scoped commutatorElement

/-- The Zariski closure of the abstract commutator subgroup. -/
public noncomputable def derivedClosure
    (G : Variety k) [AlgebraicGroup G] : ClosedSubgroup G :=
  subgroupZariskiClosure G (_root_.commutator (Variety.Point G))

omit [IsAlgClosed k] in
/-- Every abstract commutator lies in the closed derived subgroup. -/
public theorem commutatorElement_mem_derivedClosure
    {G : Variety k} [AlgebraicGroup G] (x y : Variety.Point G) :
    ⁅x, y⁆ ∈ (derivedClosure G).toSubgroup := by
  rw [derivedClosure]
  exact subset_closure (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top x) (Subgroup.mem_top y))

omit [IsAlgClosed k] in
/-- The closed derived subgroup is normal. -/
public theorem derivedClosure_normal
    (G : Variety k) [AlgebraicGroup G] :
    (derivedClosure G).toSubgroup.Normal := by
  exact subgroupZariskiClosure_isNormal G _ inferInstance

/-- The closed derived subgroup of a connected algebraic group is connected. -/
public theorem derivedClosure_connected
    {G : Variety k} [AlgebraicGroup G] (hG : Variety.IsConnected G) :
    Variety.IsConnected (derivedClosure G).carrierVariety := by
  let D := derivedClosure G
  have hD : _root_.IsConnected (D : Set (Variety.Point G)) :=
    subgroupZariskiClosure_commutator_isConnected hG
  let e := Variety.closedSubvarietyPointHomeomorph D.isZariskiClosed
  let _ : ConnectedSpace {x : Variety.Point G // x ∈ (D : Set (Variety.Point G))} :=
    Subtype.connectedSpace hD
  let _ : ConnectedSpace (Variety.Point D.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

omit [IsAlgClosed k] in
/-- The closed derived subgroup of a solvable algebraic group is solvable on
rational points. -/
public theorem derivedClosure_solvable
    {G : Variety k} [AlgebraicGroup G]
    (hG : Group.IsSolvable (Variety.Point G)) :
    Group.IsSolvable (Variety.Point (derivedClosure G).carrierVariety) := by
  let _ : Group.IsSolvable (Variety.Point G) := hG
  exact Group.isSolvable_of_isSolvable_injective
    (derivedClosure G).inclusion_injective

omit [IsAlgClosed k] in
/-- In a connected nontrivial solvable algebraic group, the closed derived
subgroup has strictly smaller dimension. -/
public theorem derivedClosure_dimension_lt_of_isSolvable
    {G : Variety k} [AlgebraicGroup G]
    (hG : Variety.IsConnected G)
    (hsolvable : Group.IsSolvable (Variety.Point G))
    [Nontrivial (Variety.Point G)] :
    Variety.dimension (derivedClosure G).carrierVariety <
      Variety.dimension G := by
  let D := derivedClosure G
  have hDproper : D ≠ ClosedSubgroup.top := by
    change subgroupZariskiClosure G (_root_.commutator (Variety.Point G)) ≠
      ClosedSubgroup.top
    exact subgroupZariskiClosure_commutator_ne_top_of_isSolvable
      hsolvable inferInstance
  have hdimle : Variety.dimension D.carrierVariety ≤ Variety.dimension G :=
    closedSubvariety_dimension_le G D.isZariskiClosed
  exact lt_of_le_of_ne hdimle (fun heq => hDproper <| by
    apply SetLike.coe_injective
    apply Set.Subset.antisymm (fun _ _ => trivial)
    have hcontains :=
      (closedSubgroup_dimension_eq_iff_contains_identityComponent G D).mp heq
    rw [(identityComponent_eq_univ_iff_isConnected G).mpr hG] at hcontains
    exact hcontains)

omit [IsAlgClosed k] in
/-- Any algebraic-group endomorphism preserves the closed derived subgroup. -/
public theorem derivedClosure_map
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G)
    (x : Variety.Point (derivedClosure G).carrierVariety) :
    sigma.onPoints ((derivedClosure G).inclusion.onPoints x) ∈
      (derivedClosure G).toSubgroup := by
  let D := derivedClosure G
  have hx : D.inclusion.onPoints x ∈
      closure (_root_.commutator (Variety.Point G) : Set (Variety.Point G)) :=
    (D.pointEquiv x).property
  apply map_mem_closure sigma.toVariety.continuous hx
  intro y hy
  have hymap : sigma.onPoints y ∈
      (_root_.commutator (Variety.Point G)).map sigma.onPoints :=
    Subgroup.mem_map_of_mem sigma.onPoints hy
  rw [map_commutator_eq] at hymap
  exact Subgroup.commutator_mono le_top le_top hymap

/-- Restrict an endomorphism to the closed derived subgroup. -/
public noncomputable def derivedRestriction
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G) :
    AlgebraicGroup.Morphism (derivedClosure G).carrierVariety
      (derivedClosure G).carrierVariety :=
  (sigma.comp (derivedClosure G).inclusion).codRestrictClosedSubgroup
    (derivedClosure G) (derivedClosure_map sigma)

omit [IsAlgClosed k] in
/-- Including the derived restriction recovers the ambient endomorphism. -/
public theorem derivedRestriction_inclusion_apply
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G)
    (x : Variety.Point (derivedClosure G).carrierVariety) :
    (derivedClosure G).inclusion.onPoints
        ((derivedRestriction sigma).onPoints x) =
      sigma.onPoints ((derivedClosure G).inclusion.onPoints x) := by
  rw [derivedRestriction]
  exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
    _ _ _ _

/-- The kernel of the derived restriction is finite when the ambient
endomorphism is point-surjective. -/
public theorem derivedRestriction_kernel_finite
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G)
    (hsigma : Function.Surjective sigma.onPoints) :
    Finite (derivedRestriction sigma).kernel := by
  let _ : Finite sigma.kernel :=
    surjectiveEndomorphism_kernel_finite sigma hsigma
  let kernelToSigma : (derivedRestriction sigma).kernel → sigma.kernel :=
    fun x => ⟨(derivedClosure G).inclusion.onPoints x, by
      have hx := x.property
      change (derivedRestriction sigma).onPoints x = 1 at hx
      have hx' := congrArg (derivedClosure G).inclusion.onPoints hx
      rw [derivedRestriction_inclusion_apply] at hx'
      change sigma.onPoints ((derivedClosure G).inclusion.onPoints x) = 1
      simpa using hx'⟩
  exact Finite.of_injective kernelToSigma (by
    intro x y hxy
    apply Subtype.ext
    apply (derivedClosure G).inclusion_injective
    have hxy' := congrArg (fun z : sigma.kernel => (z : Variety.Point G)) hxy
    simpa [kernelToSigma] using hxy')

/-- The derived restriction is point-surjective when the ambient group is
connected and the ambient endomorphism is point-surjective. -/
public theorem derivedRestriction_surjective
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G)
    (hsigma : Function.Surjective sigma.onPoints)
    (hG : Variety.IsConnected G) :
    Function.Surjective (derivedRestriction sigma).onPoints := by
  exact connected_endomorphism_surjective_of_finiteKernel
    (derivedRestriction sigma) (derivedClosure_connected hG)
    (derivedRestriction_kernel_finite sigma hsigma)

omit [IsAlgClosed k] in
/-- Fixed points of the derived restriction inject into the ambient fixed-point
subtype. -/
public theorem derivedRestriction_fixed_finite
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G)
    (hfixed : Finite {x : Variety.Point G | sigma.onPoints x = x}) :
    Finite {x : Variety.Point (derivedClosure G).carrierVariety |
      (derivedRestriction sigma).onPoints x = x} := by
  let fixedToAmbient :
      {x : Variety.Point (derivedClosure G).carrierVariety |
        (derivedRestriction sigma).onPoints x = x} →
      {x : Variety.Point G | sigma.onPoints x = x} :=
    fun x => ⟨(derivedClosure G).inclusion.onPoints x, by
      change sigma.onPoints ((derivedClosure G).inclusion.onPoints x) =
        (derivedClosure G).inclusion.onPoints x
      rw [← derivedRestriction_inclusion_apply]
      exact congrArg (derivedClosure G).inclusion.onPoints x.property⟩
  let _ := hfixed
  exact Finite.of_injective fixedToAmbient (by
    intro x y hxy
    apply Subtype.ext
    apply (derivedClosure G).inclusion_injective
    have hxy' := congrArg
      (fun z : {x : Variety.Point G | sigma.onPoints x = x} =>
        (z : Variety.Point G)) hxy
    simpa [fixedToAmbient] using hxy')

/-- A Steinberg endomorphism restricts to a Steinberg endomorphism of the
closed derived subgroup of a connected algebraic group. -/
public theorem derivedRestriction_steinbergEndomorphism
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G)
    (hsigma : IsAlgebraicSteinbergEndomorphism sigma)
    (hG : Variety.IsConnected G) :
    IsAlgebraicSteinbergEndomorphism (derivedRestriction sigma) :=
  ⟨derivedRestriction_surjective sigma hsigma.1 hG,
    derivedRestriction_fixed_finite sigma hsigma.2⟩

end Theory.AlgebraicGroup
