module

public import Theory.AlgebraicGroup.Bor1.CompleteNormalOrbitGeometry
public import Theory.AlgebraicGroup.Variety.SmoothIrreducibleNormal

/-!
# A complete closed orbit with normal stabilizer is a point

A closed orbit of a connected affine algebraic group in a complete variety is
a point whenever its point stabilizer is normal in the acting group. The orbit
is irreducible and smooth, so its local rings are integrally closed domains.
The affine stabilizer quotient is irreducible and maps bijectively to the orbit.
The normalization theorem of Borel §10.1(4) transfers completeness to the
quotient, and §10.1(2) makes its identity morphism constant.

Source: Borel, *Linear Algebraic Groups*, §10.4
(refs/KGroup/Bor1/Chapter3.tex, lines 851–859).
-/

open AlgebraicGeometry
open Theory.AlgebraicGroup

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup.Variety.Geometric.MorphicAction

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup H]
variable {X : Geometric k} (A : MorphicAction H X)

/-- The complete normal closed-orbit argument, with stalk normality explicit. -/
public theorem fixed_of_isClosed_orbit_of_normal_stabilizer_of_isNormal
    (hH : Variety.IsConnected H) (hX : IsComplete X) (x : Point X)
    (hclosed : IsClosed (Set.range (A.orbitMorphismAt x).hom))
    (hN : (A.pointStabilizer x).toSubgroup.Normal)
    (hnormal : IsNormal (A.orbitSubvariety x).toGeometric) :
    ∀ h : Variety.Point H, A.toMulAction.smul h x = x := by
  obtain ⟨D, v, hirr, hbij, hv⟩ :=
    A.exists_bijective_quotient_to_closed_orbit hH x hclosed hN
  have hcomplete := isComplete_of_bijective_morphism_to_normal_complete
    v hirr hnormal hbij (A.orbitSubvariety_isComplete hX x hclosed)
  have hconn : IsConnected (ofAffine D.quotient) := by
    letI : IrreducibleSpace (ofAffine D.quotient).toScheme := hirr
    change ConnectedSpace (ofAffine D.quotient).toScheme
    infer_instance
  have hconstant := morphism_to_affine_constant_of_isConnected_isComplete
    (Morphism.id (ofAffine D.quotient)) hconn hcomplete
  letI : MulAction (Variety.Point H) (Point X) := A.toMulAction
  intro h
  have heq : (affinePointEquiv D.quotient).symm (D.projectionToVariety.toFun h) =
      (affinePointEquiv D.quotient).symm (D.projectionToVariety.toFun 1) := by
    apply (affinePointEquiv D.quotient).injective
    simpa only [Morphism.id_apply_point] using hconstant
      ((affinePointEquiv D.quotient).symm (D.projectionToVariety.toFun h))
      ((affinePointEquiv D.quotient).symm (D.projectionToVariety.toFun 1))
  have hev := congrArg (fun q : Point (ofAffine D.quotient) =>
    (A.orbitSubvariety x).inclusion (v q)) heq
  rw [hv h, hv 1] at hev
  have hone : A.toMulAction.smul (1 : Variety.Point H) x = x := by
    change (1 : Variety.Point H) • x = x
    exact one_smul _ _
  exact hev.trans hone

/-- A closed orbit in a complete variety with normal stabilizer in the connected
acting group is a point: the geometric endpoint of Borel §10.4. -/
public theorem fixed_of_isClosed_orbit_of_normal_stabilizer
    (hH : Variety.IsConnected H) (hX : IsComplete X) (x : Point X)
    (hclosed : IsClosed (Set.range (A.orbitMorphismAt x).hom))
    (hN : (A.pointStabilizer x).toSubgroup.Normal) :
    ∀ h : Variety.Point H, A.toMulAction.smul h x = x := by
  apply A.fixed_of_isClosed_orbit_of_normal_stabilizer_of_isNormal hH hX x hclosed hN
  exact isNormal_of_isIrreducible_of_smooth (A.orbitSubvariety x).toGeometric
    (A.orbitSubvariety_isIrreducible_of_isClosed hH x hclosed)
    (A.orbitSubvariety_smooth x)

end Theory.AlgebraicGroup.Variety.Geometric.MorphicAction
