module

public import Mathlib.Algebra.Lie.Weights.Cartan
public import Theory.AlgebraicGroup.RootSubgroups.TangentLie
public import Theory.AlgebraicGroup.Tori.Character.Regular

/-!
# Maximal-torus tangents and Lie root spaces

For a maximal torus `T` in an algebraic group `K`, this module defines its
canonical toral Lie subalgebra as the range of the differential of the
inclusion `T → K`.  Coordinate comultiplication is cocommutative for a
commutative group, so the tangent Lie algebra of `T`, and hence its image, is
abelian and nilpotent.

A torus character differentiates to a linear functional on this subalgebra.
The final equivalence compares the inverse-character eigenspace of the
identity-tangent conjugation representation with Mathlib's generalized Lie
root space for that differential.  Its hypotheses state the three exact
inputs needed for this comparison: distinct characters have distinct
differentials, the torus weight spaces span the tangent, and differentiating
the conjugation eigenvector equation gives the stated bracket equation.
Differential injectivity cannot be omitted in positive characteristic, where
distinct characters can have the same differential.

The object below is the maximal-torus Cartan candidate used in the GLS3 root
space argument.  This layer proves its toral and nilpotent properties; it does
not assert the self-normalizing property of a Mathlib `IsCartanSubalgebra`,
which requires later reductive-group structure.  No geometric root-subgroup
existence or multiplicity theorem enters the construction.
-/

open scoped TensorProduct
open WithConv

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem coordinateIsCocommOfIsMulCommutative
    (K : Variety k) [AlgebraicGroup K]
    (hK : IsMulCommutative (Variety.Point K)) :
    let _ : Bialgebra k (Variety.PolynomialFunction K) := coordinateBialgebra K
    Coalgebra.IsCocomm k (Variety.PolynomialFunction K) := by
  let _ : Bialgebra k (Variety.PolynomialFunction K) := coordinateBialgebra K
  rw [isMulCommutative_iff] at hK
  constructor
  apply LinearMap.ext
  intro a
  apply polynomialFunctionTensor_injective K K
  apply Variety.PolynomialFunction.ext
  intro z
  let xy := Variety.prodPointEquiv K K z
  generalize hxy : xy = p
  obtain ⟨x, y⟩ := p
  have hz : z = (Variety.prodPointEquiv K K).symm (x, y) := by
    apply (Variety.prodPointEquiv K K).injective
    change xy = (x, y)
    exact hxy
  rw [hz]
  have hswap (t : Variety.PolynomialFunction K ⊗[k]
      Variety.PolynomialFunction K) :
      polynomialFunctionTensor K K
          (TensorProduct.comm k _ _ t)
          ((Variety.prodPointEquiv K K).symm (x, y)) =
        polynomialFunctionTensor K K t
          ((Variety.prodPointEquiv K K).symm (y, x)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht =>
        simpa [map_add, Variety.PolynomialFunction.toFun] using
          congrArg₂ (· + ·) hs ht
    | tmul g h => simp [polynomialFunctionTensor_tmul, mul_comm]
  change polynomialFunctionTensor K K
      (TensorProduct.comm k _ _ (coordinateComultiplication K a)) _ =
    polynomialFunctionTensor K K (coordinateComultiplication K a) _
  rw [hswap, coordinateComultiplication_apply,
    coordinateComultiplication_apply, hK y x]

omit [IsAlgClosed k] in
/-- The canonical tangent Lie algebra of a commutative algebraic group is
abelian. -/
public theorem identityTangent_isLieAbelian_of_isMulCommutative
    (K : Variety k) [AlgebraicGroup K]
    (hK : IsMulCommutative (Variety.Point K)) :
    IsLieAbelian (IdentityPointDerivation K) := by
  let _ : Bialgebra k (Variety.PolynomialFunction K) := coordinateBialgebra K
  let _ : Coalgebra.IsCocomm k (Variety.PolynomialFunction K) :=
    coordinateIsCocommOfIsMulCommutative K hK
  constructor
  intro D E
  apply Derivation.ext
  intro a
  change
    (toConv D.toLinearMap * toConv E.toLinearMap).ofConv a -
      (toConv E.toLinearMap * toConv D.toLinearMap).ofConv a = 0
  rw [mul_comm, sub_self]

/-- The canonical toral Lie subalgebra associated to a closed subgroup.  When
the subgroup is a maximal torus, this is the Cartan candidate used for Lie root
spaces. -/
@[expose]
public noncomputable def maximalTorusCartan
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K) :
    LieSubalgebra k (IdentityPointDerivation K) :=
  (identityTangentMorphismLieHom T.inclusion).range

omit [IsAlgClosed k] in
/-- A maximal torus has abelian tangent image in the ambient tangent Lie
algebra. -/
public theorem maximalTorusCartan_isLieAbelian
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (hT : IsMaximalTorus T) : IsLieAbelian (maximalTorusCartan T) := by
  let hsource : IsLieAbelian (IdentityPointDerivation T.carrierVariety) :=
    identityTangent_isLieAbelian_of_isMulCommutative _
      hT.1.isMulCommutative
  exact (lie_abelian_iff_equiv_lie_abelian
    ((identityTangentMorphismLieHom T.inclusion).equivRangeOfInjective
      (identityTangentMorphismLieHom_inclusion_injective T))).mp hsource

omit [IsAlgClosed k] in
/-- The tangent image of a maximal torus is a nilpotent Lie algebra. -/
public theorem maximalTorusCartan_isNilpotent
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (hT : IsMaximalTorus T) : LieRing.IsNilpotent (maximalTorusCartan T) := by
  let _ : IsLieAbelian (maximalTorusCartan T) :=
    maximalTorusCartan_isLieAbelian T hT
  exact LieModule.trivialIsNilpotent _ _

/-- The differential at the identity of a character of a closed torus. -/
@[expose]
public noncomputable def torusWeightDifferential
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (chi : TorusWeight T) :
    IdentityPointDerivation T.carrierVariety →ₗ[k] k where
  toFun D := D chi.scalarPolynomialFunction
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The differential of a torus character, transported to the torus tangent
image in the ambient Lie algebra. -/
@[expose]
public noncomputable def maximalTorusCartanCharacterDifferential
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (chi : TorusWeight T) : maximalTorusCartan T →ₗ[k] k :=
  (torusWeightDifferential T chi).comp
    ((identityTangentMorphismLieHom T.inclusion).equivRangeOfInjective
      (identityTangentMorphismLieHom_inclusion_injective T)).symm.toLinearEquiv.toLinearMap

omit [IsAlgClosed k] in
/-- The differential of the trivial torus character is zero. -/
public theorem maximalTorusCartanCharacterDifferential_one
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K) :
    maximalTorusCartanCharacterDifferential T 1 = 0 := by
  apply LinearMap.ext
  intro h
  change ((identityTangentMorphismLieHom T.inclusion).equivRangeOfInjective
      (identityTangentMorphismLieHom_inclusion_injective T)).symm h
      (1 : TorusWeight T).scalarPolynomialFunction = 0
  have hone : (1 : TorusWeight T).scalarPolynomialFunction = 1 := by
    apply Variety.PolynomialFunction.ext
    intro x
    rw [TorusCharacter.scalarPolynomialFunction_apply]
    rfl
  rw [hone]
  exact (((identityTangentMorphismLieHom T.inclusion).equivRangeOfInjective
    (identityTangentMorphismLieHom_inclusion_injective T)).symm h).map_one_eq_zero

/-- The exact compatibility equation obtained by differentiating the torus
conjugation action on each identity-tangent weight space. -/
public def IdentityTangentWeightBracketCompatibility
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K) : Prop :=
  ∀ (chi : TorusWeight T) (v : IdentityPointDerivation K),
    v ∈ weightSpace (identityTangentRepresentation K) T chi →
      ∀ h : maximalTorusCartan T,
        ⁅(h : IdentityPointDerivation K), v⁆ =
          maximalTorusCartanCharacterDifferential T chi h • v

omit [IsAlgClosed k] in
/-- Apply the differentiated torus-weight bracket compatibility equation.
This eliminator keeps the proposition's implementation opaque to importers. -/
public theorem identityTangentWeightBracketCompatibility_apply
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (hcompat : IdentityTangentWeightBracketCompatibility T)
    (chi : TorusWeight T) (v : IdentityPointDerivation K)
    (hv : v ∈ weightSpace (identityTangentRepresentation K) T chi)
    (h : maximalTorusCartan T) :
    ⁅(h : IdentityPointDerivation K), v⁆ =
      maximalTorusCartanCharacterDifferential T chi h • v :=
  hcompat chi v hv h

section AbstractRootSpace

variable {F : Type*} [Field F]

private theorem submodule_le_rootSpace
    {L : Type*} [LieRing L] [LieAlgebra F L]
    (H : LieSubalgebra F L) [LieRing.IsNilpotent H]
    (W : Submodule F L) (alpha : H → F)
    (hcompat : ∀ (v : L), v ∈ W → ∀ h : H,
      ⁅(h : L), v⁆ = alpha h • v) :
    W ≤ (LieAlgebra.rootSpace H alpha).toSubmodule := by
  intro v hv
  apply LieModule.weightSpace_le_genWeightSpace L alpha
  rw [LieModule.mem_weightSpace]
  exact hcompat v hv

private theorem weightSpace_eq_rootSpace_of_iSup_eq_top_of_injective
    {L : Type*} [LieRing L] [LieAlgebra F L]
    (H : LieSubalgebra F L) [LieRing.IsNilpotent H]
    {I : Type*} (W : I → Submodule F L) (d : I → H → F)
    (hd : Function.Injective d)
    (hspan : (⨆ i, W i) = ⊤)
    (hle : ∀ i, W i ≤ (LieAlgebra.rootSpace H (d i)).toSubmodule) :
    ∀ i, W i = (LieAlgebra.rootSpace H (d i)).toSubmodule := by
  have hindepLie : iSupIndep (fun i => LieAlgebra.rootSpace H (d i)) :=
    (LieModule.iSupIndep_genWeightSpace F H L).comp hd
  have hindep : iSupIndep
      (fun i => (LieAlgebra.rootSpace H (d i)).toSubmodule) :=
    LieSubmodule.iSupIndep_toSubmodule.mpr hindepLie
  have hfamily : W = fun i =>
      (LieAlgebra.rootSpace H (d i)).toSubmodule :=
    (hindep.le_iff_eq_of_iSup_eq_top hspan).mp hle
  exact congrFun hfamily

end AbstractRootSpace

/-- Under faithful character differentiation, a spanning torus-weight
decomposition, and the differentiated conjugation equation, the inverse
`chi`-weight space of the identity tangent is linearly equivalent to the Lie
root space for the differential of `chi⁻¹`. -/
public noncomputable def inverseWeightSpaceRootSpaceEquiv
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (hT : IsMaximalTorus T)
    (hdiff : Function.Injective
      (maximalTorusCartanCharacterDifferential T))
    (hspan : (⨆ psi : TorusWeight T,
      weightSpace (identityTangentRepresentation K) T psi) = ⊤)
    (hcompat : IdentityTangentWeightBracketCompatibility T)
    (chi : TorusWeight T) :
    let _ : LieRing.IsNilpotent (maximalTorusCartan T) :=
      maximalTorusCartan_isNilpotent T hT
    weightSpace (identityTangentRepresentation K) T chi⁻¹ ≃ₗ[k]
      LieAlgebra.rootSpace (maximalTorusCartan T)
        (maximalTorusCartanCharacterDifferential T chi⁻¹) := by
  letI : LieRing.IsNilpotent (maximalTorusCartan T) :=
    maximalTorusCartan_isNilpotent T hT
  let W : TorusWeight T → Submodule k (IdentityPointDerivation K) :=
    fun psi => weightSpace (identityTangentRepresentation K) T psi
  let d : TorusWeight T → maximalTorusCartan T → k :=
    fun psi h => maximalTorusCartanCharacterDifferential T psi h
  have heq : ∀ psi, W psi =
      (LieAlgebra.rootSpace (maximalTorusCartan T) (d psi)).toSubmodule :=
    weightSpace_eq_rootSpace_of_iSup_eq_top_of_injective
      (maximalTorusCartan T) W d (by
        intro psi phi h
        apply hdiff
        apply LinearMap.ext
        intro x
        exact congrFun h x) hspan
      (fun psi => submodule_le_rootSpace
        (maximalTorusCartan T) (W psi) (d psi)
          (fun v hv h => by
            change ⁅(h : IdentityPointDerivation K), v⁆ =
              maximalTorusCartanCharacterDifferential T psi h • v
            exact hcompat psi v (by simpa [W] using hv) h))
  exact LinearEquiv.ofEq _ _ (heq chi⁻¹)

end Theory.AlgebraicGroup
