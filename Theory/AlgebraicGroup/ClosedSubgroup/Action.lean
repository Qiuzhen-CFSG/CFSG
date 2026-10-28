module

public import Theory.AlgebraicGroup.Action
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Isomorphism

universe u

/-! The right action of a closed subgroup on its ambient algebraic group. -/

namespace Theory.AlgebraicGroup

section
variable {k : Type u} [Field k]

@[expose]
public noncomputable def ClosedSubgroup.rightActionMorphism
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Variety.Morphism (Variety.prod G H.carrierVariety) G := by
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  letI : AlgebraicGroup (Variety.prod G H.carrierVariety) :=
    AlgebraicGroup.prod G H.carrierVariety
  exact (AlgebraicGroup.mulMorphism G).comp
    ((AlgebraicGroup.Morphism.fst G H.carrierVariety).toVariety.pair
      (H.inclusion.toVariety.comp
        (AlgebraicGroup.Morphism.snd G H.carrierVariety).toVariety))

/-! Pointwise evaluation of the right action by a closed subgroup. -/

section
variable {k : Type u} [Field k]

public lemma ClosedSubgroup.rightActionMorphism_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) (h : Variety.Point H.carrierVariety) :
    H.rightActionMorphism.toFun
      ((Variety.prodPointEquiv G H.carrierVariety).symm (g, h)) =
      g * H.inclusion.onPoints h := by
  apply Variety.Point.ext
  funext i
  rfl

end
end

/-! The coordinate coaction induced by right multiplication by a closed subgroup. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

@[expose]
public noncomputable def ClosedSubgroup.coordinateCoaction
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Variety.PolynomialFunction G →ₐ[k]
      Variety.PolynomialFunction G ⊗[k]
        Variety.PolynomialFunction H.carrierVariety :=
  (polynomialFunction_prod_algEquiv G H.carrierVariety).symm.toAlgHom.comp
    H.rightActionMorphism.pullbackAlgHom

end

/-! Pointwise evaluation of the coordinate coaction. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k]

public lemma ClosedSubgroup.coordinateCoaction_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (f : Variety.PolynomialFunction G) (g : Variety.Point G)
    (h : Variety.Point H.carrierVariety) :
    polynomialFunctionTensor G H.carrierVariety (H.coordinateCoaction f)
      ((Variety.prodPointEquiv G H.carrierVariety).symm (g, h)) =
      f (g * H.inclusion.onPoints h) := by
  let e := polynomialFunction_prod_algEquiv G H.carrierVariety
  let z := (Variety.prodPointEquiv G H.carrierVariety).symm (g, h)
  change (e (e.symm (H.rightActionMorphism.pullbackAlgHom f))) z = _
  rw [e.apply_symm_apply]
  change f (H.rightActionMorphism.toFun z) = _
  rw [H.rightActionMorphism_apply]

end

variable {k : Type u} [Field k]

/-- Proposition 1.1.2(a): a Zariski-closed ordinary subgroup inherits an
algebraic-group structure, its inclusion is a morphism with the prescribed
range, and its polynomial functions are ambient restrictions. -/
public noncomputable def Action.baseClosedSubgroup
    {X : Type u} {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) :
    @ClosedSubgroup k _ A.semidirectVariety A.semidirectAlgebraicGroup := by
  letI : AlgebraicGroup A.semidirectVariety := A.semidirectAlgebraicGroup
  exact ClosedSubgroup.ofSubgroup A.rightMorphism.kernel
    A.rightMorphism.kernel_isZariskiClosed

/-- The canonical base copy is an ordinary normal subgroup. -/
public lemma Action.baseClosedSubgroup_isNormal
    {X : Type u} {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) :
    @Subgroup.Normal (Variety.Point A.semidirectVariety)
      A.semidirectAlgebraicGroup.toGroup
      (@Theory.AlgebraicGroup.Morphism.kernel k _ A.semidirectVariety
        (finiteGroupVariety k X) A.semidirectAlgebraicGroup
        (Theory.AlgebraicGroup.finiteGroup X) A.rightMorphism) := by
  let : AlgebraicGroup A.semidirectVariety := A.semidirectAlgebraicGroup
  change A.rightMorphism.onPoints.ker.Normal
  exact MonoidHom.normal_ker _

/-- The canonical morphism from the base group onto the closed kernel copy. -/
@[expose]
public noncomputable def Action.baseCarrierHom
    {X : Type u} {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) :
    @Theory.AlgebraicGroup.Morphism k _ G
      (@ClosedSubgroup.carrierVariety k _ A.semidirectVariety
        A.semidirectAlgebraicGroup A.baseClosedSubgroup)
      (inferInstance : AlgebraicGroup G)
      (@ClosedSubgroup.carrierAlgebraicGroup k _
        A.semidirectVariety A.semidirectAlgebraicGroup
        A.baseClosedSubgroup) := by
  letI : AlgebraicGroup A.semidirectVariety := A.semidirectAlgebraicGroup
  let H := A.baseClosedSubgroup
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let subgroupHom : Variety.Point G →* H.toSubgroup :=
    { toFun := fun g ↦ ⟨A.baseMorphism.onPoints g, by
        change A.rightMorphism.onPoints (A.baseMorphism.onPoints g) = 1
        simp [Theory.AlgebraicGroup.Action.rightMorphism,
          Theory.AlgebraicGroup.Action.baseMorphism,
          Theory.AlgebraicGroup.Morphism.onPoints]
        change finiteGroupPoint (k := k) X 1 = 1
        exact finiteGroupPoint_one X⟩
      map_one' := by
        apply Subtype.ext
        exact A.baseMorphism.map_one
      map_mul' := by
        intro g h
        apply Subtype.ext
        exact A.baseMorphism.map_mul g h }
  let pointHom : Variety.Point G →* Variety.Point H.carrierVariety :=
    (Equiv.mulEquiv H.pointEquiv).symm.toMonoidHom.comp subgroupHom
  exact
    { toVariety :=
        { toFun := pointHom
          regular := by
            intro i
            rcases A.baseMorphism.toVariety.regular i with ⟨p, hp⟩
            exact ⟨p, fun g ↦ by
              change (A.baseMorphism.onPoints g).val i = _
              exact hp g⟩ }
      map_one := pointHom.map_one
      map_mul := pointHom.map_mul }

/-- The inverse coordinate map from the closed base copy back to the original
group. -/
@[expose]
public noncomputable def Action.baseCarrierInverse
    {X : Type u} {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) :
    @Theory.AlgebraicGroup.Morphism k _
      (@ClosedSubgroup.carrierVariety k _ A.semidirectVariety
        A.semidirectAlgebraicGroup A.baseClosedSubgroup) G
      (@ClosedSubgroup.carrierAlgebraicGroup k _
        A.semidirectVariety A.semidirectAlgebraicGroup
        A.baseClosedSubgroup)
      (inferInstance : AlgebraicGroup G) := by
  letI : AlgebraicGroup A.semidirectVariety := A.semidirectAlgebraicGroup
  let H := A.baseClosedSubgroup
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let eMul := Equiv.mulEquiv A.semidirectPointEquiv
  exact
    { toVariety :=
        { toFun := fun x ↦
            (A.semidirectPointEquiv (H.inclusion.onPoints x)).left
          regular := by
            intro i
            exact ⟨MvPolynomial.X (Sum.inl i), fun x ↦ by
              rw [show evalPolynomial x.val (MvPolynomial.X (Sum.inl i)) =
                x.val (Sum.inl i) by simp [evalPolynomial]]
              rfl⟩ }
      map_one := by
        change (A.semidirectPointEquiv (H.inclusion.onPoints 1)).left = 1
        have hincOne : H.inclusion.onPoints 1 = 1 := H.inclusion.map_one
        rw [hincOne]
        exact congrArg SemidirectProduct.left eMul.map_one
      map_mul := by
        intro x y
        change (A.semidirectPointEquiv
          (H.inclusion.onPoints (x * y))).left =
            (A.semidirectPointEquiv (H.inclusion.onPoints x)).left *
              (A.semidirectPointEquiv (H.inclusion.onPoints y)).left
        have hincMul : H.inclusion.onPoints (x * y) =
            H.inclusion.onPoints x * H.inclusion.onPoints y :=
          H.inclusion.map_mul x y
        rw [hincMul]
        have heMul := eMul.map_mul
          (H.inclusion.onPoints x) (H.inclusion.onPoints y)
        change A.semidirectPointEquiv
            (H.inclusion.onPoints x * H.inclusion.onPoints y) =
          A.semidirectPointEquiv (H.inclusion.onPoints x) *
            A.semidirectPointEquiv (H.inclusion.onPoints y) at heMul
        rw [heMul, SemidirectProduct.mul_left]
        have hxker := (H.pointEquiv x).property
        change A.rightMorphism.onPoints (H.inclusion.onPoints x) = 1 at hxker
        have hxright := congrArg (finiteGroupPointEquiv (k := k) X) hxker
        simp [Theory.AlgebraicGroup.Action.rightMorphism,
          Theory.AlgebraicGroup.Morphism.onPoints] at hxright
        have hOne : (finiteGroupPointEquiv (k := k) X)
            (1 : Variety.Point (finiteGroupVariety k X)) = 1 := by
          change (finiteGroupPointEquiv (k := k) X)
              ((finiteGroupPointEquiv (k := k) X).symm 1) = 1
          exact (finiteGroupPointEquiv (k := k) X).apply_symm_apply 1
        rw [hOne] at hxright
        change (A.semidirectPointEquiv
            (H.inclusion.toVariety.toFun x)).right = 1 at hxright
        change (A.semidirectPointEquiv
            (H.inclusion.toVariety.toFun x)).left *
              (A.toMulAut
                (A.semidirectPointEquiv
                  (H.inclusion.toVariety.toFun x)).right)
                (A.semidirectPointEquiv
                  (H.inclusion.toVariety.toFun y)).left =
            (A.semidirectPointEquiv
              (H.inclusion.toVariety.toFun x)).left *
              (A.semidirectPointEquiv
                (H.inclusion.toVariety.toFun y)).left
        rw [hxright]
        simp }

/-- The base group and its canonical closed kernel copy are isomorphic as
algebraic groups. -/
@[expose]
public noncomputable def Action.baseIso
    {X : Type u} {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) :
    @Theory.AlgebraicGroup.Iso k _ G
      (@ClosedSubgroup.carrierVariety k _ A.semidirectVariety
        A.semidirectAlgebraicGroup A.baseClosedSubgroup)
      (inferInstance : AlgebraicGroup G)
      (@ClosedSubgroup.carrierAlgebraicGroup k _
        A.semidirectVariety A.semidirectAlgebraicGroup
        A.baseClosedSubgroup) := by
  letI : AlgebraicGroup A.semidirectVariety := A.semidirectAlgebraicGroup
  let H := A.baseClosedSubgroup
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  exact
    { hom := A.baseCarrierHom
      inv := A.baseCarrierInverse
      hom_inv_id := by
        intro g
        rfl
      inv_hom_id := by
        intro x
        apply H.inclusion_injective
        change A.baseMorphism.onPoints
            (A.baseCarrierInverse.onPoints x) =
          H.inclusion.onPoints x
        let e := A.semidirectPointEquiv
        have hxker := (H.pointEquiv x).property
        change A.rightMorphism.onPoints (H.inclusion.onPoints x) = 1 at hxker
        have hxright := congrArg (finiteGroupPointEquiv (k := k) X) hxker
        simp [Theory.AlgebraicGroup.Action.rightMorphism,
          Theory.AlgebraicGroup.Morphism.onPoints] at hxright
        have hOne : (finiteGroupPointEquiv (k := k) X)
            (1 : Variety.Point (finiteGroupVariety k X)) = 1 := by
          change (finiteGroupPointEquiv (k := k) X)
              ((finiteGroupPointEquiv (k := k) X).symm 1) = 1
          exact (finiteGroupPointEquiv (k := k) X).apply_symm_apply 1
        rw [hOne] at hxright
        apply e.injective
        have hbase :
            e (A.baseMorphism.onPoints
              (A.baseCarrierInverse.onPoints x)) =
              (⟨A.baseCarrierInverse.onPoints x, 1⟩ :
                SemidirectProduct (Variety.Point G) X A.toMulAut) := by
          simp only [Theory.AlgebraicGroup.Action.baseMorphism,
            Theory.AlgebraicGroup.Morphism.onPoints]
          change e (e.symm
            (⟨A.baseCarrierInverse.onPoints x, 1⟩ :
              SemidirectProduct (Variety.Point G) X A.toMulAut)) =
            ⟨A.baseCarrierInverse.onPoints x, 1⟩
          exact e.apply_symm_apply _
        rw [hbase]
        simp [Theory.AlgebraicGroup.Action.baseCarrierInverse,
          Theory.AlgebraicGroup.Morphism.onPoints]
        cases hxe : e (H.inclusion.toVariety.toFun x) with
        | mk u a =>
            rw [hxe] at hxright
            have ha : a = 1 := by simpa using hxright
            subst a
            rfl }

end Theory.AlgebraicGroup
