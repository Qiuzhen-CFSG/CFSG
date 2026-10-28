module

public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Isomorphism
public import Theory.AlgebraicGroup.Jordan.CommutativeComponents
public import Theory.AlgebraicGroup.Morphism.CodRestrict

/-!
# The commutative algebraic-group Jordan direct product

Let `G` be a commutative algebraic group over an algebraically closed field. The kernels of
the regular unipotent and semisimple component morphisms define closed subgroups whose ambient
points are exactly the semisimple and unipotent elements. Multiplication is an algebraic-group
isomorphism from their product onto `G`, with inverse given by the two Jordan components.

Regularity is supplied by `Jordan.CommutativeRegularity`; the remaining inverse identities
follow from existence and uniqueness of Jordan decomposition. This is Bor1, Chapter 1,
Theorem 4.7, packaged as membership and product-isomorphism APIs for downstream solvable and
nilpotent algebraic-group arguments.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The closed subgroup of semisimple points in a commutative algebraic group. -/
@[expose]
public noncomputable def commutativeSemisimpleSubgroup
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) : ClosedSubgroup G :=
  (commutativeUnipotentComponentMorphism G hcomm).kernelClosedSubgroup

/-- The closed subgroup of unipotent points in a commutative algebraic group. -/
@[expose]
public noncomputable def commutativeUnipotentSubgroup
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) : ClosedSubgroup G :=
  (commutativeSemisimpleComponentMorphism G hcomm).kernelClosedSubgroup

/-- The canonical algebraic-group structure on the semisimple closed subgroup. -/
public noncomputable instance commutativeSemisimpleSubgroupAlgebraicGroup
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) :
    AlgebraicGroup (commutativeSemisimpleSubgroup G hcomm).carrierVariety :=
  ClosedSubgroup.carrierAlgebraicGroup _

/-- The canonical algebraic-group structure on the unipotent closed subgroup. -/
public noncomputable instance commutativeUnipotentSubgroupAlgebraicGroup
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) :
    AlgebraicGroup (commutativeUnipotentSubgroup G hcomm).carrierVariety :=
  ClosedSubgroup.carrierAlgebraicGroup _

/-- The product algebraic-group structure on the semisimple and unipotent factors. -/
public noncomputable instance commutativeJordanProductAlgebraicGroup
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) :
    AlgebraicGroup
      (Variety.prod (commutativeSemisimpleSubgroup G hcomm).carrierVariety
        (commutativeUnipotentSubgroup G hcomm).carrierVariety) := by
  letI : AlgebraicGroup
      (commutativeSemisimpleSubgroup G hcomm).carrierVariety :=
    (commutativeSemisimpleSubgroup G hcomm).carrierAlgebraicGroup
  letI : AlgebraicGroup
      (commutativeUnipotentSubgroup G hcomm).carrierVariety :=
    (commutativeUnipotentSubgroup G hcomm).carrierAlgebraicGroup
  exact AlgebraicGroup.prod _ _

/-- Membership in the semisimple factor is exactly semisimplicity in the ambient group. -/
public theorem mem_commutativeSemisimpleSubgroup_iff
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) (g : Variety.Point G) :
    g ∈ commutativeSemisimpleSubgroup G hcomm ↔ IsSemisimpleElement G g := by
  change (commutativeUnipotentComponentMorphism G hcomm).onPoints g = 1 ↔ _
  rw [commutativeUnipotentComponentMorphism_apply,
    isSemisimpleElement_iff_unipotentComponent_eq_one]

/-- Membership in the unipotent factor is exactly unipotence in the ambient group. -/
public theorem mem_commutativeUnipotentSubgroup_iff
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) (g : Variety.Point G) :
    g ∈ commutativeUnipotentSubgroup G hcomm ↔ IsUnipotentElement G g := by
  change (commutativeSemisimpleComponentMorphism G hcomm).onPoints g = 1 ↔ _
  rw [commutativeSemisimpleComponentMorphism_apply,
    isUnipotentElement_iff_semisimpleComponent_eq_one]

/-- Multiplication from the product of a commutative algebraic group with itself. -/
@[expose]
public def commutativeMultiplicationMorphism
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) :
    AlgebraicGroup.Morphism (Variety.prod G G) G where
  toVariety := AlgebraicGroup.mulMorphism G
  map_one := mul_one 1
  map_mul := by
    intro x y
    have hc := isMulCommutative_iff.mp hcomm
    let px := Variety.prodPointEquiv G G x
    let py := Variety.prodPointEquiv G G y
    change (px.1 * py.1) * (px.2 * py.2) =
      (px.1 * px.2) * (py.1 * py.2)
    calc
      (px.1 * py.1) * (px.2 * py.2) =
          px.1 * (py.1 * px.2) * py.2 := by group
      _ = px.1 * (px.2 * py.1) * py.2 := by rw [hc py.1 px.2]
      _ = (px.1 * px.2) * (py.1 * py.2) := by group

/-- Multiplication restricted to the semisimple and unipotent closed subgroups. -/
@[expose]
public noncomputable def commutativeJordanProductMorphism
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) :
    AlgebraicGroup.Morphism
      (Variety.prod (commutativeSemisimpleSubgroup G hcomm).carrierVariety
        (commutativeUnipotentSubgroup G hcomm).carrierVariety) G := by
  let S := commutativeSemisimpleSubgroup G hcomm
  let U := commutativeUnipotentSubgroup G hcomm
  exact (commutativeMultiplicationMorphism G hcomm).comp
    (AlgebraicGroup.Morphism.prod
      (S.inclusion.comp (AlgebraicGroup.Morphism.fst S.carrierVariety U.carrierVariety))
      (U.inclusion.comp (AlgebraicGroup.Morphism.snd S.carrierVariety U.carrierVariety)))

/-- Evaluation of the restricted multiplication morphism on ambient points. -/
public lemma commutativeJordanProductMorphism_apply
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G))
    (x : Variety.Point
      (Variety.prod (commutativeSemisimpleSubgroup G hcomm).carrierVariety
        (commutativeUnipotentSubgroup G hcomm).carrierVariety)) :
    (commutativeJordanProductMorphism G hcomm).onPoints x =
      (commutativeSemisimpleSubgroup G hcomm).inclusion.onPoints
          (Variety.prodPointEquiv _ _ x).1 *
        (commutativeUnipotentSubgroup G hcomm).inclusion.onPoints
          (Variety.prodPointEquiv _ _ x).2 := rfl

/-- The inverse Jordan-component morphism into the semisimple-unipotent product. -/
@[expose]
public noncomputable def commutativeJordanInverseMorphism
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) :
    AlgebraicGroup.Morphism G
      (Variety.prod (commutativeSemisimpleSubgroup G hcomm).carrierVariety
        (commutativeUnipotentSubgroup G hcomm).carrierVariety) := by
  let S := commutativeSemisimpleSubgroup G hcomm
  let U := commutativeUnipotentSubgroup G hcomm
  let s : AlgebraicGroup.Morphism G S.carrierVariety :=
    (commutativeSemisimpleComponentMorphism G hcomm).codRestrictClosedSubgroup S
      (fun g => (mem_commutativeSemisimpleSubgroup_iff G hcomm _).mpr
        (jordanDecomposition g).semisimple)
  let u : AlgebraicGroup.Morphism G U.carrierVariety :=
    (commutativeUnipotentComponentMorphism G hcomm).codRestrictClosedSubgroup U
      (fun g => by
        apply (mem_commutativeUnipotentSubgroup_iff G hcomm _).mpr
        rw [commutativeUnipotentComponentMorphism_apply]
        exact (jordanDecomposition g).unipotent)
  exact AlgebraicGroup.Morphism.prod s u

/-- The ambient value of the first inverse component is the semisimple Jordan component. -/
public lemma commutativeJordanInverseMorphism_fst_apply
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) (g : Variety.Point G) :
    (commutativeSemisimpleSubgroup G hcomm).inclusion.onPoints
        (Variety.prodPointEquiv _ _
          ((commutativeJordanInverseMorphism G hcomm).onPoints g)).1 =
      (jordanDecomposition g).semisimplePart := by
  let S := commutativeSemisimpleSubgroup G hcomm
  change (S.pointEquiv
    (S.pointEquiv.symm
      ⟨(commutativeSemisimpleComponentMorphism G hcomm).onPoints g, _⟩)).val = _
  rw [S.pointEquiv.apply_symm_apply]
  exact commutativeSemisimpleComponentMorphism_apply G hcomm g

/-- The ambient value of the second inverse component is the unipotent Jordan component. -/
public lemma commutativeJordanInverseMorphism_snd_apply
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) (g : Variety.Point G) :
    (commutativeUnipotentSubgroup G hcomm).inclusion.onPoints
        (Variety.prodPointEquiv _ _
          ((commutativeJordanInverseMorphism G hcomm).onPoints g)).2 =
      (jordanDecomposition g).unipotentPart := by
  let U := commutativeUnipotentSubgroup G hcomm
  change (U.pointEquiv
    (U.pointEquiv.symm
      ⟨(commutativeUnipotentComponentMorphism G hcomm).onPoints g, _⟩)).val = _
  rw [U.pointEquiv.apply_symm_apply]
  exact commutativeUnipotentComponentMorphism_apply G hcomm g

/-- Bor1, Chapter 1, Theorem 4.7: multiplication identifies the semisimple and unipotent
closed subgroups of a commutative algebraic group with the whole group. -/
@[expose]
public noncomputable def commutativeJordanProductIso
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) :
    AlgebraicGroup.Iso
      (Variety.prod (commutativeSemisimpleSubgroup G hcomm).carrierVariety
        (commutativeUnipotentSubgroup G hcomm).carrierVariety) G where
  hom := commutativeJordanProductMorphism G hcomm
  inv := commutativeJordanInverseMorphism G hcomm
  hom_inv_id := by
    intro x
    let S := commutativeSemisimpleSubgroup G hcomm
    let U := commutativeUnipotentSubgroup G hcomm
    let p := Variety.prodPointEquiv S.carrierVariety U.carrierVariety x
    let sx := S.inclusion.onPoints p.1
    let ux := U.inclusion.onPoints p.2
    have hs : IsSemisimpleElement G sx :=
      (mem_commutativeSemisimpleSubgroup_iff G hcomm sx).mp
        (S.pointEquiv p.1).property
    have hu : IsUnipotentElement G ux :=
      (mem_commutativeUnipotentSubgroup_iff G hcomm ux).mp
        (U.pointEquiv p.2).property
    let d : JordanDecomposition (sx * ux) :=
      { semisimplePart := sx
        unipotentPart := ux
        eq_mul := rfl
        commute := isMulCommutative_iff.mp hcomm sx ux
        semisimple := hs
        unipotent := hu }
    have hd := (jordanDecomposition (sx * ux)).unique d
    apply (Variety.prodPointEquiv S.carrierVariety U.carrierVariety).injective
    apply Prod.ext
    · apply S.inclusion_injective
      rw [commutativeJordanInverseMorphism_fst_apply,
        commutativeJordanProductMorphism_apply]
      exact congrArg JordanDecomposition.semisimplePart hd
    · apply U.inclusion_injective
      rw [commutativeJordanInverseMorphism_snd_apply,
        commutativeJordanProductMorphism_apply]
      exact congrArg JordanDecomposition.unipotentPart hd
  inv_hom_id := by
    intro g
    rw [commutativeJordanProductMorphism_apply,
      commutativeJordanInverseMorphism_fst_apply,
      commutativeJordanInverseMorphism_snd_apply]
    exact (jordanDecomposition g).eq_mul.symm


end Theory.AlgebraicGroup
