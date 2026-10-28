module

public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Theory.AlgebraicGroup.Morphism.Image
public import Theory.AlgebraicGroup.Morphism.Kernel
public import Theory.AlgebraicGroup.Variety.PolynomialFunction

universe u

/-! Closed subgroups, their carrier algebraic groups, inclusions, and restrictions. -/

namespace Theory.AlgebraicGroup

open scoped TensorProduct

open LinearMap Submodule

variable {k : Type u} [Field k]

variable {k : Type u} [Field k]

/-- A closed subgroup is an ordinary subgroup of the rational points whose
carrier is Zariski closed.  It extends Mathlib's topological-group
`ClosedSubgroup`, the topology on the rational points being the Zariski
topology. -/
public structure ClosedSubgroup (G : Variety k) [AlgebraicGroup G]
    extends _root_.ClosedSubgroup (Variety.Point G)

/-- The closed subgroups of an algebraic group form a `SetLike`: the carrier
is the underlying subgroup, and the order is inclusion. -/
public instance ClosedSubgroup.instSetLike (G : Variety k) [AlgebraicGroup G] :
    SetLike (ClosedSubgroup G) (Variety.Point G) where
  coe := fun H => (H.toSubgroup : Set (Variety.Point G))
  coe_injective := by
    intro H K h
    cases H
    cases K
    congr
    exact SetLike.coe_injective h

/-- The order on closed subgroups is inclusion of carriers. -/
public instance ClosedSubgroup.instLE (G : Variety k) [AlgebraicGroup G] :
    LE (ClosedSubgroup G) where
  le := fun B C => (B : Set (Variety.Point G)) ⊆ (C : Set (Variety.Point G))

/-- The Zariski-closedness of a closed subgroup, in the zero-locus sense. -/
public lemma ClosedSubgroup.isZariskiClosed {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) :
    IsZariskiClosed G (H.toSubgroup : Set (Variety.Point G)) :=
  Variety.isClosed_iff_isZariskiClosed.mp H.isClosed'

/-- The closed subgroup built from an ordinary subgroup whose carrier is
Zariski closed. -/
@[expose]
public def ClosedSubgroup.ofSubgroup {G : Variety k} [AlgebraicGroup G]
    (H : Subgroup (Variety.Point G))
    (h : IsZariskiClosed G (H : Set (Variety.Point G))) : ClosedSubgroup G where
  toSubgroup := H
  isClosed' := by
    rw [Variety.isClosed_iff_isZariskiClosed]
    exact h

/-- The trivial closed subgroup. -/
@[expose]
public def ClosedSubgroup.bot {G : Variety k} [AlgebraicGroup G] :
    ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup ⊥ (by
    simpa using isZariskiClosed_singleton G (1 : Variety.Point G))

/-- The whole group as a closed subgroup. -/
@[expose]
public def ClosedSubgroup.top {G : Variety k} [AlgebraicGroup G] :
    ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup ⊤ (by
    refine ⟨∅, ?_⟩
    ext x
    simp)

/-- The kernel of an algebraic-group morphism as a genuine closed subgroup. -/
@[expose]
public def Morphism.kernelClosedSubgroup
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Theory.AlgebraicGroup.Morphism G H) : ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup f.kernel f.kernel_isZariskiClosed

public lemma Morphism.kernelClosedSubgroup_carrier
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Theory.AlgebraicGroup.Morphism G H) :
    (f.kernelClosedSubgroup.toSubgroup : Set (Variety.Point G)) =
      (f.kernel : Set (Variety.Point G)) := rfl

public lemma Morphism.kernelClosedSubgroup_isNormal
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Theory.AlgebraicGroup.Morphism G H) :
    f.kernelClosedSubgroup.toSubgroup.Normal := by
  change f.onPoints.ker.Normal
  exact MonoidHom.normal_ker _

/-- The image of a morphism with finite source is an actual closed subgroup. -/
@[expose]
public def Morphism.finiteImageClosedSubgroup
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    [Finite (Variety.Point G)] (f : Theory.AlgebraicGroup.Morphism G H) :
    ClosedSubgroup H :=
  ClosedSubgroup.ofSubgroup f.image f.image_isZariskiClosed_of_finiteDomain

public lemma Morphism.finiteImageClosedSubgroup_carrier
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    [Finite (Variety.Point G)] (f : Theory.AlgebraicGroup.Morphism G H) :
    (f.finiteImageClosedSubgroup.toSubgroup : Set (Variety.Point H)) =
      (f.image : Set (Variety.Point H)) := rfl

/-- The zero-locus presentation induced on a closed subgroup. -/
public abbrev ClosedSubgroup.carrierVariety {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) : Variety k :=
  Variety.closedSubvariety H.isZariskiClosed

/-- Points of the induced zero locus are the elements of the underlying
ordinary subgroup. -/
public abbrev ClosedSubgroup.pointEquiv {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) : Variety.Point H.carrierVariety ≃ H.toSubgroup :=
  Variety.closedSubvarietyPointEquiv H.isZariskiClosed

/-- The closed-subvariety equivalence preserves ambient coordinates. -/
public lemma ClosedSubgroup.pointEquiv_val {G : Variety k}
    [AlgebraicGroup G] (H : ClosedSubgroup G) (x : Variety.Point H.carrierVariety) :
    (H.pointEquiv x).val.val = x.val := rfl

public instance ClosedSubgroup.carrierAlgebraicGroup
    {G : Variety k} [hG : AlgebraicGroup G] (H : ClosedSubgroup G) :
    AlgebraicGroup H.carrierVariety := by
  let hGroup : Group (Variety.Point H.carrierVariety) := H.pointEquiv.group
  letI : Group (Variety.Point H.carrierVariety) := hGroup
  exact
    { toGroup := hGroup
      mulPolynomial := hG.mulPolynomial
      invPolynomial := hG.invPolynomial
      mul_regular := by
        intro i x y
        change (H.pointEquiv (x * y)).val.val i =
          evalPolynomial
            (Sum.elim (H.pointEquiv x).val.val (H.pointEquiv y).val.val)
            (hG.mulPolynomial i)
        have hmul : H.pointEquiv (x * y) = H.pointEquiv x * H.pointEquiv y := rfl
        rw [hmul]
        exact hG.mul_regular i (H.pointEquiv x).val (H.pointEquiv y).val
      inv_regular := by
        intro i x
        change (H.pointEquiv x⁻¹).val.val i =
          evalPolynomial (H.pointEquiv x).val.val (hG.invPolynomial i)
        have hinv : H.pointEquiv x⁻¹ = (H.pointEquiv x)⁻¹ := rfl
        rw [hinv]
        exact hG.inv_regular i (H.pointEquiv x).val }

/-- The canonical polynomial inclusion of a closed subgroup. -/
@[expose]
public def ClosedSubgroup.inclusion {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) : Theory.AlgebraicGroup.Morphism H.carrierVariety G where
  toVariety :=
    { toFun := fun x ↦ (H.pointEquiv x).val
      regular := fun i ↦ ⟨MvPolynomial.X i, fun x ↦ by
        rw [H.pointEquiv_val]
        simp [evalPolynomial]⟩ }
  map_one := by
    change (H.pointEquiv 1).val = 1
    have hone : H.pointEquiv 1 = 1 := rfl
    rw [hone]
    rfl
  map_mul := by
    intro x y
    change (H.pointEquiv (x * y)).val =
      (H.pointEquiv x).val * (H.pointEquiv y).val
    have hmul : H.pointEquiv (x * y) = H.pointEquiv x * H.pointEquiv y := rfl
    rw [hmul]
    rfl

@[expose]
public def ClosedSubgroup.includePoint
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (x : Variety.Point H.carrierVariety) : Variety.Point G :=
  (H.pointEquiv x).1

/-- The canonical inclusion of a closed subgroup is injective. -/
public lemma ClosedSubgroup.inclusion_injective {G : Variety k}
    [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Function.Injective H.inclusion.onPoints := by
  intro x y hxy
  apply H.pointEquiv.injective
  apply Subtype.ext
  exact hxy

/-- The range of the canonical inclusion is the original subgroup. -/
public lemma ClosedSubgroup.range_inclusion {G : Variety k}
    [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Set.range H.inclusion.onPoints = (H.toSubgroup : Set (Variety.Point G)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (H.pointEquiv y).property
  · intro hx
    refine ⟨H.pointEquiv.symm ⟨x, hx⟩, ?_⟩
    change (H.pointEquiv (H.pointEquiv.symm ⟨x, hx⟩)).val = x
    rw [H.pointEquiv.apply_symm_apply]

/-- Every polynomial function on a closed subgroup is the restriction of an
ambient polynomial function. -/
public lemma ClosedSubgroup.exists_polynomialFunction_extension
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (a : Variety.PolynomialFunction H.carrierVariety) :
    ∃ b : Variety.PolynomialFunction G,
      ∀ x, b (H.inclusion.onPoints x) = a x := by
  rcases a.representedBy with ⟨p, hp⟩
  refine ⟨Variety.PolynomialFunction.ofPolynomial G p, ?_⟩
  intro x
  change evalPolynomial (H.pointEquiv x).val.val p = a x
  rw [H.pointEquiv_val]
  exact (hp x).symm

/-- Restriction of polynomial functions along the closed-subgroup inclusion. -/
@[expose]
public def ClosedSubgroup.restrictionRingHom
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    G.PolynomialFunction →+* H.carrierVariety.PolynomialFunction :=
  H.inclusion.toVariety.pullbackRingHom

public lemma ClosedSubgroup.restrictionRingHom_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (a : G.PolynomialFunction) (x : Variety.Point H.carrierVariety) :
    H.restrictionRingHom a x = a (H.inclusion.onPoints x) := by
  change Variety.PolynomialFunction.pullback H.inclusion.toVariety a x = _
  rfl

public lemma ClosedSubgroup.restrictionRingHom_surjective
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Function.Surjective H.restrictionRingHom := by
  intro a
  rcases H.exists_polynomialFunction_extension a with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  exact hb x

section

variable {k : Type u} [Field k]

/-- The intersection of two closed subgroups. -/
@[expose]
public def ClosedSubgroup.inter {G : Variety k} [AlgebraicGroup G]
    (B C : ClosedSubgroup G) : ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup (B.toSubgroup ⊓ C.toSubgroup) (by
    change IsZariskiClosed G
      ((B.toSubgroup : Set (Variety.Point G)) ∩
        (C.toSubgroup : Set (Variety.Point G)))
    exact isZariskiClosed_inter B.isZariskiClosed C.isZariskiClosed)

end

section

variable {k : Type u} [Field k]

/-- Membership in the intersection of closed subgroups. -/
public lemma ClosedSubgroup.mem_inter_iff
    {G : Variety k} [AlgebraicGroup G]
    (B C : ClosedSubgroup G) (x : Variety.Point G) :
    x ∈ B.inter C ↔ x ∈ B ∧ x ∈ C := by
  rfl

end

end Theory.AlgebraicGroup

