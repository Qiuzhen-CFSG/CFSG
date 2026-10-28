module

public import Theory.AlgebraicGroup.ClosedSubgroup.Basic

universe u

/-! Restricting algebraic-group morphisms to closed subgroup codomains. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- Restrict the codomain of an algebraic-group morphism to a closed subgroup
containing its pointwise image. -/
@[expose]
public def Morphism.codRestrictClosedSubgroup
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (T : ClosedSubgroup H)
    (hmap : ∀ x, f.onPoints x ∈ T.toSubgroup) :
    AlgebraicGroup.Morphism G T.carrierVariety where
  toVariety :=
    { toFun := fun x => T.pointEquiv.symm ⟨f.onPoints x, hmap x⟩
      regular := by
        intro i
        rcases f.toVariety.regular i with ⟨p, hp⟩
        refine ⟨p, fun x => ?_⟩
        change (T.pointEquiv (T.pointEquiv.symm
          ⟨f.onPoints x, hmap x⟩)).val.val i = evalPolynomial x.val p
        rw [T.pointEquiv.apply_symm_apply]
        exact hp x }
  map_one := by
    apply T.inclusion_injective
    change (T.pointEquiv (T.pointEquiv.symm
      ⟨f.onPoints 1, hmap 1⟩)).val = (T.pointEquiv 1).val
    rw [T.pointEquiv.apply_symm_apply]
    exact f.onPoints.map_one
  map_mul := by
    intro x y
    apply T.inclusion_injective
    change (T.pointEquiv (T.pointEquiv.symm
      ⟨f.onPoints (x * y), hmap (x * y)⟩)).val =
        (T.pointEquiv
          (T.pointEquiv.symm ⟨f.onPoints x, hmap x⟩ *
            T.pointEquiv.symm ⟨f.onPoints y, hmap y⟩)).val
    rw [T.pointEquiv.apply_symm_apply]
    exact f.onPoints.map_mul x y

/-- Including a codomain-restricted morphism recovers the original point. -/
public lemma Morphism.codRestrictClosedSubgroup_inclusion_apply
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (T : ClosedSubgroup H)
    (hmap : ∀ x, f.onPoints x ∈ T.toSubgroup) (x : Variety.Point G) :
    T.inclusion.onPoints (f.codRestrictClosedSubgroup T hmap |>.onPoints x) =
      f.onPoints x := by
  change (T.pointEquiv (T.pointEquiv.symm
    ⟨f.onPoints x, hmap x⟩)).val = f.onPoints x
  rw [T.pointEquiv.apply_symm_apply]

end

section

variable {k : Type u} [Field k]

/-- The closed preimage of a closed subgroup under an algebraic-group morphism. -/
@[expose]
public def Morphism.closedSubgroupPreimage
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (S : ClosedSubgroup H) :
    ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup (S.toSubgroup.comap f.onPoints) (by
    change IsZariskiClosed G
      (f.onPoints ⁻¹' (S.toSubgroup : Set (Variety.Point H)))
    exact f.toVariety.isZariskiClosed_preimage S.isZariskiClosed)

/-- A morphism restricted from the closed preimage of a closed subgroup to
that subgroup. -/
@[expose]
public def Morphism.preimageRestriction
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (S : ClosedSubgroup H) :
    AlgebraicGroup.Morphism (f.closedSubgroupPreimage S).carrierVariety
      S.carrierVariety :=
  (f.comp (f.closedSubgroupPreimage S).inclusion).codRestrictClosedSubgroup S
    (fun x => (f.closedSubgroupPreimage S).pointEquiv x |>.property)

/-- Including a preimage restriction recovers the original morphism. -/
public lemma Morphism.preimageRestriction_inclusion_apply
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (S : ClosedSubgroup H)
    (x : Variety.Point (f.closedSubgroupPreimage S).carrierVariety) :
    S.inclusion.onPoints ((f.preimageRestriction S).onPoints x) =
      f.onPoints ((f.closedSubgroupPreimage S).inclusion.onPoints x) :=
  AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _

/-- A surjective morphism restricts surjectively to the preimage of every
closed subgroup. -/
public theorem Morphism.preimageRestriction_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (hf : Function.Surjective f.onPoints)
    (S : ClosedSubgroup H) :
    Function.Surjective (f.preimageRestriction S).onPoints := by
  intro y
  obtain ⟨x, hx⟩ := hf (S.inclusion.onPoints y)
  let P := f.closedSubgroupPreimage S
  have hxP : x ∈ P := by
    change f.onPoints x ∈ S
    rw [hx]
    exact (S.pointEquiv y).property
  let z : Variety.Point P.carrierVariety := P.pointEquiv.symm ⟨x, hxP⟩
  refine ⟨z, ?_⟩
  apply S.inclusion_injective
  rw [f.preimageRestriction_inclusion_apply]
  change f.onPoints x = S.inclusion.onPoints y
  exact hx

end

section

variable {k : Type u} [Field k]

/-- The closed preimage of a normal closed subgroup is normal. -/
public lemma Morphism.closedSubgroupPreimage_normal
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    {S : ClosedSubgroup H} (hS : S.toSubgroup.Normal) :
    (f.closedSubgroupPreimage S).toSubgroup.Normal := by
  change (S.toSubgroup.comap f.onPoints).Normal
  exact hS.comap f.onPoints

end

section

variable {k : Type u} [Field k]

public lemma Morphism.codRestrictClosedSubgroup_kernel_eq
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (T : ClosedSubgroup H)
    (hmap : ∀ x, f.onPoints x ∈ T.toSubgroup) :
    (f.codRestrictClosedSubgroup T hmap).kernel = f.kernel := by
  ext x
  constructor
  · intro hx
    apply MonoidHom.mem_ker.mpr
    have hx' := congrArg T.inclusion.onPoints (MonoidHom.mem_ker.mp hx)
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply] at hx'
    simpa using hx'
  · intro hx
    apply MonoidHom.mem_ker.mpr
    apply T.inclusion_injective
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
    exact MonoidHom.mem_ker.mp hx

end

end Theory.AlgebraicGroup

