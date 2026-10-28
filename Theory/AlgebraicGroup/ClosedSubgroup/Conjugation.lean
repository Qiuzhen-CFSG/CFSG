module

public import Theory.AlgebraicGroup.ClosedSubgroup.Normalizer
public import Theory.AlgebraicGroup.Dimension.Isomorphism
public import Theory.AlgebraicGroup.Morphism.CodRestrict

universe u

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- The conjugate `gBg⁻¹` of a closed subgroup `B`. -/
@[expose]
public def ClosedSubgroup.conjugate {G : Variety k} [AlgebraicGroup G]
    (B : ClosedSubgroup G) (g : Variety.Point G) : ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup
    (B.toSubgroup.comap (MulAut.conj g⁻¹).toMonoidHom) (by
      change IsZariskiClosed G
        ((AlgebraicGroup.conjugationByMorphism G g⁻¹).toFun ⁻¹'
          (B.toSubgroup : Set (Variety.Point G)))
      exact
        (AlgebraicGroup.conjugationByMorphism G g⁻¹).isZariskiClosed_preimage
          B.isZariskiClosed)

end

section

variable {k : Type u} [Field k]

/-- Membership in `gBg⁻¹` is detected by conjugating back into `B`. -/
public lemma ClosedSubgroup.mem_conjugate_iff
    {G : Variety k} [AlgebraicGroup G]
    (B : ClosedSubgroup G) (g x : Variety.Point G) :
    x ∈ B.conjugate g ↔ g⁻¹ * x * g ∈ B.toSubgroup := by
  change (MulAut.conj g⁻¹) x ∈ B.toSubgroup ↔ _
  simp

/-- A normalizer element fixes a closed subgroup under conjugation. -/
public lemma ClosedSubgroup.conjugate_eq_self_of_mem_normalizer
    {G : Variety k} [AlgebraicGroup G]
    {B : ClosedSubgroup G} (g : Variety.Point G)
    (hg : g ∈ B.normalizer.toSubgroup) :
    B.conjugate g = B := by
  apply SetLike.coe_injective
  ext x
  change x ∈ B.conjugate g ↔ x ∈ B.toSubgroup
  rw [B.mem_conjugate_iff]
  have hnorm : ∀ y : Variety.Point G, y ∈ B.toSubgroup ↔
      g * y * g⁻¹ ∈ B.toSubgroup :=
    Subgroup.mem_normalizer_iff.mp hg
  have hx := hnorm (g⁻¹ * x * g)
  simpa [mul_assoc] using hx

end

section

variable {k : Type u} [Field k]

/-- Conjugation by `g` identifies a closed subgroup with its conjugate. -/
@[expose]
public def ClosedSubgroup.conjugateIso
    {G : Variety k} [AlgebraicGroup G]
    (B : ClosedSubgroup G) (g : Variety.Point G) :
    AlgebraicGroup.Iso B.carrierVariety (B.conjugate g).carrierVariety := by
  let forwardAmbient : AlgebraicGroup.Morphism B.carrierVariety G :=
    { toVariety :=
        (AlgebraicGroup.conjugationByMorphism G g).comp B.inclusion.toVariety
      map_one := by
        change g * B.inclusion.onPoints 1 * g⁻¹ = 1
        rw [B.inclusion.onPoints.map_one]
        group
      map_mul := by
        intro x y
        change g * B.inclusion.onPoints (x * y) * g⁻¹ =
          (g * B.inclusion.onPoints x * g⁻¹) *
            (g * B.inclusion.onPoints y * g⁻¹)
        rw [B.inclusion.onPoints.map_mul]
        group }
  have hforwardAmbient (x) : forwardAmbient.onPoints x =
      g * B.inclusion.onPoints x * g⁻¹ := by
    exact AlgebraicGroup.conjugationByMorphism_apply G g _
  have hforward : ∀ x, forwardAmbient.onPoints x ∈ B.conjugate g := by
    intro x
    rw [hforwardAmbient, B.mem_conjugate_iff]
    have heq : g⁻¹ * (g * B.inclusion.onPoints x * g⁻¹) * g =
        B.inclusion.onPoints x := by
      group
    rw [heq]
    exact (B.pointEquiv x).property
  let backwardAmbient :
      AlgebraicGroup.Morphism (B.conjugate g).carrierVariety G :=
    { toVariety :=
        (AlgebraicGroup.conjugationByMorphism G g⁻¹).comp
          (B.conjugate g).inclusion.toVariety
      map_one := by
        change g⁻¹ * (B.conjugate g).inclusion.onPoints 1 * (g⁻¹)⁻¹ = 1
        rw [(B.conjugate g).inclusion.onPoints.map_one]
        group
      map_mul := by
        intro x y
        change g⁻¹ * (B.conjugate g).inclusion.onPoints (x * y) * (g⁻¹)⁻¹ =
          (g⁻¹ * (B.conjugate g).inclusion.onPoints x * (g⁻¹)⁻¹) *
            (g⁻¹ * (B.conjugate g).inclusion.onPoints y * (g⁻¹)⁻¹)
        rw [(B.conjugate g).inclusion.onPoints.map_mul]
        group }
  have hbackwardAmbient (x) : backwardAmbient.onPoints x =
      g⁻¹ * (B.conjugate g).inclusion.onPoints x * g := by
    change (AlgebraicGroup.conjugationByMorphism G g⁻¹).toFun
      ((B.conjugate g).inclusion.onPoints x) = _
    simpa only [inv_inv] using
      (AlgebraicGroup.conjugationByMorphism_apply G g⁻¹
        ((B.conjugate g).inclusion.onPoints x))
  have hbackward : ∀ x, backwardAmbient.onPoints x ∈ B := by
    intro x
    rw [hbackwardAmbient]
    exact (B.mem_conjugate_iff g ((B.conjugate g).inclusion.onPoints x)).mp
      ((B.conjugate g).pointEquiv x).property
  let forward :=
    forwardAmbient.codRestrictClosedSubgroup (B.conjugate g) hforward
  let backward := backwardAmbient.codRestrictClosedSubgroup B hbackward
  exact
    { hom := forward
      inv := backward
      hom_inv_id := by
        intro x
        apply B.inclusion_injective
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply,
          hbackwardAmbient]
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply,
          hforwardAmbient]
        group
      inv_hom_id := by
        intro y
        apply (B.conjugate g).inclusion_injective
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply,
          hforwardAmbient]
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply,
          hbackwardAmbient]
        group }

public lemma ClosedSubgroup.conjugateIso_hom_inclusion_apply
    {G : Variety k} [AlgebraicGroup G]
    (B : ClosedSubgroup G) (g : Variety.Point G)
    (x : Variety.Point B.carrierVariety) :
    (B.conjugate g).inclusion.onPoints ((B.conjugateIso g).hom.onPoints x) =
      g * B.inclusion.onPoints x * g⁻¹ := by
  rw [ClosedSubgroup.conjugateIso]
  rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  exact AlgebraicGroup.conjugationByMorphism_apply G g _

public lemma ClosedSubgroup.conjugateIso_inv_inclusion_apply
    {G : Variety k} [AlgebraicGroup G]
    (B : ClosedSubgroup G) (g : Variety.Point G)
    (x : Variety.Point (B.conjugate g).carrierVariety) :
    B.inclusion.onPoints ((B.conjugateIso g).inv.onPoints x) =
      g⁻¹ * (B.conjugate g).inclusion.onPoints x * g := by
  rw [ClosedSubgroup.conjugateIso]
  rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  change (AlgebraicGroup.conjugationByMorphism G g⁻¹).toFun
    ((B.conjugate g).inclusion.onPoints x) = _
  simpa only [inv_inv] using
    (AlgebraicGroup.conjugationByMorphism_apply G g⁻¹
      ((B.conjugate g).inclusion.onPoints x))

end

/-! Conjugation restricted to a normal closed subgroup. -/

section

variable {k : Type u} [Field k]

/-- Conjugation by an ambient point, restricted to a normal closed subgroup. -/
@[expose]
public def ClosedSubgroup.conjugationRestriction
    {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) (hN : H.toSubgroup.Normal)
    (g : Variety.Point G) :
    AlgebraicGroup.Morphism H.carrierVariety H.carrierVariety := by
  let cG : AlgebraicGroup.Morphism G G :=
    { toVariety := AlgebraicGroup.conjugationByMorphism G g
      map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
      map_mul := by
        intro x y
        simp only [AlgebraicGroup.conjugationByMorphism_apply]
        group }
  let cH := cG.comp H.inclusion
  apply cH.codRestrictClosedSubgroup H
  intro x
  have hx : H.inclusion.onPoints x ∈ H.toSubgroup :=
    (H.pointEquiv x).property
  change g * H.inclusion.onPoints x * g⁻¹ ∈ H.toSubgroup
  simpa using hN.conj_mem' (H.inclusion.onPoints x) hx g⁻¹

/-- Including the restricted conjugation recovers ambient conjugation. -/
public lemma ClosedSubgroup.conjugationRestriction_inclusion_apply
    {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) (hN : H.toSubgroup.Normal)
    (g : Variety.Point G) (x : Variety.Point H.carrierVariety) :
    H.inclusion.onPoints ((H.conjugationRestriction hN g).onPoints x) =
      g * H.inclusion.onPoints x * g⁻¹ := by
  rw [ClosedSubgroup.conjugationRestriction]
  rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  exact AlgebraicGroup.conjugationByMorphism_apply G g _

/-- Successive conjugations of a closed subgroup compose in reverse order. -/
public lemma ClosedSubgroup.conjugate_conjugate
    {G : Variety k} [AlgebraicGroup G]
    (B : ClosedSubgroup G) (g h : Variety.Point G) :
    (B.conjugate g).conjugate h = B.conjugate (h * g) := by
  apply SetLike.coe_injective
  ext x
  change (MulAut.conj h⁻¹) x ∈
      (B.toClosedSubgroup.toSubgroup.comap
        (MulAut.conj g⁻¹).toMonoidHom) ↔
    (MulAut.conj (h * g)⁻¹) x ∈ B.toClosedSubgroup.toSubgroup
  simp [mul_assoc]

/-- Conjugation by the identity fixes a closed subgroup. -/
public lemma ClosedSubgroup.conjugate_one
    {G : Variety k} [AlgebraicGroup G] (B : ClosedSubgroup G) :
    B.conjugate 1 = B := by
  apply SetLike.coe_injective
  ext x
  change (MulAut.conj (1 : Variety.Point G)⁻¹) x ∈
      B.toClosedSubgroup.toSubgroup ↔
    x ∈ B.toClosedSubgroup.toSubgroup
  simp

/-- A central element belongs to a closed subgroup as soon as one of its
conjugates belongs to that subgroup. -/
public theorem central_mem_closedSubgroup_of_exists_conjugate_mem
    {G : Variety k} [AlgebraicGroup G]
    (B : ClosedSubgroup G) (z : Variety.Point G)
    (hz : z ∈ Subgroup.center (Variety.Point G))
    (hconj : ∃ g : Variety.Point G, g⁻¹ * z * g ∈ B.toSubgroup) :
    z ∈ B.toSubgroup := by
  obtain ⟨g, hg⟩ := hconj
  have hcomm : g * z = z * g := Subgroup.mem_center_iff.mp hz g
  have heq : g⁻¹ * z * g = z := by
    rw [mul_assoc, ← hcomm]
    simp
  rwa [heq] at hg

/-- Conjugation preserves the dimension of a closed subgroup. -/
public lemma ClosedSubgroup.conjugate_dimension_eq
    [IsAlgClosed k] {G : Variety k} [AlgebraicGroup G]
    (B : ClosedSubgroup G) (g : Variety.Point G) :
    Variety.dimension B.carrierVariety =
      Variety.dimension (B.conjugate g).carrierVariety := by
  exact algebraicGroupIso_dimension_eq (B.conjugateIso g)

end

end Theory.AlgebraicGroup
