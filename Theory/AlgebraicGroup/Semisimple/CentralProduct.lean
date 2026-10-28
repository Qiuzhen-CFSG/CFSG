module

public import Theory.AlgebraicGroup.ClosedSubgroup.Product

universe u

/-!
  A source-independent central-product core for reductive groups.

  The missing root-data theorem in GLS3 constructs the two factors.  Once
  those factors and their pointwise factorisation are available, the routine
  group-theoretic consequences below are useful on their own: multiplication
  from the product of the factors is a surjective homomorphism, its range is
  the ambient group, and every kernel coordinate is central in the ambient
  group.  No root-system or classification statement is hidden here.
-/

namespace Theory.AlgebraicGroup

open scoped Pointwise

variable {k : Type u} [Field k]

public structure IsCentralProductData
    {G : Variety k} [AlgebraicGroup G]
    (S Z : ClosedSubgroup G) : Prop where
  central : Z.toSubgroup ≤ Subgroup.center (Variety.Point G)
  factorization : ∀ x : Variety.Point G,
    ∃ s z, s ∈ S ∧ z ∈ Z ∧ x = s * z

namespace IsCentralProductData

public def multiplicationHom
    {G : Variety k} [AlgebraicGroup G]
    {S Z : ClosedSubgroup G}
    (h : IsCentralProductData S Z) :
    (S.toSubgroup × Z.toSubgroup) →* Variety.Point G :=
  { toFun := fun p => (p.1 : Variety.Point G) * (p.2 : Variety.Point G)
    map_one' := by simp
    map_mul' := by
      intro p q
      change (p.1.1 * q.1.1) * (p.2.1 * q.2.1) =
        (p.1.1 * p.2.1) * (q.1.1 * q.2.1)
      symm
      have hcomm : p.2.1 * q.1.1 = q.1.1 * p.2.1 := by
        exact (Subgroup.mem_center_iff.mp (h.central p.2.2) q.1.1).symm
      calc
        (p.1.1 * p.2.1) * (q.1.1 * q.2.1) =
            p.1.1 * (p.2.1 * q.1.1) * q.2.1 := by simp [mul_assoc]
        _ = p.1.1 * (q.1.1 * p.2.1) * q.2.1 := by rw [hcomm]
        _ = (p.1.1 * q.1.1) * (p.2.1 * q.2.1) := by group }

public lemma multiplicationHom_surjective
    {G : Variety k} [AlgebraicGroup G]
    {S Z : ClosedSubgroup G}
    (h : IsCentralProductData S Z) :
    Function.Surjective (multiplicationHom h) := by
  intro x
  obtain ⟨s, z, hs, hz, rfl⟩ := h.factorization x
  exact ⟨(⟨s, hs⟩, ⟨z, hz⟩), rfl⟩

public lemma multiplicationHom_range_eq_top
    {G : Variety k} [AlgebraicGroup G]
    {S Z : ClosedSubgroup G}
    (h : IsCentralProductData S Z) :
    (multiplicationHom h).range = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨p, hp⟩ := h.multiplicationHom_surjective x
  exact ⟨p, hp⟩

/-! The same factorisation is represented by a regular multiplication map. -/

public lemma algebraicProductMorphism_surjective
    {G : Variety k} [AlgebraicGroup G]
    {S Z : ClosedSubgroup G}
    (h : IsCentralProductData S Z) :
    ∃ m : Variety.Morphism
      (Variety.prod S.carrierVariety Z.carrierVariety) G,
      Set.range m.toFun = Set.univ := by
  obtain ⟨m, hm⟩ :=
    exists_closedSubgroup_productMorphism_range_eq_pointwise_mul S Z
  refine ⟨m, hm.trans ?_⟩
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨s, z, hs, hz, rfl⟩ := h.factorization x
    exact Set.mem_mul.mpr ⟨s, hs, z, hz, rfl⟩

public lemma sup_eq_top
    {G : Variety k} [AlgebraicGroup G]
    {S Z : ClosedSubgroup G}
    (h : IsCentralProductData S Z) :
    S.toSubgroup ⊔ Z.toSubgroup = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨s, z, hs, hz, rfl⟩ := h.factorization x
  exact (S.toSubgroup ⊔ Z.toSubgroup).mul_mem
    (show s ∈ S.toSubgroup ⊔ Z.toSubgroup from Subgroup.mem_sup_left hs)
    (show z ∈ S.toSubgroup ⊔ Z.toSubgroup from Subgroup.mem_sup_right hz)

public lemma kernel_coordinates_central
    {G : Variety k} [AlgebraicGroup G]
    {S Z : ClosedSubgroup G}
    (h : IsCentralProductData S Z)
    {p : S.toSubgroup × Z.toSubgroup}
    (hp : p ∈ (multiplicationHom h).ker) :
    (p.1 : Variety.Point G) ∈ Subgroup.center (Variety.Point G) ∧
      (p.2 : Variety.Point G) ∈ Subgroup.center (Variety.Point G) := by
  have hprod : (p.1 : Variety.Point G) * (p.2 : Variety.Point G) = 1 := by
    have hprod' := MonoidHom.mem_ker.mp hp
    change (p.1 : Variety.Point G) * (p.2 : Variety.Point G) = 1 at hprod'
    exact hprod'
  have hfirst : (p.1 : Variety.Point G) = (p.2 : Variety.Point G)⁻¹ :=
    eq_inv_of_mul_eq_one_left hprod
  have hsecond : (p.2 : Variety.Point G) ∈
      Subgroup.center (Variety.Point G) := h.central p.2.2
  refine ⟨?_, hsecond⟩
  rw [hfirst]
  exact (Subgroup.center (Variety.Point G)).inv_mem hsecond

end IsCentralProductData

end Theory.AlgebraicGroup
