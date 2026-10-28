module

public import Theory.AlgebraicGroup.BNPair.SimpleLiftCoverage
public import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
# Collection and exchange for whole relative rays

Ordered positive-ray coordinates, with the marked ray last, let us collect
all other factors into a Borel element whose conjugate by the marked lift
still lies in the Borel. Conjugation transport on rays gives a sign
alternative for any normalizer element. In the negative case the local
rank-one Gauss identity supplies a positive-ray, torus, opposite-ray product.
This proves two-cell exchange while retaining all factors in any subgroup
containing the rays and the marked lifts. Opposite-ray separation proves
the nontriviality witness.

These are conditional group-theoretic deductions from local identities.
The fixed-point application in the parent module ties the ray carriers and
lifts to their literal algebraic intersections and defining residual. No
commutativity inside a ray, additive parametrization, or reduced
crystallographic relative root system is used.

Sources: GLS3 2.3.7--2.3.8, the rank-one relations of §2.4, and
Chapter 1, Definition 1.11.1(d).
-/

@[expose] public section
namespace Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.RelativeExchange

variable {G R I : Type*} [Group G]

/-- Local relations on whole relative rays. Conjugation is left conjugation;
the sign used for exchange is consequently the action of `n⁻¹`. -/
structure RayRelations (B H N : Subgroup G) (X : R → Subgroup G)
    (simple : I → R) (lift : I → N) where
  positive : Set R
  opposite : R → R
  sign : ∀ α, α ∈ positive ∨ opposite α ∈ positive
  action : N →* Equiv.Perm R
  action_opposite : ∀ n α, action n (opposite α) = opposite (action n α)
  transport : ∀ (n : N) α x, x ∈ X α →
    (n : G) * x * (n : G)⁻¹ ∈ X (action n α)
  reflection : I → Equiv.Perm R
  lift_action : ∀ i, action (lift i) = reflection i
  simple_positive : ∀ i, simple i ∈ positive
  reflection_simple : ∀ i, reflection i (simple i) = opposite (simple i)
  reflection_other : ∀ i α, α ∈ positive → α ≠ simple i →
    reflection i α ∈ positive
  positive_le : ∀ α, α ∈ positive → X α ≤ B
  torus_le : H ≤ B
  torus_transport : ∀ (n : N) t, t ∈ H → (n : G) * t * (n : G)⁻¹ ∈ H
  orderBefore : I → List R
  orderBefore_positive : ∀ i α, α ∈ orderBefore i → α ∈ positive
  orderBefore_ne : ∀ i α, α ∈ orderBefore i → α ≠ simple i
  /-- Ordered coordinates of 2.3.7, together with the torus factor. Only
  one order with the marked ray last is needed for each simple lift. -/
  coordinates : ∀ i b, b ∈ B → ∃ t ∈ H, ∃ f : R → G,
    (∀ α, f α ∈ X α) ∧ b = t * ((orderBefore i ++ [simple i]).map f).prod
  /-- The local Gauss multiplication identity on the entire nonidentity
  ray. For a nonabelian ray the parameters and products remain those of
  that ray; this field does not replace them by additive parameters. -/
  rank_one : ∀ i x, x ∈ X (simple i) → x ≠ 1 →
    ∃ u ∈ X (simple i), ∃ t ∈ H, ∃ v ∈ X (opposite (simple i)),
      (lift i : G) * x = u * t * v
  ray_nontrivial : ∀ i, ∃ x ∈ X (simple i), x ≠ 1
  /-- Local positive/opposite separation, before conjugation by a lift. -/
  opposite_disjoint : ∀ i, Disjoint (X (opposite (simple i))) B

namespace RayRelations
variable {B H N : Subgroup G} {X : R → Subgroup G}
  {simple : I → R} {lift : I → N}
  (D : RayRelations B H N X simple lift)

include D

/-- Collect the marked ray last, and conjugate every remaining ray separately.
No factors within a ray are commuted. -/
theorem collect (i : I) {b : G} (hb : b ∈ B) :
    ∃ b₀ ∈ B, ∃ x ∈ X (simple i), b = b₀ * x ∧
      (lift i : G) * b₀ * (lift i : G)⁻¹ ∈ B := by
  obtain ⟨t, ht, f, hf, he⟩ := D.coordinates i b hb
  let q := ((D.orderBefore i).map f).prod
  have hq : q ∈ B := by
    apply list_prod_mem
    intro x hx
    obtain ⟨α, hα, rfl⟩ := List.mem_map.mp hx
    exact D.positive_le α (D.orderBefore_positive i α hα) (hf α)
  have hsq : (lift i : G) * q * (lift i : G)⁻¹ ∈ B := by
    change (MulAut.conj (lift i : G)).toMonoidHom q ∈ B
    dsimp only [q]
    rw [MonoidHom.map_list_prod]
    apply list_prod_mem
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨α, hα, rfl⟩ := List.mem_map.mp hy
    change (lift i : G) * f α * (lift i : G)⁻¹ ∈ B
    apply D.positive_le (D.reflection i α)
      (D.reflection_other i α (D.orderBefore_positive i α hα) (D.orderBefore_ne i α hα))
    simpa only [D.lift_action] using D.transport (lift i) α (f α) (hf α)
  refine ⟨t * q, B.mul_mem (D.torus_le ht) hq, f (simple i), hf _, ?_, ?_⟩
  · simpa only [List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton, mul_assoc] using he
  · have hprod : (lift i : G) * (t * q) * (lift i : G)⁻¹ =
        ((lift i : G) * t * (lift i : G)⁻¹) *
          ((lift i : G) * q * (lift i : G)⁻¹) := by group
    rw [hprod]
    exact B.mul_mem (D.torus_le (D.torus_transport (lift i) t ht)) hsq

/-- The normalizer sends either the marked ray or its opposite into the
positive rays. This is derived from its actual ray action. -/
theorem transport_sign (i : I) (n : N) :
    (∀ x ∈ X (simple i), (n : G)⁻¹ * x * n ∈ B) ∨
      (∀ x ∈ X (D.opposite (simple i)), (n : G)⁻¹ * x * n ∈ B) := by
  rcases D.sign (D.action n⁻¹ (simple i)) with hp | hp
  · left
    intro x hx
    exact D.positive_le _ hp (by
      simpa only [Subgroup.coe_inv, inv_inv] using D.transport n⁻¹ (simple i) x hx)
  · right
    intro x hx
    rw [← D.action_opposite n⁻¹ (simple i)] at hp
    exact D.positive_le _ hp (by
      simpa only [Subgroup.coe_inv, inv_inv] using
        D.transport n⁻¹ (D.opposite (simple i)) x hx)

/-- Exchange with all factors retained in a specified overgroup of the rays
and marked lifts. The torus factor in the rank-one identity is forced into
that overgroup by the identity itself. -/
theorem exchange_factors (L : Subgroup G) (hXL : ∀ α, X α ≤ L)
    (hlift : ∀ i, (lift i : G) ∈ L) (i : I)
    {b n : G} (hb : b ∈ B) (hbL : b ∈ L) (hn : n ∈ N) (hnL : n ∈ L) :
    ∃ a c : G, a ∈ B ∧ a ∈ L ∧ c ∈ B ∧ c ∈ L ∧
      ((lift i : G) * b * n = a * ((lift i : G) * n) * c ∨
        (lift i : G) * b * n = a * n * c) := by
  obtain ⟨b₀, _hb₀, x, hx, he, hs⟩ := D.collect i hb
  have hxL : x ∈ L := hXL _ hx
  have hb₀L : b₀ ∈ L := by
    have he' : b₀ = b * x⁻¹ := by rw [he]; group
    rw [he']
    exact L.mul_mem hbL (L.inv_mem hxL)
  let a₀ := (lift i : G) * b₀ * (lift i : G)⁻¹
  have ha₀L : a₀ ∈ L := L.mul_mem (L.mul_mem (hlift i) hb₀L) (L.inv_mem (hlift i))
  have hre : (lift i : G) * b * n = a₀ * ((lift i : G) * x * n) := by
    rw [he]
    dsimp [a₀]
    group
  rw [hre]
  by_cases hx1 : x = 1
  · refine ⟨a₀, 1, hs, ha₀L, B.one_mem, L.one_mem, Or.inl ?_⟩
    simp only [hx1, mul_one]
  · rcases D.transport_sign i ⟨n, hn⟩ with hp | hm
    · refine ⟨a₀, n⁻¹ * x * n, hs, ha₀L, hp x hx,
        L.mul_mem (L.mul_mem (L.inv_mem hnL) hxL) hnL, Or.inl ?_⟩
      group
    · obtain ⟨u, hu, t, ht, v, hv, hrel⟩ := D.rank_one i x hx hx1
      have huL : u ∈ L := hXL _ hu
      have hvL : v ∈ L := hXL _ hv
      have htL : t ∈ L := by
        have ht' : t = u⁻¹ * ((lift i : G) * x) * v⁻¹ := by rw [hrel]; group
        rw [ht']
        exact L.mul_mem (L.mul_mem (L.inv_mem huL) (L.mul_mem (hlift i) hxL))
          (L.inv_mem hvL)
      refine ⟨a₀ * (u * t), n⁻¹ * v * n,
        B.mul_mem hs (B.mul_mem (D.positive_le _ (D.simple_positive i) hu)
          (D.torus_le ht)), L.mul_mem ha₀L (L.mul_mem huL htL), hm v hv,
        L.mul_mem (L.mul_mem (L.inv_mem hnL) hvL) hnL, Or.inr ?_⟩
      rw [hrel]
      group

/-- The exact local exchange interface consumed by Bruhat generation, in
the literal intersections with an intermediate subgroup. -/
theorem simpleLiftExchange (L : Subgroup G) (hXL : ∀ α, X α ≤ L)
    (hlift : ∀ i, (lift i : G) ∈ L) :
    BruhatGeneration.SimpleLiftExchange (B.subgroupOf L) (N.subgroupOf L)
      (Set.range fun i => (⟨(lift i : G), hlift i⟩ : L)) := by
  rintro _ ⟨i, rfl⟩ b hb n hn
  obtain ⟨a, c, ha, haL, hc, hcL, he⟩ :=
    D.exchange_factors L hXL hlift i hb b.property hn n.property
  refine ⟨⟨a, haL⟩, ⟨c, hcL⟩, ha, hc, ?_⟩
  rcases he with he | he
  · exact Or.inl (Subtype.ext he)
  · exact Or.inr (Subtype.ext he)

/-- A nonidentity element of the marked ray is carried into the opposite
ray, whose intersection with the Borel is trivial. -/
theorem nontriviality (L : Subgroup G) (hXL : ∀ α, X α ≤ L)
    (hlift : ∀ i, (lift i : G) ∈ L) (i : I) :
    ∃ b ∈ B.subgroupOf L,
      (⟨(lift i : G), hlift i⟩ : L) * b * (⟨(lift i : G), hlift i⟩ : L)⁻¹ ∉
        B.subgroupOf L := by
  obtain ⟨x, hx, hx1⟩ := D.ray_nontrivial i
  refine ⟨⟨x, hXL _ hx⟩, D.positive_le _ (D.simple_positive i) hx, ?_⟩
  intro hc
  have hneg : (lift i : G) * x * (lift i : G)⁻¹ ∈ X (D.opposite (simple i)) := by
    simpa only [D.lift_action, D.reflection_simple] using D.transport (lift i) _ x hx
  have he : (lift i : G) * x * (lift i : G)⁻¹ = 1 :=
    disjoint_iff_inf_le.mp (D.opposite_disjoint i) ⟨hneg, hc⟩
  apply hx1
  have := congrArg (fun z => (lift i : G)⁻¹ * z * (lift i : G)) he
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, mul_one,
    inv_mul_cancel] using this

end RayRelations
end Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.RelativeExchange
end
