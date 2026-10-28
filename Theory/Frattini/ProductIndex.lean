module
public import Theory.Frattini.OmegaProducts

/-!
# Frattini index of an ordered product

If a finite two-group is an ordered product of two subgroups, its Frattini
index is at most the product of their Frattini indices. Inclusion maps induce
maps on Frattini quotients, and ordered multiplication is surjective on the
ambient quotient. The factors need not commute or be normal.

The ambient-subgroup form is used for C(T) intersect U_s2 in Fong--Seitz I
(6C), printed p.40, with factors U2^(s1) and U2^(s1 s2).
-/

public noncomputable section
open scoped Pointwise
namespace Subgroup

/-- An ordered product of two finite two-subgroups generates at most the sum
of their Frattini ranks. The factors need not commute. -/
theorem frattini_index_le_product {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (A B : Subgroup G)
    (hprod : (A : Set G) * (B : Set G) = Set.univ) :
    Nat.card (G ⧸ frattini G) ≤
      Nat.card (A ⧸ frattini A) * Nat.card (B ⧸ frattini B) := by
  let : Fact (IsPGroup 2 G) := ⟨hG⟩
  let : Fact (IsPGroup 2 A) := ⟨hG.to_subgroup A⟩
  let : Fact (IsPGroup 2 B) := ⟨hG.to_subgroup B⟩
  let q := QuotientGroup.mk' (frattini G)
  have hker (D : Subgroup G) (hD : IsPGroup 2 D) :
      frattini D ≤ (q.comp D.subtype).ker := by
    let : Fact (IsPGroup 2 D) := ⟨hD⟩
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mpr
    exact frattini_map_le_of_isPGroup (p := 2) D.subtype (mem_map_of_mem _ hx)
  let fA := QuotientGroup.lift (frattini A) (q.comp A.subtype) (hker A (hG.to_subgroup A))
  let fB := QuotientGroup.lift (frattini B) (q.comp B.subtype) (hker B (hG.to_subgroup B))
  have hs : Function.Surjective (fun z : (A ⧸ frattini A) × (B ⧸ frattini B) => fA z.1 * fB z.2) := by
    intro z
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (frattini G) z
    have hg : g ∈ (A : Set G) * (B : Set G) := hprod.symm ▸ Set.mem_univ g
    obtain ⟨a,ha,b,hb,rfl⟩ := hg
    refine ⟨(QuotientGroup.mk' (frattini A) ⟨a,ha⟩,
      QuotientGroup.mk' (frattini B) ⟨b,hb⟩), ?_⟩
    exact (map_mul q a b).symm
  simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective _ hs

/-- Apply the two-factor Frattini bound to subgroups in their actual ambient
product; no direct-product or commutativity premise is needed. -/
theorem frattini_index_le_ambient_product {Y : Type*} [Group Y] [Finite Y]
    (A B C : Subgroup Y) (hC : IsPGroup 2 C)
    (hA : A ≤ C) (hB : B ≤ C)
    (hprod : (C : Set Y) = (A : Set Y) * (B : Set Y)) :
    Nat.card (C ⧸ frattini C) ≤
      Nat.card (A ⧸ frattini A) * Nat.card (B ⧸ frattini B) := by
  have hp : (A.subgroupOf C : Set C) * (B.subgroupOf C : Set C) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : (x : Y) ∈ (A : Set Y) * (B : Set Y) := hprod ▸ x.property
    obtain ⟨a,ha,b,hb,he⟩ := hx
    exact ⟨⟨a,hA ha⟩,ha,⟨b,hB hb⟩,hb,Subtype.ext he⟩
  have hh := frattini_index_le_product hC (A.subgroupOf C) (B.subgroupOf C) hp
  have he (D : Subgroup Y) (hD : D ≤ C) :
      Nat.card (D.subgroupOf C ⧸ frattini (D.subgroupOf C)) = Nat.card (D ⧸ frattini D) :=
    Nat.card_congr (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hD)
      (frattini_map_equiv _)).toEquiv
  rwa [he A hA,he B hB] at hh

end Subgroup
