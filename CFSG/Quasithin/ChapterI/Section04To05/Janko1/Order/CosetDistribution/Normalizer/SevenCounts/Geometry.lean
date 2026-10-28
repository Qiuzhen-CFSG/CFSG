module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Geometry

/-!
# The remaining geometry for the seven-normalizer count

The interface below concerns the actual normalizer `H = N_G(C_G(S))`.
An external involution's inverted elements must form a cyclic subgroup
of order dividing six. The subgroups of orders three and six, and the
centralizers of the former inside H, supply the incidence calculation.

This is a contract for the remaining geometry, not an assertion of its
existence. Its fiber-size consequence uses the literal multiplication
bijection for Bender's right-coset convention.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), proof of (4.3), printed p.226.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

/-- Subgroup geometry in the contrary seven-centralizer normalizer.
No field asserts the external involution incidences or coset counts. -/
public structure BenderSevenGeometry {G : Type*} [Group G] (S : Subgroup G) : Prop where
  inverted_subgroup : ∀ u : G, orderOf u = 2 →
    u ∉ normalizer (centralizer (S : Set G) : Set G) →
    ∃ K : Subgroup G,
      (∀ a : G, a ∈ K ↔ a ∈ normalizer (centralizer (S : Set G) : Set G) ∧
        u * a * u⁻¹ = a⁻¹) ∧ IsCyclic K ∧ Nat.card K ∣ 6
  three_subgroups :
    Nat.card (BenderSubgroupsOfOrder (normalizer (centralizer (S : Set G) : Set G)) 3) =
      Nat.card (centralizer (S : Set G))
  six_subgroups :
    Nat.card (BenderSubgroupsOfOrder (normalizer (centralizer (S : Set G) : Set G)) 6) =
      Nat.card (centralizer (S : Set G))
  six_cyclic : ∀ K : Subgroup G,
    K ≤ normalizer (centralizer (S : Set G) : Set G) → Nat.card K = 6 → IsCyclic K
  three_centralizer : ∀ X : Subgroup G,
    X ≤ normalizer (centralizer (S : Set G) : Set G) → Nat.card X = 3 →
    Nat.card (normalizer (centralizer (S : Set G) : Set G) ⊓
      centralizer (X : Set G) : Subgroup G) = 6

/-- The geometric description restricts the actual non-base fibers to
sizes zero, one, two, three and six. -/
public theorem BenderSevenGeometry.fiber_sizes
    {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (geometry : BenderSevenGeometry S)
    (ω : G ⧸ normalizer (centralizer (S : Set G) : Set G))
    (hω : ω ≠ benderBaseCoset (normalizer (centralizer (S : Set G) : Set G))) :
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 0 ∨
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 1 ∨
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 2 ∨
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 3 ∨
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 6 := by
  let H := normalizer (centralizer (S : Set G) : Set G)
  by_cases hc : Nat.card (BenderFiber H ω) = 0
  · exact Or.inl hc
  obtain ⟨⟨u, hu, huω⟩⟩ := (Nat.card_ne_zero.mp hc).1
  have huH : u ∉ H := by
    intro huH
    exact hω (huω.symm.trans ((benderRightCoset_eq_base_iff H u).mpr huH))
  obtain ⟨K, hK, _, hdiv⟩ := geometry.inverted_subgroup u hu huH
  have hcard := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
  have hdivisors : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide
  rw [hdivisors] at hcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcard
  have he := bender_fiber_card_of_inverted_subgroup H u hu huH K hK
  rw [huω] at he
  exact Or.inr (he.symm ▸ hcard)

end CFSG.Quasithin.Janko1CentralizerData
