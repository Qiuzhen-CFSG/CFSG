module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Bookkeeping

/-!
# The structural interface for Bender's normalizer count

This interface separates the subgroup geometry of `H = N_G(Q)` from the
ambient inversion-incidence calculation. It specifies literal subgroups
and literal inversion equations. Its existence remains a separate proof
obligation; none of its fields asserts a coset distribution.

The inversion-set field gives the preliminary fiber sizes, including two.
The incidence calculation subsequently excludes size two.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, printed pp.226–227, the distribution following (4.3).
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

/-- The subgroups of a specified order inside the literal `H`. -/
@[expose] public def BenderSubgroupsOfOrder {G : Type*} [Group G]
    (H : Subgroup G) (n : ℕ) := {S : Subgroup G // S ≤ H ∧ Nat.card S = n}

/-- The normalizer subgroup geometry used to count inversion incidences.
This record is only an interface; constructing it from the source hypotheses
is the responsibility of the structural branch. -/
public structure BenderNormalizerGeometry {G : Type*} [Group G] [Finite G]
    (h : Janko1CentralizerData G) : Prop where
  inverted_subgroup : ∀ u : G, orderOf u = 2 → u ∉ normalizer (h.sylow : Set G) →
    ∃ K : Subgroup G,
      (∀ a : G, a ∈ K ↔ a ∈ normalizer (h.sylow : Set G) ∧ u * a * u⁻¹ = a⁻¹) ∧
      (Nat.card K = 1 ∨ Nat.card K = 2 ∨ Nat.card K = 3 ∨
        Nat.card K = 6 ∨ Nat.card K = 7)
  three_subgroups : Nat.card (BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 3) = 28
  six_subgroups : Nat.card (BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 6) = 28
  seven_subgroups : Nat.card (BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 7) = 8
  six_cyclic : ∀ S : Subgroup G, S ≤ normalizer (h.sylow : Set G) →
    Nat.card S = 6 → IsCyclic S
  three_centralizer : ∀ X : Subgroup G, X ≤ normalizer (h.sylow : Set G) →
    Nat.card X = 3 →
      Nat.card (normalizer (h.sylow : Set G) ⊓ centralizer (X : Set G) : Subgroup G) = 6
  three_normalizes_seven : ∀ X : Subgroup G, X ≤ normalizer (h.sylow : Set G) →
    Nat.card X = 3 →
      Nat.card {S : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 7 //
        X ≤ normalizer (S.1 : Set G)} = 2

/-- The preliminary list of actual non-base fiber sizes, before size two is excluded. -/
public theorem BenderNormalizerGeometry.fiber_sizes_with_two
    {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G}
    (geometry : BenderNormalizerGeometry h)
    (ω : G ⧸ normalizer (h.sylow : Set G))
    (hω : ω ≠ benderBaseCoset (normalizer (h.sylow : Set G))) :
    Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 0 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 1 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 2 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 3 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 6 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 7 := by
  let H := normalizer (h.sylow : Set G)
  by_cases hc : Nat.card (BenderFiber H ω) = 0
  · exact Or.inl hc
  obtain ⟨⟨u, hu, huω⟩⟩ := (Nat.card_ne_zero.mp hc).1
  have huH : u ∉ H := by
    intro huH
    exact hω (huω.symm.trans ((benderRightCoset_eq_base_iff H u).mpr huH))
  obtain ⟨K, hK, hcard⟩ := geometry.inverted_subgroup u hu huH
  have he := bender_fiber_card_of_inverted_subgroup H u hu huH K hK
  rw [huω] at he
  exact Or.inr (he.symm ▸ hcard)

end CFSG.Quasithin.Janko1CentralizerData
