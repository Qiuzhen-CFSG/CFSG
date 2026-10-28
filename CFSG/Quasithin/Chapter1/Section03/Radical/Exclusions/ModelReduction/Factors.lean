module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockContract
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The order of the odd factors in the swapped alternative

The direct product P = (P ∩ K)(P ∩ K)^t in 1.3.4(1) has order p².
The factors are conjugate and disjoint, so each has order p. This statement
uses the actual intersections and conjugation, independently of any block
recognition. It supplies the odd subgroup for the small-model exclusions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Proposition 1.3.4(1), p.509, and the proof of 1.3.8, p.514.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open XiEmbedding
variable {G : Type*} [Group G] [Finite G]

/-- The two conjugate factors of the plane each have order p. -/
theorem swapped_intersection_card {p : ℕ} {T P K : Subgroup G}
    (hplane : Nonempty (P ≃* Plane p)) (hswap : SwappedFactors T P K) :
    Nat.card (P ⊓ K : Subgroup G) = p := by
  obtain ⟨t, _, _, hgen, hd, hc⟩ := hswap.2
  have hn : (P ⊓ K).conjBy t ≤ normalizer (P ⊓ K : Subgroup G) :=
    (commutator_eq_bot_iff_le_centralizer.mp
      ((commutator_comm ((P ⊓ K).conjBy t) (P ⊓ K)).trans hc)).trans
      (Subgroup.centralizer_le_normalizer _)
  have he := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (P ⊓ K) ((P ⊓ K).conjBy t) hn
  have ht : Nat.card ((P ⊓ K).conjBy t) = Nat.card (P ⊓ K : Subgroup G) :=
    card_map_of_injective (MulAut.conj t).injective
  have hp : Nat.card P = p ^ 2 :=
    (Nat.card_congr hplane.some.toEquiv).trans (plane_card p)
  rw [ht, hd.eq_bot, Subgroup.card_bot,
    one_mul, ← hgen, hp] at he
  nlinarith

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
