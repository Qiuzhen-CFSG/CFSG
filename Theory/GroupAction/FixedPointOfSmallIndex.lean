module

public import Mathlib.GroupTheory.Index
public import Mathlib.Order.Atoms.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Fixed points from divisibility of small subgroup indices

Let a finite group act on a finite set X. If every proper subgroup of index
at most |X| has index divisible by d, but d does not divide |X|, the action
has a fixed point. Otherwise every orbit has size divisible by d, and the
orbit decomposition would make |X| divisible by d as well.

It suffices to check maximal proper subgroups: a point stabilizer lies in
one, and its index is a multiple of the maximal subgroup's index. This
elementary orbit-counting argument is used for the degree-100 action in
GLS3, Table 5.3m, printed p.274, with d = 11. The required subgroup-index
information is a separate model calculation.
-/

public section
namespace MulAction
open Subgroup

variable {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]

/-- Divisibility of all proper small indices forces a global fixed point. -/
theorem exists_fixedPoint_of_smallIndex_dvd {d : ℕ}
    (hindex : ∀ K : Subgroup G, K ≠ ⊤ → K.index ≤ Nat.card X → d ∣ K.index)
    (hcard : ¬ d ∣ Nat.card X) : ∃ x : X, ∀ g : G, g • x = x := by
  classical
  by_contra hfixed
  have hproper (x : X) : stabilizer G x ≠ ⊤ := by
    intro heq
    apply hfixed
    exact ⟨x, fun g => mem_stabilizer_iff.mp (heq ▸ mem_top g)⟩
  let := Fintype.ofFinite (Quotient (orbitRel G X))
  apply hcard
  rw [Nat.card_congr (selfEquivSigmaOrbitsQuotientStabilizer G X), Nat.card_sigma]
  apply Finset.dvd_sum
  intro ω _
  change d ∣ (stabilizer G ω.out).index
  apply hindex _ (hproper _)
  rw [index_stabilizer]
  exact (Set.ncard_le_ncard (Set.subset_univ _)).trans_eq (Set.ncard_univ X)

/-- Only maximal proper subgroups need to be checked in the fixed-point criterion. -/
theorem exists_fixedPoint_of_smallMaximalIndex_dvd {d : ℕ}
    (hindex : ∀ K : Subgroup G, IsCoatom K → K.index ≤ Nat.card X → d ∣ K.index)
    (hcard : ¬ d ∣ Nat.card X) : ∃ x : X, ∀ g : G, g • x = x := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
  apply exists_fixedPoint_of_smallIndex_dvd (hcard := hcard)
  intro K hK hbound
  obtain ⟨M, hM, hKM⟩ := (eq_top_or_exists_le_coatom K).resolve_left hK
  exact (hindex M hM ((index_antitone hKM).trans hbound)).trans (index_dvd_of_le hKM)

end MulAction
