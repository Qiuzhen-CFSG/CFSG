module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Localization
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.LocalCounts.Commuting
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.LocalCounts.Inverting

/-!
# Local odd-prime centralizer orders and involution counts

The centralizer decomposition in Bender (4.1) gives one common parameter
`d = 1` or `d = 3`. Sylow conjugacy and the common-centralizer orders in
the actual `A₅ × C₂` model then give both ambient commuting-involution
counts in (4.2).

The normalizer argument in `LocalCounts.Inverting` supplies the ambient
inversion count. Combining these results constructs `LocalBenderPrimeData`
from the structural assertion (4.1), with no numerical premise. The source
assembly remains responsible for establishing that structural assertion.

Source: Bender, *Finite groups with large subgroups* (1974), §4, printed
pp.225–226, (4.1)–(4.2).
-/

open Subgroup

namespace CFSG.Quasithin.Janko1CentralizerData

variable {G : Type*} [Group G] [Finite G]
    (h : Janko1CentralizerData G) (s : OddPrimeCentralizerStructure h)

include s

/-- A common parameter controls both ambient centralizer orders and both
ambient commuting-involution counts. No inversion count is assumed here. -/
public theorem exists_local_centralizer_and_commuting_counts_of_structure :
    ∃ d : ℕ, (d = 1 ∨ d = 3) ∧
      (∀ x : G, x ∈ centralizer ({h.z} : Set G) → orderOf x = 3 →
        Nat.card (centralizer ({x} : Set G)) = if d = 1 then 6 else 30) ∧
      (∀ x : G, x ∈ centralizer ({h.z} : Set G) → orderOf x = 5 →
        Nat.card (centralizer ({x} : Set G)) = 10 * d) ∧
      (∀ x : G, x ∈ centralizer ({h.z} : Set G) → orderOf x = 3 →
        Nat.card {t : G // orderOf t = 2 ∧ Commute t x} = 2 * d - 1) ∧
      (∀ x : G, x ∈ centralizer ({h.z} : Set G) → orderOf x = 5 →
        Nat.card {t : G // orderOf t = 2 ∧ Commute t x} = d) := by
  obtain ⟨d, hd, h3, h5⟩ := h.exists_uniform_odd_centralizer_orders_of_structure s
  refine ⟨d, hd, (fun x _ hx => h3 x hx), (fun x _ hx => h5 x hx), ?_, ?_⟩
  · intro x hxC hx
    have hc := h.commuting_prime_count_mul_of_structure s 3 (Or.inl rfl) x hxC hx
    rw [h3 x hx] at hc
    rcases hd with rfl | rfl <;> norm_num at hc ⊢ <;> omega
  · intro x hxC hx
    have hc := h.commuting_prime_count_mul_of_structure s 5 (Or.inr rfl) x hxC hx
    rw [h5 x hx] at hc
    omega

/-- Assembly with the remaining inversion assertion explicit. The source
normalizer argument must discharge `hI` before removing it from the statement. -/
public theorem exists_localBenderPrimeData_of_structure_of_inverting_count
    (hI : ∀ x : G, x ∈ centralizer ({h.z} : Set G) → orderOf x = 3 →
      Nat.card {t : G // orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹} =
        if Nat.card (centralizer ({x} : Set G)) = 6 then 6 else 18) :
    ∃ d : ℕ, LocalBenderPrimeData h d := by
  obtain ⟨d, hd, h3, h5, hc3, hc5⟩ :=
    h.exists_local_centralizer_and_commuting_counts_of_structure s
  refine ⟨d, hd, h3, h5, ?_, hc3, hc5⟩
  intro x hxC hx
  rw [hI x hxC hx, h3 x hxC hx]
  rcases hd with rfl | rfl <;> norm_num

/-- The structural assertion (4.1) gives one common parameter for both
centralizer orders and all three ambient involution counts in (4.2). -/
public theorem exists_localBenderPrimeData_of_structure :
    ∃ d : ℕ, LocalBenderPrimeData h d :=
  h.exists_localBenderPrimeData_of_structure_of_inverting_count s
    (h.inverting_three_count_of_structure s)

end CFSG.Quasithin.Janko1CentralizerData
