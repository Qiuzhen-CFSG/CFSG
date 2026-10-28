module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CountingData
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Local contracts for Bender's odd-prime argument

The structural input is the internal semidirect product in Bender (4.1):
for an odd prime-order element in the distinguished involution centralizer,
its full ambient centralizer is a cyclic odd subgroup extended by `⟨z⟩`.
Normalization is relative to this centralizer, not normality in `G`.

`LocalBenderPrimeData` restricts only the elements of orders three and five
to `C_G(z)`. Its involution counts still range over the whole ambient group.
The localization theorem in `OddPrimeCentralizers` removes this restriction
and derives both Sylow orders. Neither of the records below is asserted to
exist here: the centralizer-structure and numerical source arguments must
construct them.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, printed pp.225–226, (4.1)–(4.2); Z. Janko, J. Algebra 3
(1966), Lemma 3.1, for the structural alternatives before the exceptional
elementary abelian order-27 case is excluded.
-/

namespace CFSG.Quasithin.Janko1CentralizerData

variable {G : Type*} [Group G] [Finite G]

/-- The internal semidirect-product conclusion of Bender (4.1).
The odd complement is normal in the displayed centralizer because it is
normalized by `⟨z⟩` and together they generate that centralizer. -/
public structure OddPrimeCentralizerStructure (h : Janko1CentralizerData G) : Prop where
  decomposition : ∀ (p : ℕ), p = 3 ∨ p = 5 → ∀ x : G,
    x ∈ Subgroup.centralizer ({h.z} : Set G) → orderOf x = p →
    ∃ A : Subgroup G, IsCyclic A ∧ (Nat.card A = p ∨ Nat.card A = 15) ∧
      Subgroup.zpowers h.z ≤ Subgroup.normalizer (A : Set G) ∧
      Disjoint A (Subgroup.zpowers h.z) ∧
      A ⊔ Subgroup.zpowers h.z = Subgroup.centralizer ({x} : Set G)

/-- The numerical statements of (4.1)–(4.2) for elements in `C_G(z)`.
All three sets of counted involutions are subsets of the ambient `G`. -/
public structure LocalBenderPrimeData (h : Janko1CentralizerData G) (d : ℕ) : Prop where
  d_cases : d = 1 ∨ d = 3
  centralizer_three : ∀ x : G, x ∈ Subgroup.centralizer ({h.z} : Set G) →
    orderOf x = 3 →
    Nat.card (Subgroup.centralizer ({x} : Set G)) = if d = 1 then 6 else 30
  centralizer_five : ∀ x : G, x ∈ Subgroup.centralizer ({h.z} : Set G) →
    orderOf x = 5 → Nat.card (Subgroup.centralizer ({x} : Set G)) = 10 * d
  inverting_three : ∀ x : G, x ∈ Subgroup.centralizer ({h.z} : Set G) →
    orderOf x = 3 →
    Nat.card {t : G // orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹} = 6 * d
  commuting_three : ∀ x : G, x ∈ Subgroup.centralizer ({h.z} : Set G) →
    orderOf x = 3 →
    Nat.card {t : G // orderOf t = 2 ∧ Commute t x} = 2 * d - 1
  commuting_five : ∀ x : G, x ∈ Subgroup.centralizer ({h.z} : Set G) →
    orderOf x = 5 → Nat.card {t : G // orderOf t = 2 ∧ Commute t x} = d

/-- The structural semidirect product has order `2p` or `30`.
This is the numerical input to the Sylow-order argument. -/
public theorem OddPrimeCentralizerStructure.centralizer_card_cases
    {h : Janko1CentralizerData G} (s : OddPrimeCentralizerStructure h)
    (p : ℕ) (hp : p = 3 ∨ p = 5) (x : G)
    (hxC : x ∈ Subgroup.centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = 2 * p ∨
      Nat.card (Subgroup.centralizer ({x} : Set G)) = 30 := by
  obtain ⟨A, _, hA, hn, hd, hsup⟩ := s.decomposition p hp x hxC hx
  have hc := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes A
    (Subgroup.zpowers h.z) hn
  rw [hd.eq_bot, Subgroup.card_bot, one_mul, hsup,
    Nat.card_zpowers, h.involution] at hc
  rcases hA with hA | hA
  · left
    rw [← hc, hA, Nat.mul_comm]
  · right
    rw [← hc, hA]

end CFSG.Quasithin.Janko1CentralizerData
