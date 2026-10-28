module
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PrimeRankHom

/-!
# Two-rank of central covers whose involutions lift

If an elementary central kernel has order 2ⁿ and every involution of the
quotient has an involutory lift, then the two-rank of the cover is the
quotient two-rank plus n. Every element of the preimage of an elementary
subgroup squares to one: it is an involutory lift times an element of the
elementary central kernel. Cardinality gives the lower bound, and the
rank bound for a homomorphism gives the reverse inequality.

The model-specific lifting hypothesis is explicit. The application is the
permitted PSL₃(4) covers in Aschbacher–Smith, 16.3.9, combined manuscript
of 1 March 2004, printed p.1180. This does not assert that arbitrary central
covers have involutory lifts.
-/

public section

open Subgroup

private theorem binary_elementary_of_square {A : Type*} [Group A]
    (h : ∀ a : A, a ^ 2 = 1) : IsElementaryAbelian 2 A := by
  exact { toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
    (fun x => orderOf_dvd_of_pow_eq_one (h x)) a b).eq⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr h }

/-- Elementary quotient subgroups have elementary full preimages under the
stated central-kernel and involution-lifting hypotheses. -/
theorem IsElementaryAbelian.comap_quotient_of_central_involution_lifts
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : N ≤ center G) [IsElementaryAbelian 2 N]
    (E : Subgroup (G ⧸ N)) [IsElementaryAbelian 2 E]
    (hlift : ∀ x ∈ E, x ^ 2 = 1 → ∃ y : G, QuotientGroup.mk' N y = x ∧ y ^ 2 = 1) :
    IsElementaryAbelian 2 (E.comap (QuotientGroup.mk' N)) := by
  apply binary_elementary_of_square
  intro x
  have hq : (QuotientGroup.mk' N (x : G)) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian _ x.property
  obtain ⟨y, hy, hy2⟩ := hlift _ x.property hq
  have hn : (x : G) * y⁻¹ ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N ((x : G) * y⁻¹) = 1
    rw [map_mul, map_inv, hy, mul_inv_cancel]
  have hn2 : ((x : G) * y⁻¹) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian _ hn
  have hc : Commute ((x : G) * y⁻¹) y :=
    (mem_center_iff.mp (hN hn) y).symm
  apply Subtype.ext
  change (x : G) ^ 2 = 1
  have hp := hc.mul_pow 2
  rw [inv_mul_cancel_right, hn2, hy2, mul_one] at hp
  exact hp

private theorem card_comap_quotient
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (E : Subgroup (G ⧸ N)) :
    Nat.card (E.comap (QuotientGroup.mk' N)) = Nat.card E * Nat.card N := by
  let q := QuotientGroup.mk' N
  let P := E.comap q
  let f : P →* E := q.restrict (fun _ hx => hx)
  have hf : Function.Surjective f := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N e
    exact ⟨⟨x, by change q x ∈ E; rw [hx]; exact e.property⟩, Subtype.ext hx⟩
  have hNP : N ≤ P := by
    intro x hx
    change q x ∈ E
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact E.one_mem
  have hker : f.ker = N.subgroupOf P := by
    ext x
    change (⟨q x, x.property⟩ : E) = 1 ↔ (x : G) ∈ N
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  have hc : Nat.card f.ker = Nat.card N := by
    rw [hker]
    exact Nat.card_congr (subgroupOfEquivOfLe hNP).toEquiv
  have hi : f.ker.index = Nat.card E := by
    rw [index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  rw [← f.ker.index_mul_card, hi, hc]

/-- An elementary abelian subgroup attains the prime rank of a finite group. -/
theorem exists_elementaryAbelian_card_primeRank {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] :
    ∃ E : Subgroup G, IsElementaryAbelian p E ∧ Nat.card E = p ^ primeRank p G := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  by_cases hr : primeRank p G = 0
  · refine ⟨⊥, ?_, ?_⟩
    · exact { toIsMulCommutative := inferInstance
              exponent_dvd_p := by simp }
    · simp [hr]
  · have hn : ¬ primeRank p G ≤ primeRank p G - 1 := by omega
    rw [primeRank_le_iff_elementary_card_le G] at hn
    push Not at hn
    obtain ⟨E, hE, hEc⟩ := hn
    let := hE
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p E).exists_card_eq
    have hu := (primeRank_le_iff_elementary_card_le G).mp le_rfl E hE
    rw [hn] at hEc hu
    have hnl := (Nat.pow_lt_pow_iff_right hp).mp hEc
    have hnu := (Nat.pow_le_pow_iff_right hp).mp hu
    have he : n = primeRank p G := by omega
    exact ⟨E, hE, by simpa only [he] using hn⟩

/-- Lifting just one elementary quotient subgroup gives a rank lower bound.
Only its involutions need lift: this also applies to a long-root plane in a
cover where other involution classes lift to elements of order four. -/
theorem primeRank_ge_of_central_elementary_lifts
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N ≤ center G) [IsElementaryAbelian 2 N]
    (E : Subgroup (G ⧸ N)) [IsElementaryAbelian 2 E] {m n : ℕ}
    (hE : Nat.card E = 2 ^ m) (hcard : Nat.card N = 2 ^ n)
    (hlift : ∀ x ∈ E, x ^ 2 = 1 → ∃ y : G, QuotientGroup.mk' N y = x ∧ y ^ 2 = 1) :
    m + n ≤ primeRank 2 G := by
  let : IsElementaryAbelian 2 (E.comap (QuotientGroup.mk' N)) :=
    IsElementaryAbelian.comap_quotient_of_central_involution_lifts N hN E hlift
  apply IsElementaryAbelian.primeRank_ge_of_card (E.comap (QuotientGroup.mk' N))
  rw [card_comap_quotient, hE, hcard, pow_add]

/-- The exact two-rank increase when every involution lifts through an elementary
central kernel. The cardinality parameter n is the rank of that kernel. -/
theorem two_rank_eq_quotient_add_of_central_involution_lifts
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N ≤ center G) [IsElementaryAbelian 2 N] {n : ℕ}
    (hcard : Nat.card N = 2 ^ n)
    (hlift : ∀ x : G ⧸ N, x ^ 2 = 1 → ∃ y : G, QuotientGroup.mk' N y = x ∧ y ^ 2 = 1) :
    primeRank 2 G = primeRank 2 (G ⧸ N) + n := by
  obtain ⟨E, hE, hEc⟩ := exists_elementaryAbelian_card_primeRank (G := G ⧸ N) (p := 2)
  let := hE
  let : IsElementaryAbelian 2 (E.comap (QuotientGroup.mk' N)) :=
    IsElementaryAbelian.comap_quotient_of_central_involution_lifts N hN E (fun x _ hx => hlift x hx)
  have hsize : Nat.card (E.comap (QuotientGroup.mk' N)) =
      2 ^ (primeRank 2 (G ⧸ N) + n) := by
    rw [card_comap_quotient, hEc, hcard, pow_add]
  have hlower := IsElementaryAbelian.primeRank_ge_of_card _ hsize
  have hupper := Theory.GroupTheory.primeRank_le_ker_add (p := 2) (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk'] at hupper
  have hNr := IsElementaryAbelian.primeRank_le_of_card_le N hcard.le
  omega
