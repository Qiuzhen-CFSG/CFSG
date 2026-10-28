module

public import ABG.Basic

/-!
# Arithmetic of characteristic parameters

Chapter I, article page 3 of Alperin–Brauer–Gorenstein defines the characteristic
power q and odd central kernel order d through the involution centralizer.
The lemmas here extract their basic arithmetic without invoking the main
theorems: q is a nontrivial odd prime power, and d is odd and positive.

The proof uses the two permitted residues modulo four to obtain oddness of q,
then transfers oddness across the nonzero prime-power exponent. Oddness of d
comes directly from the kernel subgroup in the central quotient. These facts
supply the arithmetic hypotheses needed by the later order formulas.
-/

namespace ABG
universe u v
variable {G : Type u} [Group G] {x : G} {q d : ℕ}

public theorem InvolutionCentralizerParameters.mod_four
    (h : InvolutionCentralizerParameters x q d) : q % 4 = 3 ∨ q % 4 = 1 := by
  obtain ⟨p, n, hp, hn, hq, h⟩ := h
  exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

public theorem InvolutionCentralizerParameters.odd
    (h : InvolutionCentralizerParameters x q d) : Odd q := by
  have := h.mod_four
  rw [Nat.odd_iff]
  omega

public theorem InvolutionCentralizerParameters.prime_power
    (h : InvolutionCentralizerParameters x q d) :
    ∃ p n : ℕ, p.Prime ∧ Odd p ∧ n ≠ 0 ∧ q = p ^ n := by
  have hodd := h.odd
  obtain ⟨p, n, hp, hn, hq, _⟩ := h
  refine ⟨p, n, hp, ?_, hn, hq⟩
  rw [hq] at hodd
  exact (Nat.odd_pow_iff hn).mp hodd

public theorem InvolutionCentralizerParameters.one_lt
    (h : InvolutionCentralizerParameters x q d) : 1 < q := by
  obtain ⟨p, n, hp, _, hn, rfl⟩ := h.prime_power
  exact one_lt_pow₀ hp.one_lt hn

public theorem IsCentralOddQuotient.odd
    {H : Type u} [Group H] {K : Type v} [Group K]
    (h : IsCentralOddQuotient H K d) : Odd d := by
  obtain ⟨Z, _, _, hZ, rfl, _⟩ := h
  exact hZ

public theorem InvolutionCentralizerParameters.kernel_odd
    (h : InvolutionCentralizerParameters x q d) : Odd d := by
  obtain ⟨p, n, hp, hn, hq, h⟩ := h
  let : Fact p.Prime := ⟨hp⟩
  exact h.elim (fun h => h.2.odd) (fun h => h.2.odd)

public theorem HasCharacteristicParameters.prime_power
    (h : HasCharacteristicParameters G q d) :
    ∃ p n : ℕ, p.Prime ∧ Odd p ∧ n ≠ 0 ∧ q = p ^ n := by
  obtain ⟨x, _, hx⟩ := h
  exact hx.prime_power

public theorem HasCharacteristicParameters.odd_kernel_pos
    (h : HasCharacteristicParameters G q d) : Odd d ∧ 0 < d := by
  obtain ⟨x, _, hx⟩ := h
  have hd := hx.kernel_odd
  refine ⟨hd, ?_⟩
  have := Nat.odd_iff.mp hd
  omega
end ABG
