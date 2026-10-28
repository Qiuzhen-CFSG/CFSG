module

public import Theory.Quasithin.CoprimeLocalRank

/-!
# Quasithinness through a two-group kernel

A surjection with two-group kernel preserves the upper bound on every
odd local prime rank. Lift each target two-local normalizer using the
Frattini argument, and then lift its abelian odd-prime subgroups by
Schur--Zassenhaus. Consequently quasithinness passes to quotients by
normal two-subgroups.

Source: Aschbacher--Smith, A.2.10--11, printed p.35; applied to the
literal quotient by O₂ in original 15.2.4, printed p.1106.
-/

public section
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- A surjection with two-group kernel preserves quasithinness. -/
theorem IsQuasithin.of_surjective_twoKernel (h : IsQuasithin G)
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    IsQuasithin H := by
  apply isQuasithin_iff_twoLocalPrimeRank.mpr
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  have hc : Nat.Coprime p (Nat.card f.ker) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hk
    rw [hn]
    exact (Nat.coprime_two_right.mpr ho).pow_right n
  exact (twoLocalPrimeRank_le_of_surjective_of_coprime p f hf hc).trans
    (isQuasithin_iff_twoLocalPrimeRank.mp h p hp ho)

/-- Quasithinness descends through a normal two-subgroup. -/
theorem IsQuasithin.quotient_twoSubgroup (h : IsQuasithin G)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N) : IsQuasithin (G ⧸ N) := by
  apply h.of_surjective_twoKernel (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  rw [QuotientGroup.ker_mk']
  exact hN
