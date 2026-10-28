module

public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.Mathieu.SmallModuleRanks.M24
public import Theory.Mathieu.M12.A5Fixer.Automorphisms.OuterIndex
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.GroupTheory.PrimeRankAutomorphismOrder

/-!
# Intrinsic Mathieu rank inputs for small modules

The native Sylow calculations prove m₂(M₁₂) ≤ 3 and m₂(M₂₄) ≤ 6.
The established outer index at most two for M₁₂ adds at most one to
its rank. Every automorphism of M₂₄ is inner, and centerlessness makes
conjugation an isomorphism, preserving its rank.

These bounds have no representation, recognition, or local-coverage
premises. Together with the existing M₂₂ and M₂₃ bounds, they supply
the intrinsic rank inputs used in the small Mathieu module branches.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.7.3(2),
printed p.348 (PDF p.359); rank references Asc82a and GLS98 5.2.10/5.6.1,
identified on printed p.347.
-/

public section
namespace Sporadic.Mathieu
open Theory.GroupTheory

/-- The full abstract automorphism group of native M₁₂ has two-rank at most four. -/
theorem m12_automorphism_twoRank_le_four : primeRank 2 (MulAut M12) ≤ 4 := by
  have ho : Nat.card (MulAut.Outer M12) ≤ 2 ^ 1 :=
    M12A5Fixer.Automorphisms.outerIndexBound
  exact (automorphism_primeRank_le_add_of_outer_card m12_center_eq_bot ho).trans
    (Nat.add_le_add_right m12_twoRank_le_three 1)

/-- The full abstract automorphism group of native M₂₄ has two-rank at most six. -/
theorem m24_automorphism_twoRank_le_six : primeRank 2 (MulAut M24) ≤ 6 := by
  let e : M24 ≃* MulAut M24 := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot M24InvolutionCentralizers.center_eq_bot,
      M24OuterRestriction.conj_surjective⟩
  rw [← primeRank_equiv 2 e]
  exact m24_twoRank_le_six

end Sporadic.Mathieu
