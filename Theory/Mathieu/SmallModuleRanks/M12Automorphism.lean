module
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Automorphisms
public import Theory.GroupTheory.PrimeRankHom
/-!
# Two-rank of the full automorphism group of M₁₂

The intrinsic M₁₂ rank bound is three. The actual marked inner subgroup has
index two in the verified degree-24 automorphism carrier, so adjoining outer
automorphisms adds at most one to elementary rank. The original conjugation
map is retained, giving the inner bound in the literal full automorphism group.
Source: Aschbacher–Smith H.11.1 and K.4.2.
-/
public section
namespace Sporadic.Mathieu.M12AutomorphismRank
open M12ExceptionalExtension

/-- The original M₁₂ conjugation map is injective. -/
theorem conjugation_injective : Function.Injective (MulAut.conj : M12 →* MulAut M12) := by
  intro x y h
  apply innerModel.embedding_injective
  apply automorphismEquiv.injective
  simpa only [automorphismEquiv_embedding] using h

/-- The literal inner-automorphism subgroup has two-rank at most three. -/
theorem inner_twoRank_le_three :
    primeRank 2 (MulAut.innerSubgroup M12) ≤ 3 := by
  let e : M12 ≃* MulAut.innerSubgroup M12 := MonoidHom.ofInjective conjugation_injective
  rw [← Theory.GroupTheory.primeRank_equiv 2 e]
  exact m12_twoRank_le_three

/-- The full automorphism group of the native M₁₂ has two-rank at most four. -/
theorem twoRank_le_four : primeRank 2 (MulAut M12) ≤ 4 := by
  have hh := Theory.GroupTheory.primeRank_le_add_of_index_le (p := 2) (n := 1)
    inner (by simp only [inner_index, pow_one, le_refl])
  have hr : primeRank 2 inner ≤ 3 := by
    rw [← Theory.GroupTheory.primeRank_equiv 2 innerModel.equiv]
    exact m12_twoRank_le_three
  rw [Theory.GroupTheory.primeRank_equiv 2 automorphismEquiv] at hh
  omega
end Sporadic.Mathieu.M12AutomorphismRank
