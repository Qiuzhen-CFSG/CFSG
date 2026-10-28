module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags

/-!
# The complementary pair of the four-letter alternating residual

The common fixed letters of the two standard three-cycles are exactly 4 and 5.
A permutation normalizing their embedded A₄ therefore preserves this pair.
This exposes the shared fixed-letter argument of `OrdinaryNormalizer` for
actual residual-image consumers, without exposing its implementation details.

Source: Aschbacher–Smith, §B.3, printed pp.83–85, and 3.3.31, printed p.602.
-/

open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags
private theorem common_fixed (i : Fin 6) (ha : cycle012 i = i) (hb : cycle013 i = i) :
    i = 4 ∨ i = 5 := by
  exact (by decide : ∀ j : Fin 6, cycle012 j = j → cycle013 j = j → j = 4 ∨ j = 5) i ha hb

/-- The normalizer of the first-four-letter A₄ preserves its complementary pair. -/
public theorem normalizer_K_le_H1 : normalizer (K : Set S) ≤ H1 := by
  intro g hg
  have hfix (i : Fin 6) (hi : i = 4 ∨ i = 5) (k : S) (hk : k ∈ K) : k (g i) = g i := by
    have hh := le_normalizer_iff.mp (le_refl (normalizer (K : Set S)))
      g⁻¹ ((normalizer (K : Set S)).inv_mem hg) k hk
    have hh' := (mem_K.mp hh).1
    have he : (g⁻¹ * k * (g⁻¹)⁻¹) i = i := by rcases hi with rfl | rfl; exact hh'.1; exact hh'.2
    have hf := congrArg g he
    change g (g.symm (k (g i))) = g i at hf
    simpa only [g.apply_symm_apply] using hf
  have h4 := common_fixed (g 4) (hfix 4 (Or.inl rfl) cycle012 (by decide))
    (hfix 4 (Or.inl rfl) cycle013 (by decide))
  have h5 := common_fixed (g 5) (hfix 5 (Or.inr rfl) cycle012 (by decide))
    (hfix 5 (Or.inr rfl) cycle013 (by decide))
  have hn : g 4 ≠ g 5 := g.injective.ne (by decide)
  change (pair 4 5).image g = pair 4 5
  rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5 <;>
    simp_all [pair, Finset.pair_comm]

end Theory.SpecificGroups.SymmetricSix.BinaryFlags
