module
public import CFSG.Quasithin.ChapterE.Section06.Obstructions
/-!
# The original minimum is a maximal escaping subspace

For U < W ≤ V, multiplicativity of the actual subgroup indices and their
binary power formulas give a strict decrease of corank. A subgroup attaining
the full globalR minimum therefore cannot have a larger escaping centralizer
subspace. This supplies exactly the maximality used by E.6.11, without
changing the domain defining globalR or excluding the zero subgroup by fiat.

Source: Aschbacher–Smith, E.6.11 and E.6.25, printed pp.249 and 255.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G]
variable {V U W : Subgroup G}

/-- Proper containment of binary subspaces strictly decreases corank. -/
theorem subgroupCorank_lt_of_lt [IsElementaryAbelian 2 V]
    (hUW : U < W) (hWV : W ≤ V) : subgroupCorank V W < subgroupCorank V U := by
  have hUone : U.relIndex W ≠ 1 := fun he => hUW.not_ge (relIndex_eq_one.mp he)
  have hUzero : U.relIndex W ≠ 0 := (U.subgroupOf W).index_ne_zero_of_finite
  have hUgt : 1 < U.relIndex W := by omega
  have hWpos : 0 < W.relIndex V := Nat.pos_of_ne_zero (W.subgroupOf V).index_ne_zero_of_finite
  have hi : W.relIndex V < U.relIndex V := by
    have hh := relIndex_mul_relIndex U W V hUW.le hWV
    nlinarith
  rw [relIndex_eq_two_pow_quotient_finrank,
    relIndex_eq_two_pow_quotient_finrank] at hi
  simpa only [subgroupCorank_eq_quotient_finrank] using
    (pow_lt_pow_iff_right₀ (by decide : 1 < 2)).mp hi

/-- The literal global minimum supplies the source maximality hypothesis. -/
theorem HypothesisE61.maximal_escape_of_minimum
    {K : GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : HypothesisE61 K T M V)
    (hmin : (subgroupCorank V U : ℕ∞) = globalR V) :
    ∀ W : Subgroup G, U < W → W ≤ V → centralizer (W : Set G) ≤ M := by
  let _ := h.elementary
  intro W hUW hWV
  by_contra hn
  have he : ¬ centralizer (W : Set G) ≤ normalizer (V : Set G) :=
    fun hc => hn (hc.trans h.normalizer_le)
  have hle := globalR_le_corank hWV he
  rw [← hmin] at hle
  have hh : subgroupCorank V U ≤ subgroupCorank V W := ENat.natCast_le_natCast.mp hle
  exact (subgroupCorank_lt_of_lt hUW hWV).not_ge hh
end CFSG.Quasithin.ChapterE.Section06
