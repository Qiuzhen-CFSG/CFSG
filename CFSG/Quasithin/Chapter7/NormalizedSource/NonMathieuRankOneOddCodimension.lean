module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneThompson
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Parameter
public import CFSG.Quasithin.ChapterE.Section06.Obstructions

/-!
# Odd-element codimension and the local Cartan parameter

If every odd-prime-order automizer element moves at least b/c dimensions,
a subgroup fixing a subspace of corank less than b/c has no such element.
Its actual Cartan witnesses are therefore trivial, giving n' <= 1.
This keeps the induced automizer and the literal centralizer fixed, as
required by E.6.27. The Suzuki consumer uses b=8n and c=3.
Source: Aschbacher--Smith H.0.1, H.3 and 7.4.1, pp.377,379,700.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterE ChapterE.Section06.FixedPointBounds
variable {G : Type*} [Group G] [Finite G]

/-- Without odd prime-order elements, the intrinsic Cartan parameter is one. -/
theorem nPrime_le_one_of_no_odd_prime
    (hn : ∀ (p : ℕ), p.Prime → Odd p → ∀ x : G, orderOf x ≠ p) :
    nPrime G ≤ 1 := by
  apply nPrime_le_iff.mpr
  intro c w
  have hcard : Nat.card w.cyclicGroup = 1 := by
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro p hp hd
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' p hd
    have ho : Odd (Nat.card w.cyclicGroup) := w.odd.of_dvd_nat (card_dvd_of_le w.cyclic_le)
    have hp2 : p ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ hd)
    exact hn p hp (hp.odd_of_ne_two hp2) x (by simpa using hx)
  rw [w.card] at hcard
  have hpow := c.lt_two_pow_self
  omega

/-- Small subspaces force n' <= 1 once the odd-prime displacement estimate
is known on the actual ambient automizer. -/
theorem induced_nPrime_le_one_of_odd_fixedCodim
    (W A U : Subgroup G) [IsElementaryAbelian 2 W]
    (hAN : A ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (hAU : A ≤ centralizer (U : Set G)) {b c : ℕ}
    (hodd : ∀ (p : ℕ), p.Prime → Odd p → ∀ a : Automizer W,
      orderOf a = p → b ≤ c * fixedCodim (automizerRepresentation W) (zpowers a))
    (hsmall : c * subgroupCorank W U < b) :
    nPrime (inducedAutomizer W A) ≤ 1 := by
  apply nPrime_le_one_of_no_odd_prime
  intro p hp ho a ha
  have hlow := hodd p hp ho a.val (by simpa using ha)
  have hle : zpowers a.val ≤ inducedAutomizer W A := zpowers_le.mpr a.property
  have hcod := fixedCodim_mono (automizerRepresentation W) hle
  rw [fixedCodim_inducedAutomizer W A hAN] at hcod
  have hUA : U ≤ W ⊓ centralizer (A : Set G) :=
    le_inf hUW (le_centralizer_iff.mp hAU)
  have hadd := offender_corank_add hUA inf_le_left
  have hcor : subgroupCorank W (W ⊓ centralizer (A : Set G)) ≤ subgroupCorank W U := by omega
  have hmul := Nat.mul_le_mul_left c (hcod.trans hcor)
  omega
end CFSG.Quasithin.Chapter7.NormalizedSource
