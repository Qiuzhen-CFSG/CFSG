module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentModels
public import Theory.SpecificGroups.Classical.SmallSylowOrders

/-!
# The odd-model sieve in the component branch

The literal elementary Sylow of order at most eight excludes the odd
three-dimensional linear and unitary models using their orders. The
remaining PSL₂ model has field order 3 or 5 modulo eight, so Theorem C's
degree-at-most-two restriction forces a prime field. Every conclusion
retains the actual field and the original model equivalence.

Source: Aschbacher–Smith F.6.17–18, printed pp.309–310.
-/

public section
open Subgroup Theory.GroupTheory Theory.ClassicalSmallSylow
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G]
theorem not_psl3_odd_of_small_sylow (P : Sylow 2 G) (hP : Nat.card P ≤ 8)
    {q : ℕ} (ho : Odd q) : ¬ ClassicalGroup.IsPSL G 3 q := by
  rintro ⟨F, hF, hfin, hq, ⟨e⟩⟩
  apply not_sixteen_dvd_of_sylow_le_eight P hP
  rw [Nat.card_congr e.toEquiv]
  exact sixteen_dvd_psl3_odd (hq ▸ ho)

theorem not_psu3_odd_of_small_sylow (P : Sylow 2 G) (hP : Nat.card P ≤ 8)
    {q : ℕ} (hq : 1 < q) (ho : Odd q) : ¬ ClassicalGroup.IsPSU G 3 q := by
  rintro ⟨F, hF, hfin, J, hc, hconj, ⟨e⟩⟩
  apply not_sixteen_dvd_of_sylow_le_eight P hP
  rw [Nat.card_congr e.toEquiv]
  exact sixteen_dvd_psu3_odd J hq ho hc hconj


theorem odd_model_of_small_elementary_sylow
    (P : Sylow 2 G) [IsElementaryAbelian 2 P] (hP : Nat.card P ≤ 8)
    (hm : ChapterA.Section02.IsTheoremCOddModel G) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      ClassicalGroup.IsPSL G 2 p := by
  cases hm with
  | linear_three p hp ho hm => exact (not_psl3_odd_of_small_sylow P hP ho hm).elim
  | unitary_three p hp ho hm =>
    exact (not_psu3_odd_of_small_sylow P hP hp.one_lt ho hm).elim
  | linear_two p f hp ho hf hm =>
    obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
    have hfpos : 0 < f := by
      have hc : 1 < Nat.card F := Finite.one_lt_card
      by_contra! hh
      have hz : f = 0 := by omega
      simp [hz] at hcard
      omega
    let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
    let eP : P ≃* S := (P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
    let : IsElementaryAbelian 2 S := IsElementaryAbelian.of_surjective eP.toMonoidHom eP.surjective
    have hs := psl2_mod_eight_of_elementary_sylow ⟨p, f, hp, ho, hfpos, hcard⟩ S
    rw [hcard] at hs
    have he := degree_one_of_small_degree_nonsquare_mod_eight hf hs
    subst f
    simp only [pow_one] at hcard hs
    exact ⟨p, hp, ho, hs, F, hF, hfin, hcard, ⟨e⟩⟩
end CFSG.Quasithin.ChapterF.SourceAssembly
