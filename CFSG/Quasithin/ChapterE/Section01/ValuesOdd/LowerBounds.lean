module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.ProjectiveLinearInvolutions
public import Theory.SpecificGroups.SU3.ProjectiveInvolution
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Positivity for the alternating and odd-characteristic E-generation values

The groups in E.1.14(3), (6), and (7) have even order. We establish this for
any ambient group containing the actual model: use the order of A₇, and
explicit projective involutions for PSL₂, PSL₃, and PSU₃. The unitary parameter
is the fixed-field prime, so its matrix field has order `p²`.

A positive generation witness then makes the natural infimum an attained
positive minimum. In particular an even-order group has parameter one exactly
when it is E₁-generated. This is only the lower-bound and minimum step;
the almost-simple upper generation assertions are separate obligations.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.6 and E.1.14(3), (6), (7), printed pp.210 and 214; A.2.3(2), printed
p.33, specifies that `p` in `L₃^ε(p)` is prime.
-/

public section

namespace CFSG.Quasithin.ChapterE

variable {G : Type*} [Group G]

/-- The lower bound requires nonemptiness of the set of positive generation bounds. -/
theorem one_le_generationParameter_of_even_of_exists [Finite G] (heven : 2 ∣ Nat.card G)
    (hex : ∃ i : ℕ, 0 < i ∧ IsEGenerated i G) :
    1 ≤ generationParameter G :=
  (generationParameter_spec (fun ho => ho.not_two_dvd_nat heven) hex).1

/-- A genuine rank-one generation proof supplies both the upper bound and
the nonempty set needed for the lower bound. -/
theorem generationParameter_eq_one_iff_of_even [Finite G] (heven : 2 ∣ Nat.card G) :
    generationParameter G = 1 ↔ IsEGenerated 1 G := by
  constructor
  · intro hn
    have hgen := isEGenerated_generationParameter_of_pos (G := G) (by omega)
    rwa [hn] at hgen
  · intro hgen
    exact Nat.le_antisymm (generationParameter_le (by decide) hgen)
      (one_le_generationParameter_of_even_of_exists heven ⟨1, by decide, hgen⟩)

/-- An actual A₇ subgroup, in particular `F*(G) ≃ A₇`, forces even order. -/
theorem two_dvd_card_of_alternatingSeven_subgroup (L : Subgroup G)
    (e : L ≃* alternatingGroup (Fin 7)) : 2 ∣ Nat.card G := by
  have hL : Nat.card L = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact (show 2 ∣ Nat.card L by rw [hL]; decide).trans L.card_subgroup_dvd_card

/-- The PSL₂ parity witness works over every finite field, hence also for
the odd prime powers `q > 5` in E.1.14(6). -/
theorem two_dvd_card_of_pslTwo_subgroup (L : Subgroup G) {q : ℕ}
    (hL : ClassicalGroup.IsPSL L 2 q) : 2 ∣ Nat.card G := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hL
  have h : 2 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv]
    exact Matrix.ProjectiveSpecialLinearGroup.two_dvd_card_fin_two F
  exact h.trans L.card_subgroup_dvd_card

/-- The PSL₃ lower-bound witness needs only odd field order. -/
theorem two_dvd_card_of_pslThree_subgroup (L : Subgroup G) {q : ℕ}
    (hq : Odd q) (hL : ClassicalGroup.IsPSL L 3 q) : 2 ∣ Nat.card G := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hL
  have h : 2 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv]
    exact Matrix.ProjectiveSpecialLinearGroup.two_dvd_card_fin_three F
      (Field.two_ne_zero_of_odd_card F (hcard ▸ hq))
  exact h.trans L.card_subgroup_dvd_card

/-- The PSU₃ witness retains the arbitrary Hermitian form and the fixed-field
prime convention of the actual model predicate. -/
theorem two_dvd_card_of_psuThree_subgroup (L : Subgroup G) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hL : ClassicalGroup.IsPSU L 3 p) :
    2 ∣ Nat.card G := by
  obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := hL
  have h : 2 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv]
    exact Matrix.SU3.two_dvd_projective_card_of_prime_frobenius J p hp hodd hcard hc
  exact h.trans L.card_subgroup_dvd_card

end CFSG.Quasithin.ChapterE
