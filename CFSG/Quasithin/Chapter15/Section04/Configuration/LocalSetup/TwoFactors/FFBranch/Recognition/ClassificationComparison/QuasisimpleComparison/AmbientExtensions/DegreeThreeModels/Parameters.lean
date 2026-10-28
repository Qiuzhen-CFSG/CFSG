module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.Targets
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions.Rows
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Defining-prime reduction in the two degree-three ambient rows

The actual projective matrix group contains the defining-characteristic
root group of order p³. Quotient and embedding maps retain this divisor in
both special/projective alternatives and their graph extensions. Since D/N
is a two-group, this odd cube divides the small offender actor's order.
Its possible orders force p = 3. The prescribed sign excludes the linear
case, leaving SU₃(3) or PSU₃(3), with the original graph action in row (11).

Source: Aschbacher–Smith, F.6.18(10)–(11), printed pp.309–310;
B.5.1/B.5.6, pp.99–110; the comparison in 15.4.18, p.1163.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace QuasisimpleComparison.AmbientExtensions
open GoldschmidtAlternatives
universe u v
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D} {K : GroupClass.{u}}

omit [Finite D] in
private theorem cube_linear {p : ℕ} (hm : LinearThree D p) : p ^ 3 ∣ Nat.card D := by
  obtain ⟨F, _, _, hc, he⟩ := hm
  have hd := Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card (F := F)
  rw [hc] at hd
  rcases he with he | he
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv]
    exact hd.trans (card_quotient_dvd_card (center SL(3,F)))
  · obtain ⟨e⟩ := he
    simpa only [Nat.card_congr e.toEquiv] using hd

private theorem fixed_card {p : ℕ} (hp : p.Prime) {F : Type} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hc : Nat.card F = p ^ 2) (hf : ∀ x, J.conj x = x ^ p) :
    Nat.card {x : F // J.conj x = x} = p := by
  let : Fact p.Prime := ⟨hp⟩
  simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
    J.conj p 1 (by decide) (by simpa using hc) (by simpa using hf)

omit [Finite D] in
private theorem cube_unitary {p : ℕ} (hp : p.Prime) (hm : UnitaryThree D p) :
    p ^ 3 ∣ Nat.card D := by
  obtain ⟨F, _, _, J, hc, hf, he⟩ := hm
  have hd := J.cube_dvd_card_projective hc (fixed_card hp J hc hf)
  rcases he with he | he
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv]
    exact hd.trans (card_dvd_of_surjective J.specialToProjective J.specialToProjective_surjective)
  · obtain ⟨e⟩ := he
    simpa only [Nat.card_congr e.toEquiv] using hd

omit [Finite D] in
private theorem cube_linear_graph {p : ℕ} (hm : LinearGraphExtension D p) :
    p ^ 3 ∣ Nat.card D := by
  obtain ⟨F, _, _, hc, he⟩ := hm
  have hd := Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card (F := F)
  rw [hc] at hd
  rcases he with ⟨i, t, hi, _⟩ | ⟨i, t, hi, _⟩
  · exact (hd.trans (card_quotient_dvd_card (center SL(3,F)))).trans
      (card_dvd_of_injective i hi)
  · exact hd.trans (card_dvd_of_injective i hi)

omit [Finite D] in
private theorem cube_unitary_graph {p : ℕ} (hp : p.Prime)
    (hm : UnitaryGraphExtension D p) : p ^ 3 ∣ Nat.card D := by
  obtain ⟨F, _, _, J, hc, hf, hJ, he⟩ := hm
  have hd := J.cube_dvd_card_projective hc (fixed_card hp J hc hf)
  rcases he with ⟨i, t, hi, _⟩ | ⟨i, t, hi, _⟩
  · exact (hd.trans (card_dvd_of_surjective J.specialToProjective
      J.specialToProjective_surjective)).trans (card_dvd_of_injective i hi)
  · exact hd.trans (card_dvd_of_injective i hi)

private theorem prime_eq_three_of_cube (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) {p : ℕ} (hp : p.Prime)
    (hmod : p % 8 = 3 ∨ p % 8 = 5) (hd : p ^ 3 ∣ Nat.card D) : p = 3 := by
  have hp2 : p ≠ 2 := by omega
  have hc : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr (by
    intro hd2
    have := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd2
    rcases this with he | he
    · exact hp.ne_one he
    · exact hp2 he)
  have hd' := (odd_dvd_actor h (hc.pow_left 3) hd).trans (actor_card_dvd s)
  have hle : p ≤ 7 := by
    by_contra hh
    exact no_large_prime h s hp (by omega)
      ((dvd_pow_self p (by decide : 3 ≠ 0)).trans hd)
  interval_cases p <;> norm_num at *

/-- The linear sign is excluded, and row (10) has fixed-field order three. -/
theorem case10_unitary_three (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : Case10 G₁ G₂) :
    UnitaryThree D 3 := by
  obtain ⟨p, hp, hmodel, _⟩ := hr
  rcases hmodel with ⟨hm, he⟩ | ⟨hm, he⟩
  · have hp3 := prime_eq_three_of_cube h s hp (Or.inr hm) (cube_linear he)
    omega
  · have hp3 := prime_eq_three_of_cube h s hp (Or.inl hm) (cube_unitary hp he)
    simpa only [hp3] using he

/-- Row (11) retains its actual coefficient action over a nine-element field. -/
theorem case11_unitary_three (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : Case11 G₁ G₂) :
    UnitaryGraphExtension D 3 := by
  obtain ⟨p, hp, hmodel, _⟩ := hr
  rcases hmodel with ⟨hm, he⟩ | ⟨hm, he⟩
  · have hp3 := prime_eq_three_of_cube h s hp (Or.inr hm) (cube_linear_graph he)
    omega
  · have hp3 := prime_eq_three_of_cube h s hp (Or.inl hm) (cube_unitary_graph hp he)
    simpa only [hp3] using he

end QuasisimpleComparison.AmbientExtensions
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
