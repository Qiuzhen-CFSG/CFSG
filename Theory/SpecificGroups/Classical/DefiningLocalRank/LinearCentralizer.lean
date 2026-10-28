module
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Inner
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.SpecificGroups.OddThreeRank

/-!
# Defining-prime rank of linear involution centralizers

Every PSL₃ involution centralizer is an actual quotient of GL₂. The order
q(q−1)(q²−1) has defining-prime part q, so elementary abelian defining-prime
subgroups have order at most q. This is the linear half of the local rank
calculation used in Aschbacher–Smith A.2.12, printed p.36.
-/

public section
namespace Theory.SpecificGroups.DefiningLocalRank
open Matrix Subgroup
open scoped MatrixGroups

private theorem primeRank_le_of_card_dvd_pow_mul
    {G : Type*} [Group G] [Finite G] {p e c : ℕ} [Fact p.Prime]
    (hc : Nat.Coprime p c) (hcard : Nat.card G ∣ p ^ e * c) :
    primeRank p G ≤ e := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro A hA
  let : IsElementaryAbelian p A := hA
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
  have hd : p ^ k ∣ p ^ e * c := hk ▸ A.card_subgroup_dvd_card.trans hcard
  have he : p ^ k ∣ p ^ e := (hc.pow_left k).dvd_of_dvd_mul_right hd
  rw [hk]
  exact Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos _) he

private theorem gl2_card_eq {F : Type*} [Field F] [Finite F] :
    Nat.card (GL (Fin 2) F) = Nat.card F * ((Nat.card F - 1) * (Nat.card F ^ 2 - 1)) := by
  let : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_GL_field]
  simp only [Fin.prod_univ_two,Fin.val_zero,Fin.val_one,pow_zero,pow_one]
  rw [← Nat.card_eq_fintype_card]
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hs := Nat.sub_add_cancel hq
  have hq2 : Nat.card F ≤ Nat.card F ^ 2 := by nlinarith
  have hs2 := Nat.sub_add_cancel hq2
  have hsquare : Nat.card F ^ 2 - Nat.card F = Nat.card F * (Nat.card F - 1) := by nlinarith
  rw [hsquare]
  ring

/-- An actual quotient of GL₂ has defining-prime rank bounded by the field exponent. -/
theorem primeRank_le_fieldExponent_of_gl2_surjective
    {F H : Type*} [Field F] [Finite F] [Group H] [Finite H]
    {p e : ℕ} [Fact p.Prime] (he : 0 < e) (hcard : Nat.card F = p ^ e)
    (f : GL (Fin 2) F →* H) (hf : Function.Surjective f) : primeRank p H ≤ e := by
  have hp : p.Prime := Fact.out
  have hqpos : 0 < p ^ e := pow_pos hp.pos _
  have hq2pos : 0 < (p ^ e) ^ 2 := pow_pos hqpos _
  have hpq : p ∣ p ^ e := dvd_pow_self p (by omega)
  have hcop (n : ℕ) (hn : 0 < n) (hpn : p ∣ n) : Nat.Coprime p (n - 1) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have h1 : p ∣ 1 := by
      have hh := Nat.dvd_sub hpn hd
      simpa only [Nat.sub_sub_self hn] using hh
    exact hp.not_dvd_one h1
  have hc : Nat.Coprime p ((p ^ e - 1) * ((p ^ e) ^ 2 - 1)) :=
    (hcop _ hqpos hpq).mul_right (hcop _ hq2pos (hpq.trans (dvd_pow_self _ (by decide))))
  apply primeRank_le_of_card_dvd_pow_mul hc
  have hd := card_dvd_of_surjective f hf
  rw [gl2_card_eq,hcard] at hd
  exact hd

/-- Every actual PSL₃ involution centralizer has defining-prime rank at most
the field exponent. -/
theorem psl3_involution_centralizer_rank
    {F : Type*} [Field F] [Finite F] {p e : ℕ} [Fact p.Prime]
    (hp : Odd p) (he : 0 < e) (hcard : Nat.card F = p ^ e)
    (t : PSL(3,F)) (ht : orderOf t = 2) :
    primeRank p (centralizer ({t} : Set PSL(3,F))) ≤ e := by
  have h2 := Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card hp hcard
  obtain ⟨f,hf⟩ := Matrix.PSL3.OddInvolutionFixed.exists_gl2_surjective_centralizer t ht h2
  exact primeRank_le_fieldExponent_of_gl2_surjective he hcard f hf

end Theory.SpecificGroups.DefiningLocalRank
