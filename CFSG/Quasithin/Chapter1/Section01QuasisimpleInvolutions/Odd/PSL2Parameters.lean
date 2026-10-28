module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Common
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.LinearActions
public import Theory.SpecificGroups.PSL2.OddInvolutionParameters
public import Theory.SpecificGroups.PSL2.OddSquareFieldFixed
public import Theory.SpecificGroups.PSL2.OddSylowFixers
public import GorensteinWalter.DGroupQuotientNotTwoGroup

/-!
# The PSL₂ parameter sieve in 1.1.5

The full fixed group of the actual central-quotient action has characteristic
two. For inner involutions its cyclic normal torus must be a two-group,
forcing one of `q - 1` and `q + 1` to be a power of two. Over a prime field
this gives the Fermat--Mersenne restriction. Over a square field with prime
larger than three, elementary arithmetic excludes the inner case.

The remaining square-field automorphism is conjugate to a coefficient
involution. Its full fixed subgroup is PGL₂ over the fixed field of order p.
That group's normal simple PSL₂ component makes its two-core trivial, which
contradicts characteristic two. All field witnesses, quotient maps and full
fixed groups are retained. PSL₂(9) remains available to the alternating branch.

Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.503, PDF p.520.
The two exports discharge the `hprime` and `hsquare` inputs of
`MarkedInvolution.odd_of_parameters_and_centers`.
-/

public section
open Subgroup Theory.GroupTheory GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions

private theorem fermat_or_mersenne_of_adjacent_two_power {p : ℕ} (hp : p.Prime) (hl : 3 < p)
    (h : ∃ n : ℕ, p - 1 = 2 ^ n ∨ p + 1 = 2 ^ n) :
    IsFermatOrMersennePrime p := by
  refine ⟨hp, ?_⟩
  obtain ⟨n, hn | hn⟩ := h
  · have he : p = 2 ^ n + 1 := by omega
    have hn0 : n ≠ 0 := by intro h0; simp [h0] at hn; omega
    obtain ⟨k, hk⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < 2) hn0 (he ▸ hp)
    exact Or.inl ⟨k, by simpa only [hk] using he⟩
  · exact Or.inr ⟨n, hn⟩

private theorem square_not_adjacent_two_power {p : ℕ} (ho : Odd p) (hl : 3 < p) :
    ¬ ∃ n : ℕ, p ^ 2 - 1 = 2 ^ n ∨ p ^ 2 + 1 = 2 ^ n := by
  rintro ⟨n, hm | hp⟩
  · have he : (p - 1) * (p + 1) = 2 ^ n := by
      have hpp : 1 ≤ p ^ 2 := by nlinarith
      nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p), Nat.sub_add_cancel hpp]
    have hminus : p - 1 ∣ 2 ^ n := ⟨p + 1, he.symm⟩
    have hplus : p + 1 ∣ 2 ^ n := by rw [← he]; exact dvd_mul_left _ _
    obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hminus
    obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hplus
    have ha2 : 2 ≤ a := by
      by_contra! h
      interval_cases a <;> norm_num at ha <;> omega
    have hb2 : 2 ≤ b := by
      by_contra! h
      interval_cases b <;> norm_num at hb <;> omega
    have h4a : 4 ∣ p - 1 := by rw [ha]; exact pow_dvd_pow 2 ha2
    have h4b : 4 ∣ p + 1 := by rw [hb]; exact pow_dvd_pow 2 hb2
    omega
  · have hn2 : 2 ≤ n := by
      by_contra! h
      interval_cases n <;> norm_num at hp <;> nlinarith
    have h4 : 4 ∣ p ^ 2 + 1 := by rw [hp]; exact pow_dvd_pow 2 hn2
    have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
      obtain ⟨k, hk⟩ := ho
      omega
    have hsq : (p ^ 2 + 1) % 4 = 2 := by
      rcases hmod with hm | hm <;> simp [Nat.add_mod, Nat.pow_mod, hm]
    omega

variable {L : Type*} [Group L] [Finite L] [Theory.GroupTheory.IsQuasisimple L]

/-- The prime-field parameter in source 1.1.5(3)(e) is a Fermat or Mersenne
prime, from the original marked action with no extra centralizer premise. -/
theorem MarkedInvolution.linear_two_prime_parameter
    {α : MulAut L} {P : Sylow 2 L} (d : MarkedInvolution α P)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 p) :
    IsFermatOrMersennePrime p := by
  have hl := linear_two_field_large ho hm
  obtain ⟨g, hg⟩ := (d.linear_two_prime_inner_and_center hp ho hm).1
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  obtain ⟨ha, hc, _⟩ := d.centralQuotient_model_inputs e
  have hi := (MulAut.centralQuotientAction_inner_iff e α).mpr ⟨g, hg.symm⟩
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, ho, by decide, by simpa using hcard⟩
  have hadj := Theory.PSL2.adjacent_two_power_of_inner_fixed_oddCore_eq_bot
    hodd (MulAut.centralQuotientAction e α) ha hi
    (pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hc)
  apply fermat_or_mersenne_of_adjacent_two_power hp hl
  simpa only [hcard] using hadj

/-- Square-field PSL₂ quotients with p > 3 are impossible in source 1.1.5.
Both inner and field involutions are excluded using their literal full fixed
groups. No recognition, automorphism, or covering premise remains. -/
theorem MarkedInvolution.linear_two_square_excluded
    {α : MulAut L} {P : Sylow 2 L} (d : MarkedInvolution α P)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hl : 3 < p)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 (p ^ 2)) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  obtain ⟨ha, hc, Q, hQ⟩ := d.centralQuotient_model_inputs e
  let a := MulAut.centralQuotientAction e α
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, ho, by decide, hcard⟩
  have hlarge : 3 < Nat.card F := by rw [hcard]; nlinarith
  rcases Theory.PSL2.odd_sylow_fixed_involution_inner_or_field hodd hlarge Q a ha hQ
      with hi | ⟨σ, β, hσ, hconj⟩
  · have hadj := Theory.PSL2.adjacent_two_power_of_inner_fixed_oddCore_eq_bot
      hodd a ha hi (pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hc)
    apply square_not_adjacent_two_power ho hl
    simpa only [hcard] using hadj
  · have hcf : HasCharacteristicTwo (psl2FieldAut F σ).fixedSubgroup := by
      rw [← hconj]
      exact hc.of_equiv (MulAut.fixedSubgroupCongr β a)
    obtain ⟨f⟩ := Theory.PSL2.OddSquareFieldFixed.coefficient_fixed_equiv ho hcard σ hσ
    let K := FixedPoints.subfield (zpowers σ) F
    have hK : Nat.card K = p :=
      Theory.PSL2.OddSquareFieldFixed.fixed_subfield_card hcard σ hσ
    have hKodd : IsOddPrimePower (Nat.card K) :=
      ⟨p, 1, hp, ho, by decide, by simpa using hK⟩
    have hKlarge : 3 < Nat.card K := by rwa [hK]
    have hcore := pCore_two_eq_bot_of_mulEquiv_pgl2_odd K hKodd hKlarge f
    have htriv : Subsingleton (psl2FieldAut F σ).fixedSubgroup := by
      have helem (x : (psl2FieldAut F σ).fixedSubgroup) : x = 1 := by
        apply mem_bot.mp
        rw [← hcore]
        apply hcf
        rw [hcore, mem_centralizer_iff]
        intro y hy
        have hy1 : y = 1 := mem_bot.mp hy
        simp [hy1]
      exact ⟨fun x y => (helem x).trans (helem y).symm⟩
    let : Subsingleton (psl2FieldAut F σ).fixedSubgroup := htriv
    let : Subsingleton (PGL2 K) := f.symm.injective.subsingleton
    let : Subsingleton PSL(2,K) :=
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.subsingleton
    let : IsSimpleGroup PSL(2,K) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hKlarge
    exact not_subsingleton PSL(2,K) inferInstance

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
