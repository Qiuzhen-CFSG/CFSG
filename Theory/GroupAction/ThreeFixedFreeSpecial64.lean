module
public import Theory.GroupTheory.Commutator.CentralElementaryFourQuotient
public import Theory.GroupTheory.CommutatorPreimageFrattini

/-!
# A cubic fixed-free central extension of order sixty-four

A nonabelian group H of order sixty-four with a central subgroup Z of order
four and elementary quotient H/Z is special whenever an actual automorphism
a with a³=1 fixes only the identity. More precisely, the center, derived
subgroup and Frattini subgroup all equal the prescribed Z. No graph, group
model, or faithful representation is part of the hypotheses.

Restriction of a to any characteristic subgroup remains fixed-free. Orbit
counting makes its order congruent to one modulo three. The nontrivial
derived subgroup lies in Z, so this congruence forces it to have order four.
The center consequently has order four, sixteen or sixty-four. The last case
is abelian; the middle case has central elementary quotient of order four,
whose derived subgroup has order at most two by the central-dihedral bound.
Thus the center is Z. The elementary quotient gives Frattini≤Z, and the
derived subgroup gives the reverse containment.

This source-neutral implication supplies the omitted special-group reduction
in Stellmacher, Journal of Algebra 190 (1997), proof of (8.6)(b1), printed
p.44. Its application constructs the cubic automorphism of the actual initial
residual two-core and proves nonabelianness from its module geometry.
-/

private theorem cubic_fixed_free_card_mod_three
    {H : Type*} [Group H] [Finite H]
    (a : MulAut H) (hcube : a ^ 3 = 1)
    (hfixed : ∀ x : H, a x = x → x = 1) : Nat.card H % 3 = 1 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let line := Subgroup.zpowers a
  have hp : IsPGroup 3 line := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [line,Nat.card_zpowers,pow_one] using orderOf_dvd_of_pow_eq_one hcube)
  let fixed := FixedPoints.subgroup line H
  have hbot : fixed = ⊥ := by
    apply bot_unique
    intro x hx
    apply hfixed x
    exact ((FixedPoints.mem_subgroup (M := line) (α := H) (a := x)).mp hx) ⟨a,Subgroup.mem_zpowers a⟩
  have hmod := hp.card_modEq_card_fixedPoints H
  change Nat.card H % 3 = Nat.card fixed % 3 at hmod
  simpa only [hbot,Subgroup.card_bot] using hmod

public theorem three_fixed_free_special64
    {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H = 64) (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) (hZcard : Nat.card Z = 4)
    [IsElementaryAbelian 2 (H ⧸ Z)]
    (hnoncomm : ¬ IsMulCommutative H)
    (a : MulAut H) (hcube : a ^ 3 = 1)
    (hfixed : ∀ x : H, a x = x → x = 1) :
    Subgroup.center H = Z ∧ commutator H = Z ∧ frattini H = Z := by
  classical
  have hcharMod (N : Subgroup H) [N.Characteristic] : Nat.card N % 3 = 1 := by
    apply cubic_fixed_free_card_mod_three (MulAut.characteristic N a)
      (by rw [← map_pow,hcube,map_one])
    intro n hn
    apply Subtype.ext
    exact hfixed n (congrArg Subtype.val hn)
  have htwo : IsPGroup 2 H := IsPGroup.of_card_dvd_pow (n := 6) (by rw [hcard]; decide)
  let _ : Fact (IsPGroup 2 H) := ⟨htwo⟩
  have hPhi : frattini H ≤ Z :=
    Subgroup.frattini_le_of_elementary_quotient htwo Z inferInstance
  have hderived : commutator H ≤ Z :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative (H ⧸ Z))
  have hderivedNe : commutator H ≠ ⊥ := by
    intro heq
    exact hnoncomm ((commutator_eq_bot_iff H).mp heq)
  have hderivedCard : Nat.card (commutator H) = 4 := by
    have hdvd : Nat.card (commutator H) ∣ 4 := hZcard ▸ Subgroup.card_dvd_of_le hderived
    have hmod := hcharMod (commutator H)
    have hne : Nat.card (commutator H) ≠ 1 := by
      intro heq
      exact hderivedNe (Subgroup.card_eq_one.mp heq)
    have hcases : Nat.card (commutator H) = 1 ∨ Nat.card (commutator H) = 2 ∨
        Nat.card (commutator H) = 4 := by
      have hpdiv : Nat.card (commutator H) ∣ 2 ^ 2 := hdvd
      obtain ⟨n,hn,hpow⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpdiv
      interval_cases n <;> norm_num only [Nat.reducePow] at hpow <;> omega
    omega
  have hderivedEq : commutator H = Z :=
    Subgroup.eq_of_le_of_card_ge hderived (by omega)
  have hcenterCard : Nat.card (Subgroup.center H) = 4 := by
    have hdvd : Nat.card (Subgroup.center H) ∣ 2 ^ 6 :=
      by simpa [hcard] using Subgroup.card_subgroup_dvd_card (Subgroup.center H)
    obtain ⟨n,hn,hpow⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hmod := hcharMod (Subgroup.center H)
    have hlow : 4 ≤ Nat.card (Subgroup.center H) := hZcard ▸ Subgroup.card_le_of_le hZ
    have hcases : Nat.card (Subgroup.center H) = 4 ∨
        Nat.card (Subgroup.center H) = 16 ∨ Nat.card (Subgroup.center H) = 64 := by
      interval_cases n <;> norm_num only [Nat.reducePow] at hpow <;> omega
    rcases hcases with hfour | hsixteen | hwhole
    · exact hfour
    · let _ : IsElementaryAbelian 2 (H ⧸ Subgroup.center H) :=
        Subgroup.elementary_quotient_of_frattini_le htwo (Subgroup.center H) (hPhi.trans hZ)
      have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center H)
      rw [hcard,hsixteen] at hcount
      have hquot : Nat.card (H ⧸ Subgroup.center H) = 4 := by omega
      have hbound := card_commutator_le_two_of_central_elementary_four_quotient
        (Subgroup.center H) le_rfl hquot
      omega
    · have htop : Subgroup.center H = ⊤ :=
        (Subgroup.center H).eq_top_of_card_eq (hwhole.trans hcard.symm)
      have hcomm : IsMulCommutative H := (Subgroup.center_eq_top_iff).mp htop
      exact (hnoncomm hcomm).elim
  exact ⟨(Subgroup.eq_of_le_of_card_ge hZ (by omega)).symm,hderivedEq,
    le_antisymm hPhi (hderivedEq ▸ commutator_le_frattini_of_isPGroup (p := 2))⟩
