module
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.OddLocal.Three
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.OddLocal.Five
public import Theory.GroupTheory.Covering

/-!
# The odd-primary HS multiplier bound and the remaining two-primary reduction

For every finite perfect central cover of the literal degree-100 HS carrier,
partial inversion excludes three and simultaneous inversion excludes five from
the kernel. The exact carrier order and cyclic-Sylow transfer exclude every
other odd prime, including primes absent from the base order. Consequently the
kernel is a two-group and an odd prime-power kernel is trivial.

The source application uses the actual map L → L/Z(L) followed by its specified
HS equivalence, and proves the odd-center exclusion required in A.2.19 Case II.
Neither simplicity of the base nor its comparison with the Leech model is needed
for these upper bounds. The exact upper bound of two still requires the separate
assertion that four does not divide the kernel order; the explicitly conditional
assembly below records that remaining obligation. No center-order-two hypothesis
or I.2.2 double-cover calculation is used to prove the odd-primary results.

Sources: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407, and A.2.19, pp.40–41;
GLS3 §6.1, especially Table 6.1.3. The local certificates retain the ATLAS
HSG1-p100B0 provenance under `HSUpperBound/OddLocal/source/`.
-/

namespace Theory.SpecificGroups.J2HSMultipliers.HS
open Sporadic.LeechRelated.HS PerfectCentralCovering Subgroup Theory.GroupTheory

private theorem square_not_dvd_card_carrier {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ¬ p ^ 2 ∣ Nat.card Carrier := by
  intro h
  have hd : p ∣ Nat.card Carrier := (dvd_pow_self p (by decide : 2 ≠ 0)).trans h
  rw [NormalizerIndex.card_carrier,
    show 44352000 = 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11 by norm_num] at hd
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11)] at hd
  rcases hd with (((h2 | h3) | h5) | h7) | h11
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))
  · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp
      (hp.dvd_of_dvd_pow h5))
  · subst p
    norm_num [NormalizerIndex.card_carrier] at h
  · subst p
    norm_num [NormalizerIndex.card_carrier] at h

/-- Every Sylow subgroup away from 2, 3 and 5 has order dividing its prime. -/
public theorem sylow_isCyclic_of_ne_two_three_five {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (P : Sylow p Carrier) :
    IsCyclic P := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hh
    exact square_not_dvd_card_carrier Fact.out hp2 hp3 hp5
      ((pow_dvd_pow p hh).trans (hn ▸ (P : Subgroup Carrier).card_subgroup_dvd_card))
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hn]
  simpa only [pow_one] using pow_dvd_pow p hnle

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

/-- Cyclic-Sylow transfer includes the primes absent from the HS order. -/
public theorem not_dvd_card_kernel_of_ne_two_three_five
    (f : E →* Carrier) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ¬ p ∣ Nat.card f.ker := by
  let : Fact p.Prime := ⟨hp⟩
  exact PerfectCentralCovering.not_dvd_card_kernel_of_isCyclic_sylow f hf hk
    (sylow_isCyclic_of_ne_two_three_five hp2 hp3 hp5)

/-- No odd prime divides the kernel of a finite perfect central cover of HS. -/
public theorem not_dvd_card_kernel_of_odd_prime
    (f : E →* Carrier) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card f.ker := by
  by_cases hp3 : p = 3
  · subst p
    exact Three.not_dvd_card_kernel f hf hk
  by_cases hp5 : p = 5
  · subst p
    exact Five.not_dvd_card_kernel f hf hk
  exact not_dvd_card_kernel_of_ne_two_three_five f hf hk hp hp2 hp3 hp5

/-- The whole perfect central kernel is a two-group, with no base simplicity premise. -/
public theorem kernel_isPGroup
    (f : E →* Carrier) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    IsPGroup 2 f.ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  have hp' := Nat.mem_primeFactors.mp hp
  have heq : p = 2 := by
    by_contra h2
    exact not_dvd_card_kernel_of_odd_prime f hf hk hp'.1 h2 hp'.2.1
  norm_num [heq]

/-- In particular, a perfect central kernel of odd prime-power order is trivial. -/
public theorem kernel_eq_bot_of_odd_pGroup
    (f : E →* Carrier) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hkp : IsPGroup p f.ker) : f.ker = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hkp.card_eq_or_dvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exact (not_dvd_card_kernel_of_odd_prime f hf hk hp hp2 h).elim

/-- The remaining four-divisibility bound suffices for the exact requested upper bound.
This theorem does not discharge its two-primary premise. -/
public theorem card_kernel_le_two_of_not_four_dvd
    (f : E →* Carrier) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (h4 : ¬ 4 ∣ Nat.card f.ker) : Nat.card f.ker ≤ 2 := by
  obtain ⟨n, hn⟩ := (kernel_isPGroup f hf hk).exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! h
    apply h4
    rw [hn]
    exact pow_dvd_pow 2 h
  rw [hn]
  calc
    2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hnle
    _ = 2 := by norm_num

/-- The source quotient map followed by the specified HS equivalence has two-group center. -/
public theorem center_isPGroup_of_quotient_equiv
    (e : E ⧸ center E ≃* Carrier) : IsPGroup 2 (center E) := by
  let f : E →* Carrier := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center E := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact (kernel_isPGroup f hf (le_of_eq hk)).of_equiv (MulEquiv.subgroupCongr hk)

/-- The literal A.2.19 odd-primary source cover has trivial center. -/
public theorem center_eq_bot_of_odd_pGroup_of_quotient_equiv
    (e : E ⧸ center E ≃* Carrier)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZ : IsPGroup p (center E)) :
    center E = ⊥ := by
  let f : E →* Carrier := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center E := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  rw [← hk]
  exact kernel_eq_bot_of_odd_pGroup f hf (le_of_eq hk) hp hp2 (hk.symm ▸ hZ)

/-- Exclusion consumed by A.2.19 Case II, with the actual central quotient retained. -/
public theorem not_nontrivial_odd_center_of_quotient_equiv
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (e : L ⧸ center L ≃* Carrier) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : IsPGroup p (center L)) : ¬ Nontrivial (center L) := by
  intro h
  let : Nontrivial (center L) := h
  have hb := center_eq_bot_of_odd_pGroup_of_quotient_equiv e hp hp2 hZ
  have hc := Subgroup.card_eq_one.mpr hb
  have hl : 1 < Nat.card (center L) := Finite.one_lt_card
  omega

end Theory.SpecificGroups.J2HSMultipliers.HS
