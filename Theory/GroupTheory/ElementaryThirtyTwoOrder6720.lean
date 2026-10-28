module
public import Theory.GroupTheory.Hall.Existence
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Convert

/-!
# Solvable automorphism subgroups on an elementary group of order thirty-two

A finite elementary abelian group of order 32 has no solvable automorphism
subgroup of order 6720. The elementary-abelian hypothesis matches the intended
recognition interface; the underlying action obstruction uses only the order
of the acted-on group.

Hall's theorem gives a subgroup of order 35 in any solvable group of the
prohibited order. Sylow counting makes both its Sylow subgroups normal, so
its subgroups of orders 5 and 7 commute. For a faithful action on a group of
order 32, orbit congruences and Lagrange's theorem force their fixed subgroups
to have orders 2 and 4 respectively. The subgroup of order 5 preserves the
four-element fixed subgroup of the subgroup of order 7. The minimum-order
bound for a nontrivial five-action forces it to fix this subgroup pointwise,
contradicting containment in its own two-element fixed subgroup. Every action
is the original automorphism action or its literal restriction.

This gives the solvable-case exclusion of the candidate order
`2 ^ 6 * 3 * 5 * 7` in D. Parrott, *A characterization of the Tits simple
group* (1972), Lemma 2, printed p.673. It supplies the order obstruction
needed when the normalizer is solvable in the N₂ specialization, without
using the subgroup classification of GL(5,2).
-/

namespace Theory.GroupTheory

private theorem fixed_ne_top_of_faithful
    {A E : Type*} [Group A] [Finite A] [Group E] [MulDistribMulAction A E]
    [FaithfulSMul A E] (hA : Nat.card A ≠ 1) : FixedPoints.subgroup A E ≠ ⊤ := by
  intro h
  have htriv : ∀ a : A, a = 1 := by
    intro a
    apply FaithfulSMul.eq_of_smul_eq_smul (α := E)
    intro x
    have hx : x ∈ FixedPoints.subgroup A E := by rw [h]; trivial
    simpa using hx a
  have : Subsingleton A := ⟨fun a b => (htriv a).trans (htriv b).symm⟩
  exact hA (Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩)

private theorem fixed_card_of_prime_action
    {A E : Type*} [Group A] [Finite A] [Group E] [Finite E]
    [MulDistribMulAction A E] [FaithfulSMul A E]
    (p : ℕ) [Fact p.Prime] (hp : p = 5 ∨ p = 7)
    (hA : Nat.card A = p) (hE : Nat.card E = 32) :
    Nat.card (FixedPoints.subgroup A E) = if p = 5 then 2 else 4 := by
  have hmod := (IsPGroup.of_card (p := p) (n := 1) (by simpa using hA)).card_modEq_card_fixedPoints E
  change Nat.ModEq p (Nat.card E) (Nat.card (FixedPoints.subgroup A E)) at hmod
  have hdiv : Nat.card (FixedPoints.subgroup A E) ∣ 2 ^ 5 := by
    simpa [hE] using (FixedPoints.subgroup A E).card_subgroup_dvd_card
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hfixed := fixed_ne_top_of_faithful (E := E) (A := A)
    (show Nat.card A ≠ 1 by rcases hp with hp | hp <;> omega)
  have hn5 : n ≠ 5 := by
    intro hn5
    exact hfixed (Subgroup.eq_top_of_card_eq _ (by simpa [hn5, hE] using hcard))
  rw [hE, hcard] at hmod
  rcases hp with rfl | rfl <;> interval_cases n <;> norm_num [Nat.ModEq] at * <;> assumption

private theorem sylow_five_seven_of_card35
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 35)
    (P : Sylow 5 H) (Q : Sylow 7 H) :
    Nat.card P = 5 ∧ Nat.card Q = 7 ∧ P.toSubgroup.Normal ∧ Q.toSubgroup.Normal := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hP : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hH, show (35 : ℕ) = 5 * 7 by decide,
      Nat.factorization_mul (by decide) (by decide)]
    norm_num [(show Nat.Prime 5 by decide).factorization, (show Nat.Prime 7 by decide).factorization]
  have hQ : Nat.card Q = 7 := by
    rw [Q.card_eq_multiplicity, hH, show (35 : ℕ) = 5 * 7 by decide,
      Nat.factorization_mul (by decide) (by decide)]
    norm_num [(show Nat.Prime 5 by decide).factorization, (show Nat.Prime 7 by decide).factorization]
  have hPi : P.toSubgroup.index = 7 := by
    have h := P.toSubgroup.card_mul_index
    rw [hP, hH] at h
    omega
  have hQi : Q.toSubgroup.index = 5 := by
    have h := Q.toSubgroup.card_mul_index
    rw [hQ, hH] at h
    omega
  have hPcount : Nat.card (Sylow 5 H) = 1 := by
    have hd : Nat.card (Sylow 5 H) ∣ 7 := hPi ▸ P.card_dvd_index
    have hm := card_sylow_modEq_one 5 H
    rcases (show Nat.Prime 7 by decide).eq_one_or_self_of_dvd _ hd with h | h
    · exact h
    · norm_num [h, Nat.ModEq] at hm
  have hQcount : Nat.card (Sylow 7 H) = 1 := by
    have hd : Nat.card (Sylow 7 H) ∣ 5 := hQi ▸ Q.card_dvd_index
    have hm := card_sylow_modEq_one 7 H
    rcases (show Nat.Prime 5 by decide).eq_one_or_self_of_dvd _ hd with h | h
    · exact h
    · norm_num [h, Nat.ModEq] at hm
  let : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp hPcount).1
  let : Subsingleton (Sylow 7 H) := (Nat.card_eq_one_iff_unique.mp hQcount).1
  exact ⟨hP, hQ, P.normal_of_subsingleton, Q.normal_of_subsingleton⟩

private theorem not_card35_of_faithful_action32
    {H E : Type*} [Group H] [Finite H] [Group E] [Finite E]
    [MulDistribMulAction H E] [FaithfulSMul H E]
    (hE : Nat.card E = 32) : Nat.card H ≠ 35 := by
  intro hH
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let P : Sylow 5 H := Classical.choice inferInstance
  let Q : Sylow 7 H := Classical.choice inferInstance
  obtain ⟨hP, hQ, hPn, hQn⟩ := sylow_five_seven_of_card35 hH P Q
  let : P.toSubgroup.Normal := hPn
  let : Q.toSubgroup.Normal := hQn
  have hdisj : Disjoint P.toSubgroup Q.toSubgroup :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hP, hQ]; decide)
  have hcomm : ∀ p : P, ∀ q : Q, Commute (p : H) (q : H) := by
    intro p q
    exact Subgroup.commute_of_normal_of_disjoint _ _ hPn hQn hdisj p q p.property q.property
  let F : Subgroup E := FixedPoints.subgroup Q E
  have hF : Nat.card F = 4 := by
    simpa [F] using fixed_card_of_prime_action 7 (Or.inr rfl) hQ hE
  have hFP : Nat.card (FixedPoints.subgroup P E) = 2 := by
    simpa using fixed_card_of_prime_action 5 (Or.inl rfl) hP hE
  have hforward : ∀ p : P, ∀ x : E, x ∈ F → p • x ∈ F := by
    intro p x hx q
    change (q : H) • ((p : H) • x) = (p : H) • x
    rw [← mul_smul, (hcomm p q).eq.symm, mul_smul]
    exact congrArg (fun y => (p : H) • y) (hx q)
  let : IsInvariant P E F := ⟨fun p x => ⟨hforward p x, fun h => by
    simpa using hforward p⁻¹ (p • x) h⟩⟩
  have hfixed : FixedPoints.subgroup P F = ⊤ := by
    by_contra h
    have hbound := Theory.GroupAction.sixteen_le_card_of_five_action_nontrivial hP
      (IsPGroup.of_card (p := 2) (n := 2) (by simpa using hF)) h
    omega
  have hle : F ≤ FixedPoints.subgroup P E := by
    intro x hx p
    have hmem : (⟨x, hx⟩ : F) ∈ FixedPoints.subgroup P F := by rw [hfixed]; trivial
    exact congrArg Subtype.val (hmem p)
  have hbound := Subgroup.card_le_of_le hle
  rw [hF, hFP] at hbound
  omega

/-- A solvable automorphism subgroup of an elementary group of order 32 cannot have order 6720. -/
public theorem not_card6720_of_solvable_aut32
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (K : Subgroup (MulAut E))
    (hsolv : Group.IsSolvable K) : Nat.card K ≠ 6720 := by
  intro hK
  let _ : MulDistribMulAction Unit K := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  obtain ⟨H, hHall, _⟩ := exists_isHallSubgroup_isInvariant
    (G := K) (A := Unit) hsolv (by simp) {p : Nat.Primes | p.val = 5 ∨ p.val = 7}
  have htwo : ¬ 2 ∣ Nat.card H := by
    intro h
    have hbad : (2 : ℕ) = 5 ∨ 2 = 7 := hHall.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ h
    norm_num at hbad
  have hthree : ¬ 3 ∣ Nat.card H := by
    intro h
    have hbad : (3 : ℕ) = 5 ∨ 3 = 7 := hHall.p_in_pi_of_p_dvd_card ⟨3, by decide⟩ h
    norm_num at hbad
  have hfive : ¬ 5 ∣ H.index := by
    intro h
    exact hHall.p_in_pi_of_p_dvd_index ⟨5, by decide⟩ h (Or.inl rfl)
  have hseven : ¬ 7 ∣ H.index := by
    intro h
    exact hHall.p_in_pi_of_p_dvd_index ⟨7, by decide⟩ h (Or.inr rfl)
  have hcop : Nat.Coprime (Nat.card H) 192 := by
    have h2 := (Nat.prime_two.coprime_iff_not_dvd.mpr htwo).symm
    have h3 := ((show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr hthree).symm
    convert (h2.pow_right 6).mul_right h3 using 1
  have hd : Nat.card H ∣ 35 := by
    apply hcop.dvd_of_dvd_mul_left
    simpa [hK] using H.card_subgroup_dvd_card
  have hc : Nat.Coprime 35 H.index := by
    exact ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr hfive).mul_left
      ((show Nat.Prime 7 by decide).coprime_iff_not_dvd.mpr hseven)
  have hd' : 35 ∣ Nat.card H := by
    apply hc.dvd_of_dvd_mul_right
    rw [Subgroup.card_mul_index, hK]
    decide
  have hH : Nat.card H = 35 := Nat.dvd_antisymm hd hd'
  exact not_card35_of_faithful_action32 (H := H) hE hH

end Theory.GroupTheory
