module

public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.ElementaryEightSolvableCore
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# A lower bound for a solvable self-centralizing two-core

If 64 divides the order of a finite solvable group with self-centralizing
two-core, that core has order at least 16. Conjugation on its Frattini
quotient has kernel exactly the core. A core of order at most eight would
therefore give a solvable binary automorphism image with trivial two-core.
In dimensions below three its order is at most six; in dimension three
four-divisibility contradicts the elementary-eight two-core theorem.

This is the small-core reduction for the solvable case of Parrott,
*A characterization of the Tits' simple group* (1972), p.677, Lemma 6.
-/

open Subgroup

private theorem small_elementary_aut_card
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (k : ℕ) (hk : k ≤ 2) (hV : Nat.card V = 2 ^ k) :
    Nat.card (MulAut V) ≤ 6 := by
  interval_cases k
  · have : Subsingleton V := (Nat.card_eq_one_iff_unique.mp (by simpa using hV)).1
    have : Subsingleton (MulAut V) := ⟨fun a b => MulEquiv.ext (fun _ => Subsingleton.elim _ _)⟩
    rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩]
    decide
  · have hc : Nat.card V = 2 := by simpa using hV
    let : IsCyclic V := isCyclic_of_prime_card hc
    rw [IsCyclic.card_mulAut, hc]
    decide
  · have hc : Nat.card V = 4 := by simpa using hV
    let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    let : IsKleinFour V := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
    rw [IsKleinFour.card_mulAut V]

/-- Divisibility by 64 forces a self-centralizing two-core in a finite
solvable group to have order at least 16. -/
public theorem sixteen_le_card_two_core_of_solvable_self_centralizing
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (hcentral : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hdiv : 64 ∣ Nat.card G) : 16 ≤ Nat.card (pCore 2 G) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := pCore 2 G
  have hQ : IsPGroup 2 Q := pCore_isPGroup
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  let V := Q ⧸ frattini Q
  let : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini (p := 2)
  let action : G →* MulAut V := (quotientAut (frattini Q)).comp MulAut.conjNormal
  have hker : action.ker = Q := pCore_frattini_action_kernel 2 hcentral
  have hcount : Nat.card Q * Nat.card action.range = Nat.card G := by
    rw [← index_ker, hker]
    exact Q.card_mul_index
  let : Group.IsSolvable action.range :=
    Group.isSolvable_of_surjective action.rangeRestrict_surjective
  have hcore : Nat.card (pCore 2 action.range) = 1 := by
    have hh := action.rangeRestrict.card_pCore_of_ker_isPGroup
      action.rangeRestrict_surjective (by
        rw [MonoidHom.ker_rangeRestrict, hker]
        exact hQ)
    rw [MonoidHom.ker_rangeRestrict, hker] at hh
    have hpos : 0 < Nat.card Q := Nat.card_pos
    change Nat.card Q = Nat.card Q * Nat.card (pCore 2 action.range) at hh
    nlinarith
  by_contra! hsmall
  obtain ⟨j, hj⟩ := hQ.exists_card_eq
  have hjlt : j < 4 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [← hj] at hp
    norm_num at hp
    exact (not_le_of_gt hsmall) hp
  have hQle : Nat.card Q ≤ 8 := by
    rw [hj]
    exact Nat.pow_le_pow_right (by decide) (by omega : j ≤ 3)
  have hVle : Nat.card V ≤ Nat.card Q := Nat.le_of_dvd Nat.card_pos
    (Subgroup.card_quotient_dvd_card (frattini Q))
  obtain ⟨k, hk⟩ := (hQ.to_quotient (frattini Q)).exists_card_eq
  change Nat.card V = 2 ^ k at hk
  have hkle : k ≤ 3 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [← hk] at hp
    norm_num at hp
    omega
  by_cases hsmallV : k ≤ 2
  · have himage : Nat.card action.range ≤ 6 :=
      (Nat.card_le_card_of_injective _ Subtype.val_injective).trans
        (small_elementary_aut_card k hsmallV hk)
    have hGge := Nat.le_of_dvd Nat.card_pos hdiv
    nlinarith
  · have hk3 : k = 3 := by omega
    have hV : Nat.card V = 8 := by simpa [hk3] using hk
    have hQ8 : Nat.card Q = 8 := by omega
    have hfour : 4 ∣ Nat.card action.range := by
      obtain ⟨m, hm⟩ := hdiv
      rw [hQ8, hm] at hcount
      refine ⟨2 * m, ?_⟩
      omega
    have hbound := four_le_card_pCore_of_solvable_elementary_eight_automorphisms
      V hV action.range hfour
    omega

/-- Vanishing of the odd prime cores supplies the self-centralization
hypothesis through the solvable Fitting theorem. -/
public theorem sixteen_le_card_two_core_of_solvable_odd_cores_trivial
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → pCore p G = ⊥)
    (hdiv : 64 ∣ Nat.card G) : 16 ≤ Nat.card (pCore 2 G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfit : fittingSubgroup G = pCore 2 G := by
    apply le_antisymm
    · rw [fitting_eq_sup_pCore]
      refine iSup_le fun p => ?_
      by_cases hp : p.val.val = 2
      · rw [hp]
      · rw [hodd p.val.val (Nat.prime_of_mem_primeFactors p.val.property) hp]
        exact bot_le
    · exact pCore_le_fitting G 2
  apply sixteen_le_card_two_core_of_solvable_self_centralizing (hdiv := hdiv)
  rw [← hfit]
  exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance
