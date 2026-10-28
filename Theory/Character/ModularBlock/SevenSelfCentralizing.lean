module

public import Theory.Character.ModularBlock.PrimeCongruence
public import Theory.Character.CharacterValues
public import Theory.GroupTheory.PrimeOrderSylowCentralizer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.FieldSimp

/-!
# Prime-to-seven rows at a self-centralizing Sylow subgroup

The central-character definition of an ordinary congruence block gives a
short proof of the principal-block assertion in the cyclic prime case.  At a
`p`-regular class the class size is divisible by `p`; at a `p`-singular class,
self-centralization forces the element to have order `p`, and the ordinary
character congruence at a commuting prime-order element supplies the required
central-character congruence.

Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from `PrimeOrderSelfCentralizing`, whose source is
Alperin--Brauer--Gorenstein III.8, Proposition 5, p.117.
-/

public section
noncomputable section

open ModularBlock
open ModularBlock.BlockPreliminaries
open ModularBlock.PrimeBlockConstruction
open ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData

namespace ModularBlock.PrimeBlockConstruction

variable {G : Type*} [Group G] [Finite G]

private theorem natCast_mem_iff_of_liesOver
    {p : ℕ} {A : Type*} [CommRing A] (P : Ideal A)
    (hP : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) (n : ℕ) :
    (n : A) ∈ P ↔ p ∣ n := by
  have h := Ideal.mem_of_liesOver P (Ideal.span ({(p : ℤ)} : Set ℤ)) (n : ℤ)
  have h' : (algebraMap ℤ A) (n : ℤ) ∈ P ↔ p ∣ n := by
    simpa only [Ideal.mem_span_singleton, Int.natCast_dvd_natCast] using h.symm
  convert h' using 1
  norm_cast

private theorem one_sub_primitive_root_mem
    {p : ℕ} [Fact p.Prime]
    {η ξ : ℂ}
    (hξ : IsPrimitiveRoot ξ p) (hξA : ξ ∈ cyclotomicOrder η)
    (P : Ideal (cyclotomicOrder η)) (_hPmax : P.IsMaximal)
    (hP : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) :
    (⟨1 - ξ, (cyclotomicOrder η).sub_mem (cyclotomicOrder η).one_mem hξA⟩ :
      cyclotomicOrder η) ∈ P := by
  let Aη := cyclotomicOrder η
  let : P.IsMaximal := _hPmax
  let : Field (Aη ⧸ P) := Ideal.Quotient.field P
  let : CharP (Aη ⧸ P) p := (charP_iff _ _).mpr (by
    intro n
    change Ideal.Quotient.mk P (n : Aη) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, natCast_mem_iff_of_liesOver P hP n])
  let ξA : Aη := ⟨ξ, hξA⟩
  have hpow : (Ideal.Quotient.mk P ξA) ^ p = 1 := by
    rw [← map_pow]
    change Ideal.Quotient.mk P (ξA ^ p) = 1
    rw [show ξA ^ p = 1 by apply Subtype.ext; simpa [ξA] using hξ.pow_eq_one, map_one]
  have hzero : (Ideal.Quotient.mk P ξA - 1) ^ p = 0 := by
    rw [sub_pow_char]
    rw [hpow]
    simp
  have hz : Ideal.Quotient.mk P ξA - 1 = 0 :=
    (pow_eq_zero_iff (show p ≠ 0 from (inferInstance : Fact (Nat.Prime p)).out.ne_zero)).mp hzero
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk P (1 - ξA) = 0
  rw [map_sub, map_one]
  exact sub_eq_zero.mpr (sub_eq_zero.mp hz).symm

private theorem natCast_ne_zero_mod_liesOver
    {p n : ℕ} [Fact p.Prime] {A : Type*} [CommRing A]
    (P : Ideal A) (_hPmax : P.IsMaximal)
    (hP : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
    (hn : ¬ p ∣ n) : Ideal.Quotient.mk P (n : A) ≠ 0 := by
  intro h
  have hm : (n : A) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp h
  exact hn ((natCast_mem_iff_of_liesOver P hP n).mp hm)

private theorem centralizer_eq_of_prime_card
    {p : ℕ} [Fact p.Prime] (P : Subgroup G) (hPcard : Nat.card P = p)
    (hC : Subgroup.centralizer (P : Set G) = P) (u : P) (hu : u ≠ 1) :
    Subgroup.centralizer ({(u : G)} : Set G) = P := by
  have huorder : orderOf (u : G) = p := by
    exact (Subgroup.orderOf_coe u).trans (orderOf_eq_prime
      (by simpa [hPcard] using (pow_card_eq_one' (x := u))) hu)
  have hz : Subgroup.zpowers (u : G) = P := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr u.property)
    · rw [Nat.card_zpowers, huorder]
      exact hPcard.le
  calc
    Subgroup.centralizer ({(u : G)} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    _ = Subgroup.centralizer (P : Set G) := by rw [hz]
    _ = P := hC

private theorem classSize_mul_centralizer_eq_card (g : G) :
    Nat.card (ConjClasses.mk g).carrier *
        Nat.card (Subgroup.centralizer ({g} : Set G)) = Nat.card G := by
  have h := class_card_mul_centralizer_card (G := G) g
  let e : {x : G // x * g = g * x} ≃
      ↥(Subgroup.centralizer ({g} : Set G)) := {
    toFun x := ⟨x.1, by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact x.2.symm⟩
    invFun x := ⟨x.1, by
      have hx := x.2
      rw [Subgroup.mem_centralizer_iff] at hx
      exact (hx g (by simp)).symm⟩
    left_inv x := by rfl
    right_inv x := by rfl }
  simpa only [show Nat.card {x : G // x * g = g * x} =
      Nat.card ↥(Subgroup.centralizer ({g} : Set G)) from Nat.card_congr e] using h

private theorem centralizer_card_not_dvd_of_regular_ne_one
    (P : Sylow 7 G) (hPcard : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    {g : G} (hg : g ≠ 1) (hsing : ¬ 7 ∣ orderOf g) :
    ¬ 7 ∣ Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hdiv
  obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' 7 hdiv
  have hxorderG : orderOf (x : G) = 7 := by
    simpa only [Subgroup.orderOf_coe] using hxorder
  obtain ⟨y, hy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow
    (n := 1) (by simpa [hxorderG])
  obtain ⟨t, ht⟩ := isConj_iff.mp hy
  change (MulAut.conj t) (x : G) = (y : G) at ht
  let z : G := (MulAut.conj t) g
  have hcomm : (y : G) * z = z * (y : G) := by
    have hxg : g * (x : G) = (x : G) * g := by
      have hx := x.property
      rw [Subgroup.mem_centralizer_iff] at hx
      exact hx g (by simp)
    have := congrArg (MulAut.conj t) hxg
    simpa [z, ht, map_mul] using this.symm
  have hyne : y ≠ 1 := by
    intro h
    have : orderOf (MulAut.conj t (x : G)) = orderOf (1 : G) := by simp [ht, h]
    rw [(MulAut.conj t).orderOf_eq] at this
    rw [hxorderG] at this
    norm_num at this
  have hcy := centralizer_eq_of_prime_card (P := (P : Subgroup G))
    hPcard hC y hyne
  have hzP : z ∈ (P : Subgroup G) := by
    rw [← hcy, Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hcomm
  have horderdiv : orderOf z ∣ 7 := by
    simpa [hPcard, Subgroup.orderOf_mk] using
      (orderOf_dvd_natCard (⟨z, hzP⟩ : (P : Subgroup G)))
  have hz_ne : z ≠ 1 := by
    intro hz
    apply hg
    apply (MulAut.conj t).injective
    simpa [z] using hz
  have hzorder : orderOf z = 7 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp horderdiv).resolve_left
      (by
        intro hone
        apply hz_ne
        exact orderOf_eq_one_iff.mp hone)
  apply hsing
  have htransport : orderOf z = orderOf g := by
    simpa [z] using (MulAut.conj t).orderOf_eq g
  rw [← htransport, hzorder]

private theorem centralCharacter_diff_mem_of_mul_diff_mem
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (P : Ideal (cyclotomicOrder η)) (χ : ConjClassFunction G)
    (hχ : IsIrreducibleConjCharacter χ) {n : ℕ}
    (C : ConjClasses G)
    (hn : ¬ 7 ∣ n)
    (hPmax : P.IsMaximal)
    (hP : P.LiesOver (Ideal.span ({(7 : ℤ)} : Set ℤ)))
    {a : cyclotomicOrder η}
    (ha : (n : cyclotomicOrder η) *
        (centralCharacterInCyclotomicOrder hη χ hχ C -
          (Nat.card C.carrier : cyclotomicOrder η)) = a)
    (haP : a ∈ P) :
    centralCharacterInCyclotomicOrder hη χ hχ C -
      (Nat.card C.carrier : cyclotomicOrder η) ∈ P := by
  let : P.IsMaximal := hPmax
  let : Field (cyclotomicOrder η ⧸ P) := Ideal.Quotient.field P
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hnc : Ideal.Quotient.mk P (n : cyclotomicOrder η) ≠ 0 := by
    exact natCast_ne_zero_mod_liesOver (p := 7) P hPmax hP hn
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (mul_eq_zero.mp ?_).resolve_left hnc
  rw [← map_mul]
  rw [ha]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr haP

/-- A character whose degree is prime to seven belongs to the principal
seven-block attached to any chosen prime above seven, provided the
Sylow subgroup of order seven is self-centralizing. -/
public theorem mem_block_of_prime_to_seven_degree
    (P : Sylow 7 G) (hPcard : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (d : PrimeCongruenceBlockData 7 G) (i : d.I) (n : ℕ)
    (hd : d.chi i (ConjClasses.mk 1) = (n : ℂ))
    (hn : ¬ 7 ∣ n) : i ∈ d.block := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply (mem_blockOf_iff_centralCharacter d i d.principal).2
  intro C
  rcases d.complete.1 i with hχ
  obtain ⟨m, ρ, hρχ⟩ := hχ.1
  have hρirr : Representation.IsIrreducible ρ := by
    exact (irreducible_iff_character_norm_one (ρ := ρ)).2 (by simpa [hρχ] using hχ.2)
  let := hρirr
  have hcharDegree : d.chi i (ConjClasses.mk 1) = ρ.character 1 := by
    rw [hρχ]
    rfl
  have hn0 : n ≠ 0 := by
    have hmpos : 0 < m := by
      let := irreducible_nontrivial ρ
      have hp' : 0 < Module.finrank ℂ (Fin m → ℂ) :=
        Module.finrank_pos_iff.mpr (inferInstance : Nontrivial (Fin m → ℂ))
      simpa using hp'
    have hdegne : ρ.character 1 ≠ 0 := by
      let := irreducible_nontrivial ρ
      rw [Representation.char_one]
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (by simpa using hmpos))
    intro hn0
    apply hdegne
    rw [← hcharDegree, hd, hn0]
    simp
  obtain ⟨g, hg⟩ := ConjClasses.exists_rep C
  subst C
  have hχg : d.chi i (ConjClasses.mk g) = ρ.character g := by
    rw [hρχ]
    rfl
  let χg : cyclotomicOrder d.eta := ⟨d.chi i (ConjClasses.mk g), by
    rw [hχg]
    exact representation_character_mem_cyclotomicOrder d.eta_spec ρ g⟩
  let cc := centralCharacterInCyclotomicOrder d.eta_spec (d.chi i) hχ
    (ConjClasses.mk g)
  let a : cyclotomicOrder d.eta := (n : cyclotomicOrder d.eta) *
    (cc - (Nat.card (ConjClasses.mk g).carrier : cyclotomicOrder d.eta))
  have ha : (n : cyclotomicOrder d.eta) *
      (centralCharacterInCyclotomicOrder d.eta_spec (d.chi i) hχ
        (ConjClasses.mk g) - (Nat.card (ConjClasses.mk g).carrier : cyclotomicOrder d.eta)) = a := by
    rfl
  have hid : a = (Nat.card (ConjClasses.mk g).carrier : cyclotomicOrder d.eta) *
      (χg - (n : cyclotomicOrder d.eta)) := by
    apply Subtype.ext
    simp [a, cc, χg, centralCharacterInCyclotomicOrder,
      ordinaryCentralCharacterValue, hd]
    field_simp [hn0]
  have hprincipalχ : IsIrreducibleConjCharacter (d.chi d.principal) :=
    d.complete.1 d.principal
  have hprincipalCC : centralCharacterInCyclotomicOrder d.eta_spec
      (d.chi d.principal) hprincipalχ (ConjClasses.mk g) =
      (Nat.card (ConjClasses.mk g).carrier : cyclotomicOrder d.eta) := by
    apply Subtype.ext
    simp [centralCharacterInCyclotomicOrder, ordinaryCentralCharacterValue,
      d.principal_eq, PrincipalBlockConstruction.ordinaryPrincipalCharacter]
  rw [hprincipalCC]
  by_cases hsing : 7 ∣ orderOf g
  · have horder : orderOf g = 7 := by
      obtain ⟨q, hq⟩ := hsing
      have hqpos : 0 < q := by
        have ho := orderOf_pos g
        rw [hq] at ho
        omega
      by_cases hq1 : q = 1
      · simpa [hq1] using hq
      · have hqgt : 1 < q := by omega
        have hne := Sylow.orderOf_ne_prime_mul_of_self_centralizing
          P hPcard hC hqgt g
        exact False.elim (hne (by simpa [Nat.mul_comm] using hq))
    have hξ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 7)) 7 :=
      Complex.isPrimitiveRoot_exp 7 (by decide)
    have hξA : Complex.exp (2 * Real.pi * Complex.I / 7) ∈ cyclotomicOrder d.eta := by
      exact primitive_root_mem_cyclotomicOrder_of_dvd d.eta_spec
        (Nat.card_pos (α := G)).ne' hξ (by simpa [horder] using orderOf_dvd_natCard g)
    obtain ⟨hgm, h1m, hcong⟩ := representation_character_congruent_at_mul
      (x := g) (y := 1) hξ (by decide) d.eta_spec hξA ρ horder (by simp)
    have hdiff : (⟨ρ.character g, by simpa only [mul_one] using hgm⟩ : cyclotomicOrder d.eta) -
        ⟨ρ.character 1, h1m⟩ ∈ d.primeIdeal := by
      have hmem := one_sub_primitive_root_mem hξ hξA d.primeIdeal
        d.primeIdeal_maximal d.primeIdeal_liesOver
      have hc := hcong
      change congruentModIn _ _ _ _ at hc
      rw [congruentModIn_iff_dvd] at hc
      rcases hc with ⟨z, hz⟩
      have hz' : (⟨ρ.character g, by simpa only [mul_one] using hgm⟩ :
          cyclotomicOrder d.eta) - ⟨ρ.character 1, h1m⟩ =
          ⟨1 - Complex.exp (2 * Real.pi * Complex.I / 7),
            (cyclotomicOrder d.eta).sub_mem (cyclotomicOrder d.eta).one_mem hξA⟩ * z := by
        simpa only [mul_one] using hz
      rw [hz']
      exact d.primeIdeal.mul_mem_right _ hmem
    have hmn : (m : cyclotomicOrder d.eta) = (n : cyclotomicOrder d.eta) := by
      apply Subtype.ext
      calc
        (m : ℂ) = ρ.character 1 := by
          rw [Representation.char_one]
          simp
        _ = d.chi i (ConjClasses.mk 1) := hcharDegree.symm
        _ = (n : ℂ) := hd
    have h1eq : (⟨ρ.character 1, h1m⟩ : cyclotomicOrder d.eta) =
        (m : cyclotomicOrder d.eta) := by
      apply Subtype.ext
      simp [Representation.char_one]
    have hdelta : χg - (n : cyclotomicOrder d.eta) ∈ d.primeIdeal := by
      rw [← hmn]
      rw [h1eq] at hdiff
      simpa [χg, hχg, hρχ] using hdiff
    have haP : a ∈ d.primeIdeal := by
      rw [hid]
      exact d.primeIdeal.mul_mem_left _ hdelta
    exact centralCharacter_diff_mem_of_mul_diff_mem d.eta_spec d.primeIdeal
      (d.chi i) hχ (ConjClasses.mk g) hn d.primeIdeal_maximal
      d.primeIdeal_liesOver ha haP
  · have hmul := classSize_mul_centralizer_eq_card (G := G) g
    have hpG : 7 ∣ Nat.card G := by
      exact hPcard ▸ (Subgroup.card_subgroup_dvd_card (P : Subgroup G))
    by_cases hg1 : g = 1
    · subst g
      have hdelta : χg - (n : cyclotomicOrder d.eta) = 0 := by
        apply Subtype.ext
        simp [χg, hd]
      have haP : a ∈ d.primeIdeal := by
        rw [hid, hdelta]
        simp
      exact centralCharacter_diff_mem_of_mul_diff_mem d.eta_spec d.primeIdeal
        (d.chi i) hχ (ConjClasses.mk (1 : G)) hn d.primeIdeal_maximal
        d.primeIdeal_liesOver ha haP
    have hcent_not : ¬ 7 ∣ Nat.card (Subgroup.centralizer ({g} : Set G)) :=
      centralizer_card_not_dvd_of_regular_ne_one P hPcard hC hg1 hsing
    have hclass : 7 ∣ Nat.card (ConjClasses.mk g).carrier :=
      ((Nat.Prime.dvd_mul (by decide : Nat.Prime 7)).mp
        (show 7 ∣ Nat.card (ConjClasses.mk g).carrier *
          Nat.card (Subgroup.centralizer ({g} : Set G)) from by rw [hmul]; exact hpG)).resolve_right hcent_not
    have hclassA : (Nat.card (ConjClasses.mk g).carrier : cyclotomicOrder d.eta) ∈
        d.primeIdeal := (natCast_mem_iff_of_liesOver d.primeIdeal
          d.primeIdeal_liesOver _).2 hclass
    have haP : a ∈ d.primeIdeal := by
      rw [hid]
      exact d.primeIdeal.mul_mem_right _ hclassA
    exact centralCharacter_diff_mem_of_mul_diff_mem d.eta_spec d.primeIdeal
      (d.chi i) hχ (ConjClasses.mk g) hn d.primeIdeal_maximal
      d.primeIdeal_liesOver ha haP

end ModularBlock.PrimeBlockConstruction
