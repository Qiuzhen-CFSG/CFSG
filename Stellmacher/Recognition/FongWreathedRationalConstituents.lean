module

public import GorensteinWalter.LowNormVirtualCharacterDecomposition
public import GorensteinWalter.GeneralizedCharacterVirtual
public import Theory.Character.InvolutionSum
public import Mathlib.GroupTheory.Subgroup.Simple
public import Theory.Character.CharacterKernel
public import Theory.Character.UniqueDegreeRationality
public import Theory.Character.GaloisScalarProduct

/-!
# Fong's four rational constituents

A generalized character of norm four and principal coefficient one has three
other distinct signed irreducible constituents. Vanishing at the identity and
at the unique class of involutions, together with the involution-pair relation,
forces the signs to be `+,-,-`: the alternative gives a sum of three squares
whose vanishing places the involution in a nonprincipal character's kernel.

Galois automorphisms preserve the coefficients. They fix the unique positive
nonprincipal constituent and permute the negative pair. An exchange would make
the two negative degrees and involution values equal; equations (8) and (9)
then again put the involution in the positive constituent's kernel. Thus all
three characters are integer-valued. `FongRationalConstituents` records actual
characters and the integer and rational equations needed by the degree step.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), p.72, equations (8), (9) and the following
sum-of-squares and rationality arguments. The involution integrality calculation
adapts the private eigenvalue proof in `BenderGlauberman.TheoremC`.
-/

open scoped BigOperators
open Theory.Character BenderGlauberman
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G]

private theorem principal_irr : IsIrreducibleCharacter (1 : ClassFunction G) :=
  Section3.principalCharacter_isIrreducibleCharacterOnGroup

omit [Finite G] in
private theorem degree_nat {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    ∃ n : ℕ, 0 < n ∧ χ 1 = (n : ℂ) := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  let : Representation.IsIrreducible ρ := hρ
  let : Nontrivial (Fin n → ℂ) := irreducible_nontrivial ρ
  refine ⟨n, ?_, ?_⟩
  · simpa using Module.finrank_pos (R := ℂ) (M := Fin n → ℂ)
  · simp [Representation.char_one]

omit [Finite G] in
private theorem involution_int {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    {J : G} (hJ : orderOf J = 2) : ∃ z : ℤ, χ J = (z : ℂ) := by
  classical
  obtain ⟨n, ρ, _, rfl⟩ := hχ
  let f : Module.End ℂ (Fin n → ℂ) := ρ J
  have hpow : f ^ 2 = 1 := by
    change (ρ J) ^ 2 = 1
    rw [← map_pow, ← hJ, pow_orderOf_eq_one, map_one]
  have htrace := Representation.trace_pow_eq_sum_eigenvalues
    (f := f) (n := 2) (k := 1) (by norm_num) hpow
  simp only [pow_one] at htrace
  let m : f.Eigenvalues → ℤ := fun μ =>
    if (μ : ℂ) = 1 then Module.finrank ℂ (f.eigenspace (μ : ℂ))
    else -Module.finrank ℂ (f.eigenspace (μ : ℂ))
  refine ⟨∑ μ, m μ, ?_⟩
  rw [Representation.character, htrace, Int.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro μ _
  have hp : (μ : ℂ) ^ 2 = 1 :=
    Representation.eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
  rcases sq_eq_one_iff.mp hp with hμ | hμ
  · simp [m, hμ]
  · have hne : (μ : ℂ) ≠ 1 := by rw [hμ]; norm_num
    simp only [m, if_neg hne, Int.cast_neg]
    rw [hμ]
    norm_num

private theorem value_ne_degree [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hnp : χ ≠ 1) {g : G} (hg : g ≠ 1) :
    χ g ≠ χ 1 := by
  classical
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  have hi : IsIrreducibleCharacter ρ.character := ⟨n, ρ, hρ, rfl⟩
  obtain ⟨d, hd, hdegree⟩ := degree_nat hi
  have hker : ρ.ker = ⊥ := by
    rcases (MonoidHom.normal_ker ρ).eq_bot_or_eq_top with h | h
    · exact h
    have hc (x : G) : ρ.character x = (d : ℂ) := by
      rw [← hdegree]
      exact (ρ.mem_ker_iff_character_eq_degree x).mp (h ▸ Subgroup.mem_top x)
    have horth := scalarProduct_irreducible_orthogonal hi principal_irr hnp
    have hcard : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
    have hz : (d : ℂ) = 0 := by
      simpa [scalarProduct, hc, ← Nat.card_eq_fintype_card, hcard] using horth
    exact False.elim ((Nat.cast_ne_zero.mpr hd.ne' : (d : ℂ) ≠ 0) hz)
  intro he
  have hm := (ρ.mem_ker_iff_character_eq_degree g).mpr he
  rw [hker, Subgroup.mem_bot] at hm
  exact hg hm

private theorem signed_low_norm {Θ : ClassFunction G}
    (hΘ : IsGeneralizedCharacter Θ)
    (hprincipal : scalarProduct G Θ 1 = 1) (hnorm : scalarProduct G Θ Θ = 4) :
    ∃ (χ : Fin 3 → ClassFunction G) (ε : Fin 3 → ℂ),
      (∀ i, IsIrreducibleCharacter (χ i)) ∧ Function.Injective χ ∧
      (∀ i, χ i ≠ 1) ∧ (∀ i, ε i = 1 ∨ ε i = -1) ∧
      Θ = 1 + ε 0 • χ 0 + ε 1 • χ 1 + ε 2 • χ 2 := by
  obtain ⟨χ, ε, hi, hinj, hnp, hs, he⟩ :=
    GorensteinWalter.low_norm_virtual_character_decomposition Θ 3 (Or.inr rfl)
      (generalizedCharacter_isVirtualCharacter hΘ) hprincipal (by change scalarProduct G Θ Θ = (3 : ℂ) + 1; norm_num; exact hnorm)
  refine ⟨χ, ε, hi, hinj, hnp, hs, ?_⟩
  rw [he]
  ext g
  simp only [Section1.weightedFamilySum, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Section1.principalCharacter, Pi.one_apply]
  rw [show @Finset.univ (Fin 3) (Fintype.ofFinite (Fin 3)) =
    @Finset.univ (Fin 3) (Fin.fintype 3) by ext; simp]
  simp [Fin.sum_univ_succ, add_assoc]

omit [Finite G] in
private theorem degree_real {χ : ClassFunction G} (hi : IsIrreducibleCharacter χ) :
    χ 1 = ((χ 1).re : ℂ) := by
  obtain ⟨n, _, hn⟩ := degree_nat hi
  simp [hn]

omit [Finite G] in
private theorem involution_real {χ : ClassFunction G} (hi : IsIrreducibleCharacter χ)
    {J : G} (hJ : orderOf J = 2) : χ J = ((χ J).re : ℂ) := by
  obtain ⟨z, hz⟩ := involution_int hi hJ
  simp [hz]

private theorem signed_pair_identity {Θ : ClassFunction G} {J : G}
    (hJ : orderOf J = 2) (hfuse : ∀ u : G, orderOf u = 2 → IsConj u J)
    (χ : Fin 3 → ClassFunction G) (hi : ∀ i, IsIrreducibleCharacter (χ i))
    (ε : Fin 3 → ℂ)
    (he : Θ = 1 + ε 0 • χ 0 + ε 1 • χ 1 + ε 2 • χ 2)
    (hpair : scalarProduct G Θ (fun g => (involutionPairCount g : ℂ)) = 0) :
    1 + ε 0 * (χ 0 J ^ 2 / χ 0 1) + ε 1 * (χ 1 J ^ 2 / χ 1 1) +
      ε 2 * (χ 2 J ^ 2 / χ 2 1) = 0 := by
  rw [he] at hpair
  simp only [scalarProduct_add_left, scalarProduct_smul_left] at hpair
  rw [scalarProduct_irreducible_involutionPairCount_of_fusion J hJ hfuse _ principal_irr,
    scalarProduct_irreducible_involutionPairCount_of_fusion J hJ hfuse _ (hi 0),
    scalarProduct_irreducible_involutionPairCount_of_fusion J hJ hfuse _ (hi 1),
    scalarProduct_irreducible_involutionPairCount_of_fusion J hJ hfuse _ (hi 2)] at hpair
  have hg : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hc : (Nat.card (Subgroup.centralizer ({J} : Set G)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Subgroup.centralizer ({J} : Set G))).ne'
  apply (mul_eq_zero.mp (show
      ((Nat.card G : ℂ) / Nat.card (Subgroup.centralizer ({J} : Set G)) ^ 2) *
        (1 + ε 0 * (χ 0 J ^ 2 / χ 0 1) + ε 1 * (χ 1 J ^ 2 / χ 1 1) +
          ε 2 * (χ 2 J ^ 2 / χ 2 1)) = 0 from ?_)).resolve_left
      (div_ne_zero hg (pow_ne_zero _ hc))
  simp only [Pi.one_apply, one_pow, mul_one, div_one] at hpair
  convert hpair using 1
  ring

private theorem variance_zero (p q r a b c : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hd : 1 + p + q - r = 0) (ha : 1 + a + b - c = 0)
    (he : 1 + a ^ 2 / p + b ^ 2 / q - c ^ 2 / r = 0) : a = p := by
  have hr : 0 < r := by linarith
  have h := he
  field_simp at h
  have hv : q * (a - p) ^ 2 + p * (b - q) ^ 2 + (q * a - p * b) ^ 2 = 0 := by
    have hr' : r = 1 + p + q := by linarith
    have hc' : c = 1 + a + b := by linarith
    rw [hr', hc'] at h
    nlinarith only [h]
  have hnon : 0 ≤ p * (b - q) ^ 2 := mul_nonneg hp.le (sq_nonneg _)
  have ha0 : (a - p) ^ 2 = 0 := by
    nlinarith [sq_nonneg (q * a - p * b), sq_nonneg (a - p)]
  nlinarith [sq_nonneg (a - p)]

private theorem not_two_positive [IsSimpleGroup G]
    {A B C : ClassFunction G} (hA : IsIrreducibleCharacter A)
    (hB : IsIrreducibleCharacter B) (hC : IsIrreducibleCharacter C)
    (hAn : A ≠ 1) {J : G} (hJ : orderOf J = 2)
    (hd : 1 + A 1 + B 1 - C 1 = 0)
    (ha : 1 + A J + B J - C J = 0)
    (he : 1 + A J ^ 2 / A 1 + B J ^ 2 / B 1 - C J ^ 2 / C 1 = 0) : False := by
  have hp : 0 < (A 1).re := by
    obtain ⟨n, hn, he⟩ := degree_nat hA
    simpa [he] using (show (0 : ℝ) < n by exact_mod_cast hn)
  have hq : 0 < (B 1).re := by
    obtain ⟨n, hn, he⟩ := degree_nat hB
    simpa [he] using (show (0 : ℝ) < n by exact_mod_cast hn)
  have hdr : 1 + (A 1).re + (B 1).re - (C 1).re = 0 := by
    simpa using congrArg Complex.re hd
  have har : 1 + (A J).re + (B J).re - (C J).re = 0 := by
    simpa using congrArg Complex.re ha
  have her : 1 + (A J).re ^ 2 / (A 1).re + (B J).re ^ 2 / (B 1).re -
      (C J).re ^ 2 / (C 1).re = 0 := by
    rw [degree_real hA, degree_real hB, degree_real hC,
      involution_real hA hJ, involution_real hB hJ, involution_real hC hJ] at he
    exact_mod_cast he
  have hv := variance_zero _ _ _ _ _ _ hp hq hdr har her
  apply value_ne_degree hA hAn (show J ≠ 1 from by intro h; simp [h] at hJ)
  calc
    A J = ((A J).re : ℂ) := involution_real hA hJ
    _ = ((A 1).re : ℂ) := congrArg Complex.ofReal hv
    _ = A 1 := (degree_real hA).symm

/-- The involution-pair relation selects Fong's sign pattern. -/
public theorem fong_signed_constituents [IsSimpleGroup G] {Θ : ClassFunction G}
    (hΘ : IsGeneralizedCharacter Θ) (J : G) (hJ : orderOf J = 2)
    (hfuse : ∀ u : G, orderOf u = 2 → IsConj u J)
    (hprincipal : scalarProduct G Θ 1 = 1) (hnorm : scalarProduct G Θ Θ = 4)
    (hdegree : Θ 1 = 0) (hvalue : Θ J = 0)
    (hpair : scalarProduct G Θ (fun g => (involutionPairCount g : ℂ)) = 0) :
    ∃ A B C : ClassFunction G,
      IsIrreducibleCharacter A ∧ IsIrreducibleCharacter B ∧ IsIrreducibleCharacter C ∧
      A ≠ 1 ∧ B ≠ 1 ∧ C ≠ 1 ∧ A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ Θ = 1 + A - B - C := by
  classical
  obtain ⟨χ, ε, hi, hinj, hnp, hs, he⟩ := signed_low_norm hΘ hprincipal hnorm
  have hp := signed_pair_identity hJ hfuse χ hi ε he hpair
  have hd := hdegree
  have ha := hvalue
  rw [he] at hd ha
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at hd ha
  have h01 : χ 0 ≠ χ 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h)
  have h02 : χ 0 ≠ χ 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h)
  have h12 : χ 1 ≠ χ 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h)
  obtain ⟨n0, hn0, hd0⟩ := degree_nat (hi 0)
  obtain ⟨n1, hn1, hd1⟩ := degree_nat (hi 1)
  obtain ⟨n2, hn2, hd2⟩ := degree_nat (hi 2)
  rcases hs 0 with h0 | h0 <;> rcases hs 1 with h1 | h1 <;> rcases hs 2 with h2 | h2
  · simp only [h0, h1, h2, one_mul, hd0, hd1, hd2] at hd
    have hh := congrArg Complex.re hd
    simp only [Complex.add_re, Complex.one_re, Complex.natCast_re, Complex.zero_re] at hh
    exfalso
    have hp : (0 : ℝ) < 1 + n0 + n1 + n2 := by positivity
    linarith
  · exfalso
    apply not_two_positive (hi 0) (hi 1) (hi 2) (hnp 0) hJ
    · simpa [h0, h1, h2, sub_eq_add_neg] using hd
    · simpa [h0, h1, h2, sub_eq_add_neg] using ha
    · simpa [h0, h1, h2, sub_eq_add_neg] using hp
  · exfalso
    apply not_two_positive (hi 0) (hi 2) (hi 1) (hnp 0) hJ
    · simpa [h0, h1, h2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hd
    · simpa [h0, h1, h2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using ha
    · simpa [h0, h1, h2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hp
  · refine ⟨χ 0, χ 1, χ 2, hi 0, hi 1, hi 2, hnp 0, hnp 1, hnp 2, h01, h02, h12, ?_⟩
    simpa [h0, h1, h2, sub_eq_add_neg] using he
  · exfalso
    apply not_two_positive (hi 1) (hi 2) (hi 0) (hnp 1) hJ
    · simpa [h0, h1, h2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hd
    · simpa [h0, h1, h2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using ha
    · simpa [h0, h1, h2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hp
  · refine ⟨χ 1, χ 0, χ 2, hi 1, hi 0, hi 2, hnp 1, hnp 0, hnp 2, h01.symm, h12, h02, ?_⟩
    rw [he, h0, h1, h2]
    simp only [one_smul, neg_smul]
    abel
  · refine ⟨χ 2, χ 0, χ 1, hi 2, hi 0, hi 1, hnp 2, hnp 0, hnp 1, h02.symm, h12.symm, h01, ?_⟩
    rw [he, h0, h1, h2]
    simp only [one_smul, neg_smul]
    abel
  · simp only [h0, h1, h2, neg_one_mul, hd0, hd1, hd2] at hd
    have hh := congrArg Complex.re hd
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.natCast_re, Complex.zero_re] at hh
    have hh' : (1 : ℤ) + -(n0 : ℤ) + -(n1 : ℤ) + -(n2 : ℤ) = 0 := by exact_mod_cast hh
    omega

/-- Fong's equation (9), initially over the complex numbers. -/
public theorem fong_constituent_involution_identity {Θ A B C : ClassFunction G}
    (hA : IsIrreducibleCharacter A) (hB : IsIrreducibleCharacter B)
    (hC : IsIrreducibleCharacter C) (J : G) (hJ : orderOf J = 2)
    (hfuse : ∀ u : G, orderOf u = 2 → IsConj u J)
    (he : Θ = 1 + A - B - C)
    (hpair : scalarProduct G Θ (fun g => (involutionPairCount g : ℂ)) = 0) :
    1 + A J ^ 2 / A 1 = B J ^ 2 / B 1 + C J ^ 2 / C 1 := by
  have hi : ∀ i : Fin 3, IsIrreducibleCharacter (![A, B, C] i) := by
    intro i; fin_cases i <;> assumption
  have he' : Θ = 1 + (![1, -1, -1] : Fin 3 → ℂ) 0 • (![A,B,C] : Fin 3 → ClassFunction G) 0 +
      (![1, -1, -1] : Fin 3 → ℂ) 1 • (![A,B,C] : Fin 3 → ClassFunction G) 1 +
      (![1, -1, -1] : Fin 3 → ℂ) 2 • (![A,B,C] : Fin 3 → ClassFunction G) 2 := by
    simpa [sub_eq_add_neg] using he
  have hh := signed_pair_identity hJ hfuse _ hi _ he' hpair
  change 1 + 1 * (A J ^ 2 / A 1) + (-1) * (B J ^ 2 / B 1) +
    (-1) * (C J ^ 2 / C 1) = 0 at hh
  linear_combination hh

private theorem equal_negative_values_impossible [IsSimpleGroup G]
    {A B C : ClassFunction G} (hA : IsIrreducibleCharacter A)
    (hB : IsIrreducibleCharacter B) (hAn : A ≠ 1) {J : G} (hJ : orderOf J = 2)
    (hd : 1 + A 1 - B 1 - C 1 = 0) (ha : 1 + A J - B J - C J = 0)
    (he : 1 + A J ^ 2 / A 1 = B J ^ 2 / B 1 + C J ^ 2 / C 1)
    (hdeg : B 1 = C 1) (hval : B J = C J) : False := by
  rw [← hdeg, ← hval] at he
  rw [← hdeg] at hd
  rw [← hval] at ha
  have hp : (A 1).re ≠ 0 := by
    obtain ⟨n, hn, he⟩ := degree_nat hA
    simpa [he] using (show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne')
  have hq : (B 1).re ≠ 0 := by
    obtain ⟨n, hn, he⟩ := degree_nat hB
    simpa [he] using (show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne')
  have hdr : 1 + (A 1).re - (B 1).re - (B 1).re = 0 := by
    simpa using congrArg Complex.re hd
  have har : 1 + (A J).re - (B J).re - (B J).re = 0 := by
    simpa using congrArg Complex.re ha
  have her : 1 + (A J).re ^ 2 / (A 1).re =
      (B J).re ^ 2 / (B 1).re + (B J).re ^ 2 / (B 1).re := by
    rw [degree_real hA, degree_real hB, involution_real hA hJ, involution_real hB hJ] at he
    exact_mod_cast he
  field_simp at her
  have he1 : (A 1).re = 2 * (B 1).re - 1 := by linarith
  have heJ : (A J).re = 2 * (B J).re - 1 := by linarith
  rw [he1, heJ] at her
  have hv : (B J).re = (B 1).re := by nlinarith only [her, sq_nonneg ((B J).re - (B 1).re)]
  apply value_ne_degree hA hAn (show J ≠ 1 from by intro h; simp [h] at hJ)
  rw [degree_real hA, involution_real hA hJ]
  congr 1
  linarith

private theorem rational_constituents [IsSimpleGroup G]
    {Θ A B C : ClassFunction G} (hA : IsIrreducibleCharacter A)
    (hB : IsIrreducibleCharacter B) (hC : IsIrreducibleCharacter C)
    (hAn : A ≠ 1) (hBn : B ≠ 1)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hint : ∀ g, ∃ z : ℤ, Θ g = (z : ℂ))
    (he : Θ = 1 + A - B - C) {J : G} (hJ : orderOf J = 2)
    (hd : 1 + A 1 - B 1 - C 1 = 0) (ha : 1 + A J - B J - C J = 0)
    (hp : 1 + A J ^ 2 / A 1 = B J ^ 2 / B 1 + C J ^ 2 / C 1) :
    (∀ g, ∃ z : ℤ, A g = (z : ℂ)) ∧
      (∀ g, ∃ z : ℤ, B g = (z : ℂ)) ∧ (∀ g, ∃ z : ℤ, C g = (z : ℂ)) := by
  classical
  have coeff (ψ : ClassFunction G) (hi : IsIrreducibleCharacter ψ) (hn : ψ ≠ 1) :
      scalarProduct G Θ ψ = (if A = ψ then 1 else 0) -
        (if B = ψ then 1 else 0) - (if C = ψ then 1 else 0) := by
    rw [he, scalarProduct_sub_left, scalarProduct_sub_left, scalarProduct_add_left,
      scalarProduct_irr_ite principal_irr hi, scalarProduct_irr_ite hA hi,
      scalarProduct_irr_ite hB hi, scalarProduct_irr_ite hC hi]
    simp [hn.symm]
  have fixed (σ : ℂ ≃+* ℂ) : (fun g => σ (Θ g)) = Θ := by
    funext g
    obtain ⟨z, hz⟩ := hint g
    simp [hz]
  have transport (σ : ℂ ≃+* ℂ) {ψ : ClassFunction G} (hi : IsIrreducibleCharacter ψ) :
      scalarProduct G Θ (fun g => σ (ψ g)) = σ (scalarProduct G Θ ψ) := by
    rw [← hi.scalarProduct_comp_ringEquiv σ Θ, fixed σ]
  have nonprincipal (σ : ℂ ≃+* ℂ) {ψ : ClassFunction G} (hn : ψ ≠ 1) :
      (fun g => σ (ψ g)) ≠ (1 : ClassFunction G) := by
    intro hh
    apply hn
    funext g
    apply σ.injective
    simpa using congrFun hh g
  have fixedA (σ : ℂ ≃+* ℂ) : (fun g => σ (A g)) = A := by
    have hs := transport σ hA
    rw [coeff A hA hAn] at hs
    simp [hAB.symm, hAC.symm] at hs
    rw [coeff _ (hA.comp_ringEquiv σ) (nonprincipal σ hAn)] at hs
    by_contra hh
    rw [if_neg (Ne.symm hh)] at hs
    split_ifs at hs <;> norm_num at hs
  have orbitB (σ : ℂ ≃+* ℂ) : (fun g => σ (B g)) = B ∨ (fun g => σ (B g)) = C := by
    have hs := transport σ hB
    rw [coeff B hB hBn] at hs
    simp [hAB, hBC.symm] at hs
    rw [coeff _ (hB.comp_ringEquiv σ) (nonprincipal σ hBn)] at hs
    by_cases hb : (fun g => σ (B g)) = B
    · exact Or.inl hb
    by_cases hc : (fun g => σ (B g)) = C
    · exact Or.inr hc
    rw [if_neg (Ne.symm hb), if_neg (Ne.symm hc)] at hs
    split_ifs at hs <;> norm_num at hs
  have fixedB (σ : ℂ ≃+* ℂ) : (fun g => σ (B g)) = B := by
    rcases orbitB σ with hb | hc
    · exact hb
    exfalso
    have hdeg : B 1 = C 1 := (hB.ringEquiv_degree σ).symm.trans (congrFun hc 1)
    have hval : B J = C J := by
      obtain ⟨z, hz⟩ := involution_int hB hJ
      have hh := congrFun hc J
      simpa [hz] using hh
    exact equal_negative_values_impossible hA hB hAn hJ hd ha hp hdeg hval
  have fixedC (σ : ℂ ≃+* ℂ) : (fun g => σ (C g)) = C := by
    funext g
    have hh := congrFun (fixed σ) g
    rw [he] at hh
    simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply, map_sub, map_add, map_one] at hh
    rw [congrFun (fixedA σ) g, congrFun (fixedB σ) g] at hh
    linear_combination -hh
  exact ⟨hA.integer_of_fixed (fun σ g => congrFun (fixedA σ) g),
    hB.integer_of_fixed (fun σ g => congrFun (fixedB σ) g),
    hC.integer_of_fixed (fun σ g => congrFun (fixedC σ) g)⟩

/-- The four rational constituents in Fong's first exceptional character.
The principal constituent is the constant function one; the other three
are actual irreducible characters, with integer degree and involution value.
The last three fields are equations (8) and (9) of Fong, p.72. -/
public structure FongRationalConstituents (Θ : ClassFunction G) (J : G) where
  χ₂ : ClassFunction G
  χ₃ : ClassFunction G
  χ₄ : ClassFunction G
  irreducible : IsIrreducibleCharacter χ₂ ∧ IsIrreducibleCharacter χ₃ ∧
    IsIrreducibleCharacter χ₄
  nonprincipal : χ₂ ≠ 1 ∧ χ₃ ≠ 1 ∧ χ₄ ≠ 1
  distinct : χ₂ ≠ χ₃ ∧ χ₂ ≠ χ₄ ∧ χ₃ ≠ χ₄
  integer_values : (∀ g, ∃ z : ℤ, χ₂ g = (z : ℂ)) ∧
    (∀ g, ∃ z : ℤ, χ₃ g = (z : ℂ)) ∧ (∀ g, ∃ z : ℤ, χ₄ g = (z : ℂ))
  decomposition : Θ = 1 + χ₂ - χ₃ - χ₄
  d₂ : ℤ
  d₃ : ℤ
  d₄ : ℤ
  a₂ : ℤ
  a₃ : ℤ
  a₄ : ℤ
  degrees : χ₂ 1 = (d₂ : ℂ) ∧ χ₃ 1 = (d₃ : ℂ) ∧ χ₄ 1 = (d₄ : ℂ)
  involution_values : χ₂ J = (a₂ : ℂ) ∧ χ₃ J = (a₃ : ℂ) ∧ χ₄ J = (a₄ : ℂ)
  positive_degrees : 0 < d₂ ∧ 0 < d₃ ∧ 0 < d₄
  degree_equation : 1 + d₂ - d₃ - d₄ = 0
  involution_equation : 1 + a₂ - a₃ - a₄ = 0
  rational_identity : 1 + (a₂ : ℚ) ^ 2 / d₂ = (a₃ : ℚ) ^ 2 / d₃ + (a₄ : ℚ) ^ 2 / d₄

/-- Extract Fong's rational four-constituent packet from the explicit
norm, vanishing, and involution-pair data of the first exceptional character.
Simplicity suffices: the nonsolvability hypothesis of the application is
not needed for this extraction. -/
public theorem fong_rational_constituents [IsSimpleGroup G] {Θ : ClassFunction G}
    (hΘ : IsGeneralizedCharacter Θ) (hint : ∀ g, ∃ z : ℤ, Θ g = (z : ℂ))
    (J : G) (hJ : orderOf J = 2) (hfuse : ∀ u : G, orderOf u = 2 → IsConj u J)
    (hprincipal : scalarProduct G Θ 1 = 1) (hnorm : scalarProduct G Θ Θ = 4)
    (hdegree : Θ 1 = 0) (hvalue : Θ J = 0)
    (hpair : scalarProduct G Θ (fun g => (involutionPairCount g : ℂ)) = 0) :
    Nonempty (FongRationalConstituents Θ J) := by
  obtain ⟨A, B, C, hA, hB, hC, hAn, hBn, hCn, hAB, hAC, hBC, he⟩ :=
    fong_signed_constituents hΘ J hJ hfuse hprincipal hnorm hdegree hvalue hpair
  have hd : 1 + A 1 - B 1 - C 1 = 0 := by
    simpa only [he, Pi.sub_apply, Pi.add_apply, Pi.one_apply] using hdegree
  have ha : 1 + A J - B J - C J = 0 := by
    simpa only [he, Pi.sub_apply, Pi.add_apply, Pi.one_apply] using hvalue
  have hp := fong_constituent_involution_identity hA hB hC J hJ hfuse he hpair
  obtain ⟨hintA, hintB, hintC⟩ := rational_constituents hA hB hC hAn hBn
    hAB hAC hBC hint he hJ hd ha hp
  obtain ⟨d₂, hd₂⟩ := hintA 1
  obtain ⟨d₃, hd₃⟩ := hintB 1
  obtain ⟨d₄, hd₄⟩ := hintC 1
  obtain ⟨a₂, ha₂⟩ := hintA J
  obtain ⟨a₃, ha₃⟩ := hintB J
  obtain ⟨a₄, ha₄⟩ := hintC J
  have positive {χ : ClassFunction G} (hi : IsIrreducibleCharacter χ)
      {d : ℤ} (hd : χ 1 = (d : ℂ)) : 0 < d := by
    obtain ⟨n, hn, he⟩ := degree_nat hi
    have hnd : (n : ℤ) = d := by exact_mod_cast he.symm.trans hd
    rw [← hnd]
    exact_mod_cast hn
  refine ⟨{ χ₂ := A, χ₃ := B, χ₄ := C
            irreducible := ⟨hA, hB, hC⟩
            nonprincipal := ⟨hAn, hBn, hCn⟩
            distinct := ⟨hAB, hAC, hBC⟩
            integer_values := ⟨hintA, hintB, hintC⟩
            decomposition := he
            d₂ := d₂, d₃ := d₃, d₄ := d₄
            a₂ := a₂, a₃ := a₃, a₄ := a₄
            degrees := ⟨hd₂, hd₃, hd₄⟩
            involution_values := ⟨ha₂, ha₃, ha₄⟩
            positive_degrees := ⟨positive hA hd₂, positive hB hd₃, positive hC hd₄⟩
            degree_equation := ?_
            involution_equation := ?_
            rational_identity := ?_ }⟩
  · rw [hd₂, hd₃, hd₄] at hd
    exact_mod_cast hd
  · rw [ha₂, ha₃, ha₄] at ha
    exact_mod_cast ha
  · rw [hd₂, hd₃, hd₄, ha₂, ha₃, ha₄] at hp
    exact_mod_cast hp

end Stellmacher.Recognition
