module
public import ABG.Recognition.ThreeCharacterPath

/-!
# The seven-character form of Wong's five induced functions

This interface keeps the seven genuine irreducibles, their distinctness and
nontriviality, the four signs, and the five identities together. Orthogonality
then shows that an irreducible outside this one catalog is absent from all five
functions. To extend the four-character path, integral coefficients and the
Gram matrix constrain the path projections. Positivity of irreducible degrees
selects one path constituent in each norm-three function. The two norm-two
residuals share exactly one signed constituent, supplying three new characters.

Source: Wong (1964), equation (3), p.98 and the Appendix, p.106.
-/

namespace ABG
open BenderGlauberman
open scoped BigOperators

/-- One shared set of witnesses for all five identities in Wong's equation (3).
The indices of `χ` and `sign` start at zero. -/
public structure ThreeCharacterDecomposition {G : Type*} [Group G]
    (Ψ : Fin 5 → ClassFunction G) where
  χ : Fin 7 → ClassFunction G
  irreducible : ∀ i, IsIrreducibleCharacter (χ i)
  distinct : Function.Injective χ
  nontrivial : ∀ i, χ i ≠ 1
  sign : Fin 4 → ℤ
  sign_unit : ∀ i, sign i = 1 ∨ sign i = -1
  first : Ψ 0 = 1 + (sign 0 : ℂ) • (χ 0 - χ 1)
  second : Ψ 1 = (sign 0 : ℂ) • (χ 0 - χ 2)
  third : Ψ 2 = (sign 0 : ℂ) • (χ 2 - χ 3)
  fourth : Ψ 3 = (sign 0 : ℂ) • χ 1 + (sign 1 : ℂ) • χ 4 + (sign 2 : ℂ) • χ 5
  fifth : Ψ 4 = (sign 0 : ℂ) • χ 0 + (sign 1 : ℂ) • χ 4 + (sign 3 : ℂ) • χ 6

public theorem ThreeCharacterDecomposition.orthogonal_of_not_mem
    {G : Type*} [Group G] [Fintype G] {Ψ : Fin 5 → ClassFunction G}
    (d : ThreeCharacterDecomposition Ψ) {θ : ClassFunction G}
    (hθ : IsIrreducibleCharacter θ) (h1 : θ ≠ 1) (hχ : ∀ i, θ ≠ d.χ i)
    (k : Fin 5) : scalarProduct G θ (Ψ k) = 0 := by
  have ho (i : Fin 7) : scalarProduct G θ (d.χ i) = 0 :=
    irreducible_scalarProduct_of_ne hθ (d.irreducible i) (hχ i)
  have ht : scalarProduct G θ 1 = 0 :=
    irreducible_scalarProduct_of_ne hθ isLinearCharacter_one.1 h1
  fin_cases k <;>
    simp [d.first, d.second, d.third, d.fourth, d.fifth,
      scalarProduct_add_right, scalarProduct_sub_right, scalarProduct_smul_right, ho, ht]

private theorem path_projection {G : Type*} [Group G] [Fintype G]
    (χ : Fin 4 → ClassFunction G) (hi : ∀ i, IsIrreducibleCharacter (χ i))
    (hinj : Function.Injective χ) (R : ClassFunction G) (hn : normSq G R = 3)
    (hd : R 1 = 0) (e x : ℤ) (he : e = 1 ∨ e = -1) (j : Fin 4)
    (hc : ∀ i, scalarProduct G R (χ i) = ((if i = j then x + e else x : ℤ) : ℂ)) :
    x = 0 := by
  classical
  let c (i : Fin 4) : ℤ := if i = j then x + e else x
  let P : ClassFunction G := ∑ i, (c i : ℂ) • χ i
  have hc' (i : Fin 4) : scalarProduct G (χ i) R = (c i : ℂ) := by
    rw [← scalarProduct_conj, hc]
    simp only [star_intCast]; rfl
  have hPP : scalarProduct G P P = ∑ i, (c i : ℂ)^2 :=
    decomp_scalarProduct hi (fun i k h => fun h' => h (hinj h'))
  have hRP : scalarProduct G R P = ∑ i, (c i : ℂ)^2 := by
    simp only [P, scalarProduct_sum_right, scalarProduct_smul_right, hc, c,
      star_intCast, pow_two]
  have hPR : scalarProduct G P R = ∑ i, (c i : ℂ)^2 := by
    simp [P, scalarProduct_sum_left, scalarProduct_smul_left, hc', pow_two]
  have hs : (∑ i, (c i : ℂ)^2) = 4 * (x : ℂ)^2 + 2 * e * x + 1 := by
    have ht (i : Fin 4) : (c i : ℂ)^2 =
        (x : ℂ)^2 + if i = j then 2 * e * x + (e : ℂ)^2 else 0 := by
      by_cases h : i = j <;> simp [c, h]
      ring
    simp only [ht, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases he with rfl | rfl <;> norm_num <;> ring
  have hN : normSq G (R - P) = 2 - 4 * (x : ℂ)^2 - 2 * e * x := by
    change scalarProduct G (R - P) (R - P) = _
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right,
      hPP, hRP, hPR, hs]
    change normSq G R - _ - (_ - _) = _
    rw [hn]; ring
  have hb := normSq_nonneg (G := G) (R - P)
  rw [hN] at hb
  have hb' : (0 : ℤ) ≤ 2 - 4 * x^2 - 2 * e * x := by
    exact_mod_cast (by simpa [pow_two, Complex.mul_re] using hb : (0 : ℝ) ≤ 2 - 4 * (x : ℝ)^2 - 2 * e * x)
  have hx : x = 0 ∨ x = -e := by
    rcases he with rfl | rfl
    · have hl : -1 ≤ x := by nlinarith
      have hu : x ≤ 0 := by nlinarith
      omega
    · have hl : 0 ≤ x := by nlinarith
      have hu : x ≤ 1 := by nlinarith
      omega
  rcases hx with hx | hx
  · exact hx
  exfalso
  have hzero : R - P = 0 := (normSq_eq_zero_iff _).mp (by
    rw [hN, hx]; rcases he with rfl | rfl <;> norm_num)
  have hv := congrArg Complex.re (congrFun (sub_eq_zero.mp hzero) 1)
  have h0 := irreducible_degree_ge_one (hi 0)
  have h1 := irreducible_degree_ge_one (hi 1)
  have h2 := irreducible_degree_ge_one (hi 2)
  have h3 := irreducible_degree_ge_one (hi 3)
  fin_cases j <;> rcases he with rfl | rfl <;>
    simp [P, c, hx, Fin.sum_univ_four, hd] at hv <;> linarith

private theorem irr_product {G : Type*} [Group G] [Fintype G]
    {a b : ClassFunction G} (ha : IsIrreducibleCharacter a)
    (hb : IsIrreducibleCharacter b) :
    scalarProduct G a b = if a = b then 1 else 0 := by
  classical
  split_ifs with h
  · subst b; exact irreducible_scalarProduct_self ha
  · exact irreducible_scalarProduct_of_ne ha hb h

private theorem signed_pair {G : Type*} [Group G] [Fintype G]
    {R : ClassFunction G} (hg : IsGeneralizedCharacter R) (hn : normSq G R = 2) :
    ∃ a b : ClassFunction G, ∃ r s : ℤ,
      IsIrreducibleCharacter a ∧ IsIrreducibleCharacter b ∧ a ≠ b ∧
      (r = 1 ∨ r = -1) ∧ (s = 1 ∨ s = -1) ∧ R = (r : ℂ) • a + (s : ℂ) • b := by
  obtain ⟨a, b, ha, hb, hab, h⟩ := norm_two_pair hg hn
  rcases h with h | h | h | h
  · exact ⟨a,b,1,-1,ha,hb,hab,Or.inl rfl,Or.inr rfl,by simpa [sub_eq_add_neg] using h⟩
  · exact ⟨a,b,1,1,ha,hb,hab,Or.inl rfl,Or.inl rfl,by simpa using h⟩
  · exact ⟨a,b,-1,-1,ha,hb,hab,Or.inr rfl,Or.inr rfl,by simpa [sub_eq_add_neg] using h⟩
  · exact ⟨a,b,-1,1,ha,hb,hab,Or.inr rfl,Or.inl rfl,by simpa using h⟩

private theorem pair_orthogonal {G : Type*} [Group G] [Fintype G]
    {a b θ : ClassFunction G} (ha : IsIrreducibleCharacter a)
    (hb : IsIrreducibleCharacter b) (hθ : IsIrreducibleCharacter θ) (hab : a ≠ b)
    (r s : ℤ) (hr : r = 1 ∨ r = -1) (hs : s = 1 ∨ s = -1)
    (h : scalarProduct G ((r : ℂ) • a + (s : ℂ) • b) θ = 0) :
    a ≠ θ ∧ b ≠ θ := by
  simp only [scalarProduct_add_left, scalarProduct_smul_left] at h
  constructor
  · intro he; subst θ
    rw [irreducible_scalarProduct_self ha, irreducible_scalarProduct_of_ne hb ha hab.symm] at h
    rcases hr with rfl | rfl <;> norm_num at h
  · intro he; subst θ
    rw [irreducible_scalarProduct_self hb, irreducible_scalarProduct_of_ne ha hb hab] at h
    rcases hs with rfl | rfl <;> norm_num at h

private theorem pair_overlap {G : Type*} [Group G] [Fintype G]
    {a b c d : ClassFunction G}
    (ha : IsIrreducibleCharacter a) (hb : IsIrreducibleCharacter b)
    (hc : IsIrreducibleCharacter c) (hd : IsIrreducibleCharacter d)
    (hab : a ≠ b) (hcd : c ≠ d)
    (r s t u : ℤ) (hr : r = 1 ∨ r = -1) (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) (hu : u = 1 ∨ u = -1)
    (h : scalarProduct G ((r : ℂ) • a + (s : ℂ) • b)
      ((t : ℂ) • c + (u : ℂ) • d) = 1) :
    (a = c ∧ r = t ∧ b ≠ d) ∨ (a = d ∧ r = u ∧ b ≠ c) ∨
    (b = c ∧ s = t ∧ a ≠ d) ∨ (b = d ∧ s = u ∧ a ≠ c) := by
  classical
  simp only [scalarProduct_add_left, scalarProduct_add_right,
    scalarProduct_smul_left, scalarProduct_smul_right, star_intCast,
    irr_product ha hc, irr_product ha hd, irr_product hb hc, irr_product hb hd] at h
  by_cases hac : a = c <;> by_cases had : a = d <;>
    by_cases hbc : b = c <;> by_cases hbd : b = d <;>
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;>
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    simp_all <;> norm_num at h

private theorem path_coefficients {G : Type*} [Group G] [Fintype G]
    {Ψ : Fin 5 → ClassFunction G} (p : ThreeCharacterPath Ψ)
    (hgen : ∀ k, IsGeneralizedCharacter (Ψ k))
    (hdeg : ∀ k, Ψ k 1 = 0)
    (htriv : ∀ k, scalarProduct G (Ψ k) 1 = if k = 0 then 1 else 0)
    (hgram : ∀ k l, scalarProduct G (Ψ k) (Ψ l) =
      ![![3,1,0,-1,1], ![1,2,-1,0,1], ![0,-1,2,0,0],
        ![-1,0,0,3,1], ![1,1,0,1,3]] k l)
    (k : Fin 5) (hk : k = 3 ∨ k = 4) :
    ∀ i, scalarProduct G (Ψ k) (p.χ i) =
      if i = (if k = 3 then 1 else 0 : Fin 4) then (p.sign : ℂ) else 0 := by
  classical
  obtain ⟨x, hx⟩ := multiplicity_int (p.irreducible 3) (Ψ k) (hgen k)
  have hx' : scalarProduct G (Ψ k) (p.χ 3) = (x : ℂ) := by
    rw [← scalarProduct_conj, hx]; simp only [star_intCast]
  have h0 := hgram k 0
  have h1 := hgram k 1
  have h2 := hgram k 2
  rw [p.first, scalarProduct_add_right, scalarProduct_smul_right,
    scalarProduct_sub_right, htriv] at h0
  rw [p.second, scalarProduct_smul_right, scalarProduct_sub_right] at h1
  rw [p.third, scalarProduct_smul_right, scalarProduct_sub_right] at h2
  have hc (i : Fin 4) : scalarProduct G (Ψ k) (p.χ i) =
      ((if i = (if k = 3 then 1 else 0 : Fin 4) then x + p.sign else x : ℤ) : ℂ) := by
    rcases hk with rfl | rfl <;> fin_cases i <;>
      rcases p.sign_unit with hs | hs <;>
      simp [hs, Matrix.cons_val] at h0 h1 h2 ⊢
    all_goals first
      | exact hx'
      | linear_combination h1 + h2 + hx'
      | linear_combination -h0 + h1 + h2 + hx'
      | linear_combination h2 + hx'
      | linear_combination -h1 - h2 + hx'
      | linear_combination h0 - h1 - h2 + hx'
      | linear_combination -h2 + hx'
  have hn : normSq G (Ψ k) = 3 := by
    rcases hk with rfl | rfl
    · exact hgram 3 3
    · exact hgram 4 4
  have hz := path_projection p.χ p.irreducible p.distinct (Ψ k) hn (hdeg k)
    p.sign x p.sign_unit (if k = 3 then 1 else 0) hc
  intro i
  simpa [hz] using hc i

private theorem path_residual {G : Type*} [Group G] [Fintype G]
    (χ : Fin 4 → ClassFunction G) (hi : ∀ i, IsIrreducibleCharacter (χ i))
    (hinj : Function.Injective χ) (R : ClassFunction G) (hg : IsGeneralizedCharacter R)
    (hn : normSq G R = 3) (e : ℤ) (he : e = 1 ∨ e = -1) (j : Fin 4)
    (hc : ∀ i, scalarProduct G R (χ i) = if i = j then (e : ℂ) else 0) :
    IsGeneralizedCharacter (R - (e : ℂ) • χ j) ∧
      normSq G (R - (e : ℂ) • χ j) = 2 ∧
      ∀ i, scalarProduct G (R - (e : ℂ) • χ j) (χ i) = 0 := by
  have hj : scalarProduct G (χ j) R = (e : ℂ) := by
    rw [← scalarProduct_conj, hc]; simp only [ite_true, star_intCast]
  have ho (i : Fin 4) : scalarProduct G (χ j) (χ i) = if i = j then 1 else 0 := by
    classical
    by_cases h : i = j
    · subst i; simp [irreducible_scalarProduct_self (hi j)]
    · rw [if_neg h]
      exact irreducible_scalarProduct_of_ne (hi j) (hi i) (fun he => h (hinj he).symm)
  constructor
  · rcases he with rfl | rfl
    · simpa using isGeneralizedCharacter_sub_char hg (isCharacter_of_isIrreducibleCharacter (hi j))
    · simpa using isGeneralizedCharacter_add_char hg (isCharacter_of_isIrreducibleCharacter (hi j))
  constructor
  · change scalarProduct G _ _ = _
    simp only [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_smul_left,
      scalarProduct_smul_right, star_intCast, hc, hj, ho, ite_true]
    change normSq G R - _ - _ = _
    rw [hn]; rcases he with rfl | rfl <;> norm_num
  · intro i
    simp only [scalarProduct_sub_left, scalarProduct_smul_left, hc, ho]
    split_ifs <;> ring

private theorem extend_path {G : Type*} [Group G]
    {Ψ : Fin 5 → ClassFunction G} (p : ThreeCharacterPath Ψ)
    (a b c : ClassFunction G)
    (ha : IsIrreducibleCharacter a) (hb : IsIrreducibleCharacter b)
    (hc : IsIrreducibleCharacter c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hna : a ≠ 1) (hnb : b ≠ 1) (hnc : c ≠ 1)
    (hpa : ∀ i, a ≠ p.χ i) (hpb : ∀ i, b ≠ p.χ i) (hpc : ∀ i, c ≠ p.χ i)
    (r s t : ℤ) (hr : r = 1 ∨ r = -1) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (hR : Ψ 3 - (p.sign : ℂ) • p.χ 1 = (r : ℂ) • a + (s : ℂ) • b)
    (hS : Ψ 4 - (p.sign : ℂ) • p.χ 0 = (r : ℂ) • a + (t : ℂ) • c) :
    Nonempty (ThreeCharacterDecomposition Ψ) := by
  classical
  let η : Fin 3 → ClassFunction G := ![a,b,c]
  have hη : Function.Injective η := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [η]
  refine ⟨⟨Fin.append p.χ η, ?_, ?_, ?_, ![p.sign,r,s,t], ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    cases i using Fin.addCases (m := 4) (n := 3) with
    | left j => simpa using p.irreducible j
    | right j => fin_cases j <;> assumption
  · apply Fin.append_injective_iff.mpr
    refine ⟨p.distinct, hη, ?_⟩
    intro i j
    fin_cases j
    · exact (hpa i).symm
    · exact (hpb i).symm
    · exact (hpc i).symm
  · intro i
    cases i using Fin.addCases (m := 4) (n := 3) with
    | left j => simpa using p.nontrivial j
    | right j => fin_cases j <;> assumption
  · intro i; fin_cases i
    · exact p.sign_unit
    · exact hr
    · exact hs
    · exact ht
  · exact p.first
  · exact p.second
  · exact p.third
  · change Ψ 3 = (p.sign : ℂ) • p.χ 1 + (r : ℂ) • a + (s : ℂ) • b
    rw [sub_eq_iff_eq_add] at hR
    rw [hR]; abel
  · change Ψ 4 = (p.sign : ℂ) • p.χ 0 + (r : ℂ) • a + (t : ℂ) • c
    rw [sub_eq_iff_eq_add] at hS
    rw [hS]; abel

/-- Extend Wong's four-constituent path by the three constituents supplied by
his two norm-three functions. Positivity of degrees rules out the alternative
path projection, and the two norm-two residuals share exactly one constituent. -/
public theorem exists_threeCharacterDecomposition_of_path
    {G : Type*} [Group G] [Fintype G] (Ψ : Fin 5 → ClassFunction G)
    (hgen : ∀ k, IsGeneralizedCharacter (Ψ k))
    (hdeg : ∀ k, Ψ k 1 = 0)
    (htriv : ∀ k, scalarProduct G (Ψ k) 1 = if k = 0 then 1 else 0)
    (hgram : ∀ k l, scalarProduct G (Ψ k) (Ψ l) =
      ![![3,1,0,-1,1], ![1,2,-1,0,1], ![0,-1,2,0,0],
        ![-1,0,0,3,1], ![1,1,0,1,3]] k l)
    (p : ThreeCharacterPath Ψ) : Nonempty (ThreeCharacterDecomposition Ψ) := by
  classical
  have c3 : ∀ i, scalarProduct G (Ψ 3) (p.χ i) =
      if i = 1 then (p.sign : ℂ) else 0 :=
    path_coefficients p hgen hdeg htriv hgram 3 (Or.inl rfl)
  have c4 : ∀ i, scalarProduct G (Ψ 4) (p.χ i) =
      if i = 0 then (p.sign : ℂ) else 0 :=
    path_coefficients p hgen hdeg htriv hgram 4 (Or.inr rfl)
  let R := Ψ 3 - (p.sign : ℂ) • p.χ 1
  let S := Ψ 4 - (p.sign : ℂ) • p.χ 0
  obtain ⟨hRg, hRn, hRo⟩ := path_residual p.χ p.irreducible p.distinct
    (Ψ 3) (hgen 3) (hgram 3 3) p.sign p.sign_unit 1 c3
  obtain ⟨hSg, hSn, hSo⟩ := path_residual p.χ p.irreducible p.distinct
    (Ψ 4) (hgen 4) (hgram 4 4) p.sign p.sign_unit 0 c4
  have ht (i : Fin 4) : scalarProduct G (p.χ i) 1 = 0 :=
    irreducible_scalarProduct_of_ne (p.irreducible i) isLinearCharacter_one.1 (p.nontrivial i)
  have hR1 : scalarProduct G R 1 = 0 := by
    simp [R, scalarProduct_sub_left, scalarProduct_smul_left, htriv, ht]
  have hS1 : scalarProduct G S 1 = 0 := by
    simp [S, scalarProduct_sub_left, scalarProduct_smul_left, htriv, ht]
  have h10 : scalarProduct G (p.χ 1) (p.χ 0) = 0 :=
    irreducible_scalarProduct_of_ne (p.irreducible 1) (p.irreducible 0)
      (p.distinct.ne (by decide))
  have h1S : scalarProduct G (p.χ 1) (Ψ 4) = 0 := by
    rw [← scalarProduct_conj, c4]; simp
  have h34 : scalarProduct G (Ψ 3) (Ψ 4) = 1 := hgram 3 4
  have hRS : scalarProduct G R S = 1 := by
    simp [R, S, scalarProduct_sub_left, scalarProduct_sub_right,
      scalarProduct_smul_left, scalarProduct_smul_right, h34, c3, h1S, h10]
  obtain ⟨a, b, r, s, ha, hb, hab, hr, hs, hR⟩ := signed_pair hRg hRn
  obtain ⟨c, d, t, u, hc, hd, hcd, htu, hu, hS⟩ := signed_pair hSg hSn
  have hna := pair_orthogonal ha hb isLinearCharacter_one.1 hab r s hr hs
    (by rw [← hR]; exact hR1)
  have hnc := pair_orthogonal hc hd isLinearCharacter_one.1 hcd t u htu hu
    (by rw [← hS]; exact hS1)
  have hpa (i : Fin 4) := pair_orthogonal ha hb (p.irreducible i) hab r s hr hs
    (by rw [← hR]; exact hRo i)
  have hpc (i : Fin 4) := pair_orthogonal hc hd (p.irreducible i) hcd t u htu hu
    (by rw [← hS]; exact hSo i)
  have hov := pair_overlap ha hb hc hd hab hcd r s t u hr hs htu hu
    (by rw [← hR, ← hS]; exact hRS)
  rcases hov with ⟨hac, hrt, hbd⟩ | ⟨had, hru, hbc⟩ | ⟨hbc, hst, had⟩ | ⟨hbd, hsu, hac⟩
  · subst c; subst t
    exact extend_path p a b d ha hb hd hab hcd hbd hna.1 hna.2 hnc.2
      (fun i => (hpa i).1) (fun i => (hpa i).2) (fun i => (hpc i).2)
      r s u hr hs hu hR hS
  · subst d; subst u
    exact extend_path p a b c ha hb hc hab hcd.symm hbc hna.1 hna.2 hnc.1
      (fun i => (hpa i).1) (fun i => (hpa i).2) (fun i => (hpc i).1)
      r s t hr hs htu hR (hS.trans (add_comm _ _))
  · subst c; subst t
    exact extend_path p b a d hb ha hd hab.symm hcd had hna.2 hna.1 hnc.2
      (fun i => (hpa i).2) (fun i => (hpa i).1) (fun i => (hpc i).2)
      s r u hs hr hu (hR.trans (add_comm _ _)) hS
  · subst d; subst u
    exact extend_path p b a c hb ha hc hab.symm hcd.symm hac hna.2 hna.1 hnc.1
      (fun i => (hpa i).2) (fun i => (hpa i).1) (fun i => (hpc i).1)
      s r t hs hr htu (hR.trans (add_comm _ _)) (hS.trans (add_comm _ _))

/-- Wong's Gram matrix and degree conditions yield the seven distinct nontrivial
irreducibles and four signs in equation (3). First extract the four-character
path from the norm-two functions, then extend it using the norm-three functions. -/
public theorem exists_threeCharacterDecomposition
    {G : Type*} [Group G] [Fintype G] (Ψ : Fin 5 → ClassFunction G)
    (hgen : ∀ k, IsGeneralizedCharacter (Ψ k))
    (hdeg : ∀ k, Ψ k 1 = 0)
    (htriv : ∀ k, scalarProduct G (Ψ k) 1 = if k = 0 then 1 else 0)
    (hgram : ∀ k l, scalarProduct G (Ψ k) (Ψ l) =
      ![![3,1,0,-1,1], ![1,2,-1,0,1], ![0,-1,2,0,0],
        ![-1,0,0,3,1], ![1,1,0,1,3]] k l) :
    Nonempty (ThreeCharacterDecomposition Ψ) := by
  obtain ⟨p⟩ := exists_threeCharacterPath Ψ hgen hdeg htriv hgram
  exact exists_threeCharacterDecomposition_of_path Ψ hgen hdeg htriv hgram p

end ABG
