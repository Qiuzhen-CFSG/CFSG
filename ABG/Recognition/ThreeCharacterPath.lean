module
public import BenderGlauberman.ClassFunction

/-!
# The four-constituent path in Wong's character argument

Norm-two integral character vectors have two signed constituents. In degree
zero or minus one, positivity of irreducible degrees forces opposite signs.
The three pairings in Wong's Gram matrix then force a path on four vertices.

Source: Wong (1964), equation (3), p.98 and Appendix, p.106.
-/

namespace ABG
open BenderGlauberman
open scoped BigOperators

private theorem norm_two_difference {G : Type*} [Group G] [Fintype G]
    {δ : ClassFunction G} (hδ : IsGeneralizedCharacter δ)
    (hn : scalarProduct G δ δ = 2) (hd : δ 1 = 0 ∨ δ 1 = -1) :
    ∃ a b : ClassFunction G, IsIrreducibleCharacter a ∧ IsIrreducibleCharacter b ∧
      a ≠ b ∧ δ = a - b := by
  obtain ⟨a, b, ha, hb, hab, he⟩ := norm_two_pair hδ hn
  have hda := irreducible_degree_ge_one ha
  have hdb := irreducible_degree_ge_one hb
  rcases he with he | he | he | he
  · exact ⟨a, b, ha, hb, hab, he⟩
  · have hv := congrArg Complex.re (congrFun he 1)
    rcases hd with hd | hd <;> simp [hd] at hv <;> linarith
  · have hv := congrArg Complex.re (congrFun he 1)
    rcases hd with hd | hd <;> simp [hd] at hv <;> linarith
  · exact ⟨b, a, hb, ha, hab.symm, he.trans (by abel)⟩

private theorem irr_product {G : Type*} [Group G] [Fintype G]
    {a b : ClassFunction G} (ha : IsIrreducibleCharacter a)
    (hb : IsIrreducibleCharacter b) :
    scalarProduct G a b = if a = b then 1 else 0 := by
  classical
  split_ifs with h
  · subst b; exact irreducible_scalarProduct_self ha
  · exact irreducible_scalarProduct_of_ne ha hb h

private theorem difference_product_one {G : Type*} [Group G] [Fintype G]
    {a b c d : ClassFunction G}
    (ha : IsIrreducibleCharacter a) (hb : IsIrreducibleCharacter b)
    (hc : IsIrreducibleCharacter c) (hd : IsIrreducibleCharacter d)
    (_hab : a ≠ b) (_hcd : c ≠ d)
    (h : scalarProduct G (a - b) (c - d) = 1) : a = c ∨ b = d := by
  classical
  simp only [scalarProduct_sub_left, scalarProduct_sub_right,
    irr_product ha hc, irr_product ha hd, irr_product hb hc, irr_product hb hd] at h
  by_contra hn
  have hac : a ≠ c := fun he => hn (Or.inl he)
  have hbd : b ≠ d := fun he => hn (Or.inr he)
  simp only [if_neg hac, if_neg hbd] at h
  split_ifs at h <;> norm_num at h

private theorem difference_product_zero {G : Type*} [Group G] [Fintype G]
    {a b c d : ClassFunction G}
    (ha : IsIrreducibleCharacter a) (hb : IsIrreducibleCharacter b)
    (hc : IsIrreducibleCharacter c) (hd : IsIrreducibleCharacter d)
    (hab : a ≠ b) (hcd : c ≠ d)
    (h : scalarProduct G (a - b) (c - d) = 0) :
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  classical
  simp only [scalarProduct_sub_left, scalarProduct_sub_right,
    irr_product ha hc, irr_product ha hd, irr_product hb hc, irr_product hb hd] at h
  by_cases hac : a = c
  · subst c
    simp only [if_neg hcd, if_neg hab.symm] at h
    split_ifs at h <;> norm_num at h
  by_cases had : a = d
  · subst d
    simp only [if_neg hac, if_neg hab.symm] at h
    split_ifs at h <;> norm_num at h
  by_cases hbc : b = c
  · subst c
    simp only [if_neg hab, if_neg had, if_neg hcd] at h
    norm_num at h
  refine ⟨hac, had, hbc, ?_⟩
  intro hbd
  simp only [if_neg hac, if_neg had, if_neg hbc, if_pos hbd] at h
  norm_num at h

private theorem difference_nontrivial {G : Type*} [Group G] [Fintype G]
    {a b : ClassFunction G} (ha : IsIrreducibleCharacter a)
    (hb : IsIrreducibleCharacter b) (hab : a ≠ b)
    (h : scalarProduct G (a - b) 1 = 0) : a ≠ 1 ∧ b ≠ 1 := by
  classical
  have hi : IsIrreducibleCharacter (1 : ClassFunction G) := isLinearCharacter_one.1
  simp only [scalarProduct_sub_left, irr_product ha hi, irr_product hb hi] at h
  constructor
  · intro he
    have hb1 : b ≠ 1 := by simpa [he] using hab.symm
    simp [he, hb1] at h
  · intro he
    have ha1 : a ≠ 1 := by simpa [he] using hab
    simp [he, ha1] at h

/-- The first three identities of Wong's decomposition, with their shared
four distinct nontrivial irreducibles. -/
public structure ThreeCharacterPath {G : Type*} [Group G]
    (Ψ : Fin 5 → ClassFunction G) where
  χ : Fin 4 → ClassFunction G
  irreducible : ∀ i, IsIrreducibleCharacter (χ i)
  distinct : Function.Injective χ
  nontrivial : ∀ i, χ i ≠ 1
  sign : ℤ
  sign_unit : sign = 1 ∨ sign = -1
  first : Ψ 0 = 1 + (sign : ℂ) • (χ 0 - χ 1)
  second : Ψ 1 = (sign : ℂ) • (χ 0 - χ 2)
  third : Ψ 2 = (sign : ℂ) • (χ 2 - χ 3)

/-- The degree and Gram data force the first four constituents of Wong's
seven-character catalog. -/
public theorem exists_threeCharacterPath {G : Type*} [Group G] [Fintype G]
    (Ψ : Fin 5 → ClassFunction G)
    (hgen : ∀ k, IsGeneralizedCharacter (Ψ k))
    (hdeg : ∀ k, Ψ k 1 = 0)
    (htriv : ∀ k, scalarProduct G (Ψ k) 1 = if k = 0 then 1 else 0)
    (hgram : ∀ k l, scalarProduct G (Ψ k) (Ψ l) =
      ![![3,1,0,-1,1], ![1,2,-1,0,1], ![0,-1,2,0,0],
        ![-1,0,0,3,1], ![1,1,0,1,3]] k l) :
    Nonempty (ThreeCharacterPath Ψ) := by
  classical
  have hi : IsIrreducibleCharacter (1 : ClassFunction G) := isLinearCharacter_one.1
  have h11 : scalarProduct G (1 : ClassFunction G) 1 = 1 :=
    irreducible_scalarProduct_self hi
  have htriv' (k : Fin 5) : scalarProduct G 1 (Ψ k) = if k = 0 then 1 else 0 := by
    rw [← scalarProduct_conj, htriv]
    split_ifs <;> simp
  have hn : scalarProduct G (Ψ 0 - 1) (Ψ 0 - 1) = 2 := by
    norm_num [scalarProduct_sub_left, scalarProduct_sub_right, hgram, htriv, htriv', h11]
  obtain ⟨a, b, ha, hb, hab, hA⟩ := norm_two_difference
    (isGeneralizedCharacter_sub_char (hgen 0) (isCharacter_of_isIrreducibleCharacter hi))
    hn (Or.inr (by simp [hdeg]))
  obtain ⟨c, d, hc, hd, hcd, hB⟩ := norm_two_difference (hgen 1)
    (by simpa using hgram 1 1) (Or.inl (hdeg 1))
  obtain ⟨e, f, he, hf, hef, hC⟩ := norm_two_difference (hgen 2)
    (by simpa using hgram 2 2) (Or.inl (hdeg 2))
  have hAB : scalarProduct G (a - b) (c - d) = 1 := by
    rw [← hA, ← hB]
    simp [scalarProduct_sub_left, hgram, htriv']
  have hAC : scalarProduct G (a - b) (e - f) = 0 := by
    rw [← hA, ← hC]
    simp [scalarProduct_sub_left, hgram, htriv']
  have hBC : scalarProduct G (c - d) (f - e) = 1 := by
    have h := hgram 1 2
    rw [hB, hC] at h
    have hr : f - e = -(e - f) := by abel
    rw [hr, scalarProduct_neg_right, h]
    change -(-1 : ℂ) = 1
    ring
  have hAB' := difference_product_one ha hb hc hd hab hcd hAB
  have hBC' := difference_product_one hc hd hf he hcd hef.symm hBC
  have hAC' := difference_product_zero ha hb he hf hab hef hAC
  have hna : a ≠ 1 ∧ b ≠ 1 := difference_nontrivial ha hb hab (by
    rw [← hA]; simp [scalarProduct_sub_left, htriv, h11])
  have hnc : c ≠ 1 ∧ d ≠ 1 := difference_nontrivial hc hd hcd (by
    rw [← hB]; simpa using htriv 1)
  have hne : e ≠ 1 ∧ f ≠ 1 := difference_nontrivial he hf hef (by
    rw [← hC]; simpa using htriv 2)
  rcases hAB' with h | h
  · subst c
    have hde : d = e := hBC'.resolve_left hAC'.2.1
    subst e
    refine ⟨⟨![a, b, d, f], ?_, ?_, ?_, 1, Or.inl rfl, ?_, ?_, ?_⟩⟩
    · intro i; fin_cases i <;> assumption
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i; fin_cases i <;> simp_all
    · simpa using (sub_eq_iff_eq_add.mp hA).trans (add_comm _ _)
    · simpa using hB
    · simpa using hC
  · subst d
    have hcf : c = f := hBC'.resolve_right hAC'.2.2.1
    subst f
    refine ⟨⟨![b, a, c, e], ?_, ?_, ?_, -1, Or.inr rfl, ?_, ?_, ?_⟩⟩
    · intro i; fin_cases i <;> assumption
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i; fin_cases i <;> simp_all
    · simpa [neg_sub] using (sub_eq_iff_eq_add.mp hA).trans (add_comm _ _)
    · simpa [neg_sub] using hB
    · simpa [neg_sub] using hC

end ABG
