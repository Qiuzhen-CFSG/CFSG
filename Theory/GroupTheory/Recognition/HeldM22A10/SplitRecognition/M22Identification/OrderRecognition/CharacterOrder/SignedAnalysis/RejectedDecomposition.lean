module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.RejectedArithmetic
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.SignedCoordinates

/-!
# Excluding the third signed decomposition in Janko's Lemma 12

For the five distinct signed characters X1, X2, X3, Y1, Y2, consider the
pattern with third induction `1 + X2 + Y1 - Y2`. The exact Gram equations
force Y1's fifth multiplicity to vanish and its fourth signed multiplicity to
be zero or one. The column formula therefore gives signed involution value
-5 or 3. The three actual Suzuki pairings and the degree-zero equations give
the p.14 quadratic identity in Y1's signed degree. Restriction and divisibility
then exclude all eight arithmetic cases.

This proves the rejected-pattern exclusion conditional on Lemma 11. It does
not yet construct the first two signed expansions or exhaust the possibilities
for the third one. Those support arguments remain necessary for Lemma 12.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 12, pp.13–14. Signs follow the page images.
-/

noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
variable {G : Type*} [Group G] [Finite G]

namespace SignedAnalysis

omit [Group G] in
private theorem sp_sub_right (f g h : ClassFunction G) :
    scalarProduct G f (g - h) = scalarProduct G f g - scalarProduct G f h := by
  simp only [scalarProduct, Pi.sub_apply, star_sub, mul_sub, Finset.sum_sub_distrib,
    mul_sub]

/-- The rejected five-character pattern in Lemma 12 cannot occur. The unit
multiplicity premise is precisely Lemma 11, proved separately. -/
public theorem rejected_decomposition_impossible
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    (hU : HasUnitMultiplicities I.induced) (F : SignedFamily G 5)
    (he0 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (he1 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (he2 : I.induced 2 = 1 + F.term 1 + F.term 3 - F.term 4) : False := by
  choose c hc hv using fun j => I.columns (F.character j) (F.irreducible j)
  change ∀ j i, scalarProduct G (I.induced i) (F.character j) = (c j i : ℂ) at hc
  have hprincipal (i : Fin 5) : scalarProduct G (I.induced i) 1 =
      (exceptionalCoefficients i 0 : ℂ) := I.principal_multiplicity i
  let a (i j : Fin 5) : ℤ := F.sign j * c j i
  have hp (i j : Fin 5) : scalarProduct G (I.induced i) (F.term j) = (a i j : ℂ) := by
    rw [SignedFamily.term, scalarProduct_smul_right, hc j i, star_intCast]
    simp only [a, Int.cast_mul]
    ring
  have ha (i j : Fin 5) : a i j = 0 ∨ a i j = 1 ∨ a i j = -1 := by
    have hh := hU (F.character j) (F.irreducible j) i
    rw [hc j i] at hh
    have hh' : c j i = 0 ∨ c j i = 1 ∨ c j i = -1 := by exact_mod_cast hh
    rcases F.sign_eq j with hs | hs <;> rcases hh' with hh | hh | hh <;> simp [a, hs, hh]
  have hab (i j : Fin 5) : -1 ≤ a i j ∧ a i j ≤ 1 := by
    rcases ha i j with h | h | h <;> omega
  have hg0 (i : Fin 5) : a i 0 + a i 1 + a i 2 = exceptionalGram i 0 := by
    have h := I.gram i 0
    change scalarProduct G (I.induced i) (I.induced 0) = _ at h
    rw [he0, scalarProduct_add_right, scalarProduct_add_right, hp, hp, hp] at h
    exact_mod_cast h
  have hg1 (i : Fin 5) : a i 0 + a i 3 + a i 4 = exceptionalGram i 1 := by
    have h := I.gram i 1
    change scalarProduct G (I.induced i) (I.induced 1) = _ at h
    rw [he1, scalarProduct_add_right, scalarProduct_add_right, hp, hp, hp] at h
    exact_mod_cast h
  have hg2 (i : Fin 5) : exceptionalCoefficients i 0 + a i 1 + a i 3 - a i 4 =
      exceptionalGram i 2 := by
    have h := I.gram i 2
    change scalarProduct G (I.induced i) (I.induced 2) = _ at h
    rw [he2, sp_sub_right, scalarProduct_add_right, scalarProduct_add_right,
      hp, hp, hp, hprincipal] at h
    exact_mod_cast h
  have hfifth : a 4 3 = 0 := by
    have h0 : a 4 0 + a 4 1 + a 4 2 = 0 := hg0 4
    have h1 : a 4 0 + a 4 3 + a 4 4 = 1 := hg1 4
    have h2 : 0 + a 4 1 + a 4 3 - a 4 4 = -1 := hg2 4
    have hb := hab 4 2
    omega
  have hfourth : a 3 3 = 0 ∨ a 3 3 = 1 := by
    have h1 : a 3 0 + a 3 3 + a 3 4 = 1 := hg1 3
    have h2 : 0 + a 3 1 + a 3 3 - a 3 4 = 1 := hg2 3
    have hb0 := hab 3 0
    have hb1 := hab 3 1
    have hb3 := hab 3 3
    omega
  have hy0 : a 0 3 = 0 := by
    have h := hp 0 3
    rw [he0] at h
    simp only [scalarProduct_add_left, F.term_orthonormal] at h
    exact_mod_cast h.symm
  have hy1 : a 1 3 = 1 := by
    have h := hp 1 3
    rw [he1] at h
    simp only [scalarProduct_add_left, F.term_orthonormal] at h
    norm_num at h
    exact_mod_cast h.symm
  have hy2 : a 2 3 = 1 := by
    have h := hp 2 3
    rw [he2] at h
    simp only [scalarProduct_sub_left, scalarProduct_add_left, F.term_orthonormal,
      F.one_scalarProduct_term] at h
    norm_num at h
    exact_mod_cast h.symm
  let t : ℤ := -5 + 8 * a 3 3
  have ht : F.term 3 D.z = (t : ℂ) := by
    have hh := hv 3 0
    simp only [specialRepresentative, Matrix.cons_val_zero, CaseII.into_z_zero,
      columnValue] at hh
    have hh' := congrArg (fun z : ℂ => (F.sign 3 : ℂ) * z) hh
    change F.term 3 D.z = _ at hh'
    have he : F.sign 3 * (7 * c 3 0 - 6 * c 3 1 + c 3 2 + 8 * c 3 3 + 3 * c 3 4) =
        7 * a 0 3 - 6 * a 1 3 + a 2 3 + 8 * a 3 3 + 3 * a 4 3 := by dsimp [a]; ring
    rw [← Int.cast_mul, he, hy0, hy1, hy2, hfifth] at hh'
    simpa [t] using hh'
  have htcases : t = -5 ∨ t = 3 := by
    rcases hfourth with h | h <;> simp [t, h]
  have hdeg (i : Fin 5) : I.induced i 1 = 0 := I.degree_zero i
  have hval (i : Fin 5) : I.induced i D.z = (exceptionalValues i 0 : ℂ) := by
    simpa [specialRepresentative, CaseII.into_z_zero, SpecialInductionData.induced] using I.values i 0
  have hdeg2 : F.term 2 1 = 1 + 2 * F.term 3 1 := by
    have h0 := hdeg 0
    have h1 := hdeg 1
    have h2 := hdeg 2
    rw [he0] at h0
    rw [he1] at h1
    rw [he2] at h2
    simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at h0 h1 h2
    linear_combination h0 - h1 - h2
  have hval2 : F.term 2 D.z = 1 + 2 * F.term 3 D.z := by
    have h0 : I.induced 0 D.z = 16 := hval 0
    have h1 : I.induced 1 D.z = 0 := by simpa [exceptionalValues] using hval 1
    have h2 : I.induced 2 D.z = 16 := hval 2
    rw [he0] at h0
    rw [he1] at h1
    rw [he2] at h2
    simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at h0 h1 h2
    linear_combination h0 - h1 - h2
  let q (j : Fin 5) : ℂ := F.term j D.z ^ 2 / F.term j 1
  have hpair1 : scalarProduct G 1 (fun g => (Theory.Character.involutionPairCount g : ℂ)) =
      (Nat.card G : ℂ) / 147456 := by
    have h := Theory.Character.scalarProduct_irreducible_involutionPairCount_of_fusion
      D.z D.z_order L.involution_fusion 1 isIrreducibleCharacter_one
    rw [D.centralizer_card] at h
    simpa only [Pi.one_apply, one_pow, div_one, mul_one, Nat.cast_ofNat, show (384 : ℂ) ^ 2 = 147456 by norm_num] using h
  have hs0 : (Nat.card G : ℂ) / 147456 * (q 0 + q 1 + q 2) = 31 / 12 := by
    have h := hI 0
    rw [he0] at h
    simp only [scalarProduct_add_left, F.term_pairing D k L] at h
    dsimp [pairingConstants] at h
    norm_num at h
    simp only [← Nat.card_eq_fintype_card] at h
    dsimp [q]
    linear_combination h
  have hs1 : (Nat.card G : ℂ) / 147456 * (q 0 + q 3 + q 4) = -1 := by
    have h := hI 1
    rw [he1] at h
    simp only [scalarProduct_add_left, F.term_pairing D k L] at h
    dsimp [pairingConstants] at h
    norm_num at h
    simp only [← Nat.card_eq_fintype_card] at h
    dsimp [q]
    linear_combination h
  have hs2 : (Nat.card G : ℂ) / 147456 * (1 + q 1 + q 3 - q 4) = 91 / 12 := by
    have h := hI 2
    rw [he2] at h
    simp only [scalarProduct_sub_left, scalarProduct_add_left, F.term_pairing D k L,
      hpair1] at h
    dsimp [pairingConstants] at h
    norm_num at h
    simp only [← Nat.card_eq_fintype_card] at h
    dsimp [q]
    linear_combination h
  have hy : F.term 3 1 ≠ 0 := by
    rw [F.term_one]
    exact_mod_cast F.signedDegree_ne_zero 3
  have hx : 1 + 2 * F.term 3 1 ≠ 0 := by
    rw [← hdeg2, F.term_one]
    exact_mod_cast F.signedDegree_ne_zero 2
  have he := rejected_case_suzuki_elimination (Nat.card G) (F.term 3 1) (F.term 3 D.z)
    (q 0) (q 1) (q 4) hy hx
    (by simpa only [q, hdeg2, hval2] using hs0) hs1 hs2
  have hd : F.signedDegree 2 = 1 + 2 * F.signedDegree 3 := by
    simp only [F.term_one] at hdeg2
    exact_mod_cast hdeg2
  have he' : (Nat.card G : ℤ) * (F.signedDegree 3 - t) ^ 2 =
      294912 * F.signedDegree 3 * (1 + 2 * F.signedDegree 3) := by
    simp only [F.term_one, ht] at he
    exact_mod_cast he
  exact rejected_case_of_actual_degrees D k L (F.irreducible 3) (F.irreducible 2)
    (F.sign 3) (F.sign 2) t (F.sign_eq 3) (F.sign_eq 2) ht htcases hd he'

end SignedAnalysis
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
