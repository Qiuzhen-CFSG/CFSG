module

public import Theory.AlgebraicGroup.RootSystems.IntegralAllRootOperators

/-!
# All-root integral Chevalley bracket constants

For a finite reduced crystallographic root pairing and a chosen base, this module computes
the action of every transported root operator on every transported root line.  If the sum
of two roots is a root, the resulting integral coefficient is a sign times one more than
the bottom length of the corresponding root string.  Equivalently, its absolute value is
the standard Chevalley coefficient `p + 1`.

The proof pulls a pair back along the chosen Weyl route.  Weyl transport preserves membership
in root strings and hence their bottom coefficients.  The positive case then uses the simple
raising formula, while the negative case uses the lowering formula and the identity exchanging
top and bottom string lengths under root negation.  Products of the integral Tits signs have
square one, which accounts for all route-dependent signs.

The complementary non-root-sum action is zero away from an opposite pair.  Opposite roots
share the exact transported Cartan vector supplied by the common positive-root route.  No
irreducibility hypothesis occurs, so all formulas also apply when the two roots lie in
different components.  The construction is the integral root-string calculation underlying
the Chevalley basis relations, transported using `IntegralAllRootOperators`.
-/


namespace RootPairing.IntegralGeckConstruction

open Matrix

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

lemma titsWordSign_mul_self (word : List b.support) (j : ι) :
    titsWordSign (P := P) word j * titsWordSign word j = 1 := by
  induction word with
  | nil => simp [titsWordSign]
  | cons i word ih =>
      simp only [titsWordSign]
      rw [mul_mul_mul_comm, ih]
      simp [← pow_add, ← two_mul]

/-- The preimage of a root index under the Weyl element represented by a word. -/
private def reflectionWordPreimage (word : List b.support) (j : ι) : ι :=
  P.weylGroupToPerm (b.wordProd word)⁻¹ j

@[simp] private lemma reflectionWord_preimage (word : List b.support) (j : ι) :
    reflectionWord word (reflectionWordPreimage (P := P) word j) = j := by
  rw [reflectionWord_eq_weylGroupToPerm]
  simp [reflectionWordPreimage]

@[simp] private lemma reflectionWordPreimage_reflectionWord (word : List b.support) (j : ι) :
    reflectionWordPreimage (P := P) word (reflectionWord word j) = j := by
  rw [reflectionWord_eq_weylGroupToPerm]
  simp [reflectionWordPreimage]

private lemma root_reflectionWordPreimage (word : List b.support) (j : ι) :
    P.root (reflectionWordPreimage (P := P) word j) =
      (b.wordProd word)⁻¹ • P.root j := by
  rw [reflectionWordPreimage, P.weylGroup_apply_root]

private lemma root_add_reflectionWordPreimage (word : List b.support) {i j k : ι}
    (h : P.root k = P.root i + P.root j) :
    P.root (reflectionWordPreimage (P := P) word k) =
      P.root (reflectionWordPreimage (P := P) word i) +
        P.root (reflectionWordPreimage (P := P) word j) := by
  rw [root_reflectionWordPreimage, root_reflectionWordPreimage,
    root_reflectionWordPreimage, h, smul_add]

private lemma root_sub_reflectionWordPreimage (word : List b.support) {i j k : ι}
    (h : P.root k = P.root j - P.root i) :
    P.root (reflectionWordPreimage (P := P) word k) =
      P.root (reflectionWordPreimage (P := P) word j) -
        P.root (reflectionWordPreimage (P := P) word i) := by
  rw [root_reflectionWordPreimage, root_reflectionWordPreimage,
    root_reflectionWordPreimage, h, smul_sub]

private lemma root_sub_nsmul_mem_range_reflectionWord_iff
    (word : List b.support) (i j : ι) (n : ℕ) :
    P.root (reflectionWord word j) - n • P.root (reflectionWord word i) ∈
        Set.range P.root ↔
      P.root j - n • P.root i ∈ Set.range P.root := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨reflectionWordPreimage (P := P) word k, ?_⟩
    rw [root_reflectionWordPreimage, hk, root_reflectionWord,
      root_reflectionWord, smul_sub]
    have hnsmul (x : M) :
        (b.wordProd word)⁻¹ • (n • x) =
          n • ((b.wordProd word)⁻¹ • x) := by
      exact map_nsmul
        (DistribSMul.toAddMonoidHom M (b.wordProd word)⁻¹) n x
    rw [hnsmul]
    simp
  · rintro ⟨k, hk⟩
    refine ⟨reflectionWord word k, ?_⟩
    rw [root_reflectionWord, hk, root_reflectionWord, root_reflectionWord,
      smul_sub]
    have hnsmul (x : M) :
        b.wordProd word • (n • x) = n • (b.wordProd word • x) := by
      exact map_nsmul
        (DistribSMul.toAddMonoidHom M (b.wordProd word)) n x
    rw [hnsmul]

private lemma root_add_mem_range_reflectionWord_iff (word : List b.support) (i j : ι) :
    P.root (reflectionWord word i) + P.root (reflectionWord word j) ∈
        Set.range P.root ↔
      P.root i + P.root j ∈ Set.range P.root := by
  letI := P.indexNeg
  have hrootNeg (x : ι) : P.root (-x) = -P.root x := by
    simp only [P.indexNeg_neg, P.root_reflectionPerm, P.reflection_apply_self]
  simpa only [reflectionWord_neg, one_nsmul, hrootNeg, sub_neg_eq_add,
    add_comm] using
    root_sub_nsmul_mem_range_reflectionWord_iff (P := P) (b := b)
      word (-i) j 1

lemma chainBotCoeff_reflectionWord (word : List b.support) (i j : ι)
    (hlin : LinearIndependent R ![P.root i, P.root j]) :
    P.chainBotCoeff (reflectionWord word i) (reflectionWord word j) =
      P.chainBotCoeff i j := by
  have hlin' : LinearIndependent R
      ![P.root (reflectionWord word i), P.root (reflectionWord word j)] := by
    let f : M ≃ₗ[R] M :=
      RootPairing.Equiv.weightHom P (b.wordProd word)
    have hm := hlin.map' f.toLinearMap
      (LinearMap.ker_eq_bot.mpr f.injective)
    have heq : f.toLinearMap ∘ ![P.root i, P.root j] =
        ![P.root (reflectionWord word i),
          P.root (reflectionWord word j)] := by
      simp_rw [root_reflectionWord]
      funext x
      fin_cases x <;> rfl
    rwa [heq] at hm
  apply Nat.le_antisymm
  · rw [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin]
    rw [← root_sub_nsmul_mem_range_reflectionWord_iff word]
    exact (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin').2 le_rfl
  · rw [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin']
    rw [root_sub_nsmul_mem_range_reflectionWord_iff word]
    exact (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin).2 le_rfl

lemma exists_rootVector_sign (i : ι) :
    ∃ s : ℤ, s * s = 1 ∧
      rootVector (P := P) (b := b) i = s • v (b := b) i := by
  letI := P.indexNeg
  by_cases hi : b.IsPos i
  · refine ⟨titsWordSign (rootRoute (P := P) (b := b) i).word
        (rootRoute (P := P) (b := b) i).simple, ?_, ?_⟩
    · exact titsWordSign_mul_self _ _
    · exact rootVector_of_pos_eq_smul_v i hi
  · have hneg : b.IsPos (-i) := by
      rw [RootPairing.Base.IsPos.neg_iff_not]
      exact hi
    refine ⟨titsWordSign (rootRoute (P := P) (b := b) (-i)).word
        (-(rootRoute (P := P) (b := b) (-i)).simple : ι), ?_, ?_⟩
    · exact titsWordSign_mul_self _ _
    · have h := rootVector_neg_of_pos_eq_smul_v (P := P) (b := b) (-i) hneg
      simpa only [neg_neg] using h

private lemma exists_rootVector_transport_sign (word : List b.support) (j : ι) :
    ∃ s : ℤ, s * s = 1 ∧
      rootVector (P := P) (b := b) j =
        s • transportedVector (P := P) word
          (v (b := b) (reflectionWordPreimage (P := P) word j)) := by
  rcases exists_rootVector_sign (P := P) (b := b) j with ⟨sj, hsj, hj⟩
  let aj := titsWordSign (P := P) word
    (reflectionWordPreimage (P := P) word j)
  have haj : aj * aj = 1 := titsWordSign_mul_self word _
  have htransport : transportedVector (P := P) word
      (v (b := b) (reflectionWordPreimage (P := P) word j)) =
        aj • v (b := b) j := by
    rw [transportedVector, titsWord_mulVec_v, reflectionWord_preimage]
  refine ⟨sj * aj, ?_, ?_⟩
  · calc
      (sj * aj) * (sj * aj) = (sj * sj) * (aj * aj) := by ring
      _ = 1 := by rw [hsj, haj]; norm_num
  · rw [hj, htransport, smul_smul, mul_assoc, haj, mul_one]

lemma rootOperator_mulVec_root_add_signed {i j k : ι}
    (h : P.root k = P.root i + P.root j) :
    ∃ ε : ℤ, ε * ε = 1 ∧
      rootOperator (P := P) (b := b) i *ᵥ rootVector (P := P) (b := b) j =
        (ε * (P.chainBotCoeff i j + 1 : ℤ)) •
          rootVector (P := P) (b := b) k := by
  letI := P.indexNeg
  by_cases hi : b.IsPos i
  · let route := rootRoute (P := P) (b := b) i
    let preJ := reflectionWordPreimage (P := P) route.word j
    let preK := reflectionWordPreimage (P := P) route.word k
    have hpreI : reflectionWordPreimage (P := P) route.word i = route.simple := by
      have ht := congrArg (reflectionWordPreimage (P := P) route.word) route.target
      simpa only [reflectionWordPreimage_reflectionWord] using ht.symm
    have hpre : P.root preK = P.root route.simple + P.root preJ := by
      simpa only [preJ, preK, hpreI] using
        root_add_reflectionWordPreimage (P := P) (b := b) route.word h
    have hlin : LinearIndependent R ![P.root route.simple, P.root preJ] :=
      P.linearIndependent_of_add_mem_range_root' ⟨preK, hpre⟩
    have hcoeff : P.chainBotCoeff route.simple preJ =
        P.chainBotCoeff i j := by
      have hc := (chainBotCoeff_reflectionWord (P := P) (b := b)
        route.word route.simple preJ hlin).symm
      simpa only [route.target, preJ, reflectionWord_preimage] using hc
    rcases exists_rootVector_sign (P := P) (b := b) j with
      ⟨sj, hsj, hj⟩
    rcases exists_rootVector_sign (P := P) (b := b) k with
      ⟨sk, hsk, hk⟩
    let aj := titsWordSign (P := P) route.word preJ
    let ak := titsWordSign (P := P) route.word preK
    have haj : aj * aj = 1 := titsWordSign_mul_self route.word preJ
    have hak : ak * ak = 1 := titsWordSign_mul_self route.word preK
    have htransportJ : transportedVector (P := P) route.word (v (b := b) preJ) =
        aj • v (b := b) j := by
      rw [transportedVector, titsWord_mulVec_v, reflectionWord_preimage]
    have htransportK : transportedVector (P := P) route.word (v (b := b) preK) =
        ak • v (b := b) k := by
      rw [transportedVector, titsWord_mulVec_v, reflectionWord_preimage]
    have hvj : v (b := b) j = aj •
        transportedVector (P := P) route.word (v (b := b) preJ) := by
      rw [htransportJ, smul_smul, haj, one_smul]
    have hjT : rootVector (P := P) (b := b) j =
        (sj * aj) • transportedVector (P := P) route.word (v (b := b) preJ) := by
      rw [hj, hvj, smul_smul]
    have hkT : transportedVector (P := P) route.word (v (b := b) preK) =
        (ak * sk) • rootVector (P := P) (b := b) k := by
      rw [htransportK, hk, smul_smul, mul_assoc, hsk, mul_one]
    refine ⟨sj * aj * ak * sk, ?_, ?_⟩
    · calc
        (sj * aj * ak * sk) * (sj * aj * ak * sk) =
            (sj * sj) * (aj * aj) * (ak * ak) * (sk * sk) := by ring
        _ = 1 := by rw [hsj, haj, hak, hsk]; norm_num
    · rw [hjT, Matrix.mulVec_smul,
        rootOperator_mulVec_root_add_of_pos i hi hpre,
        hcoeff, hkT]
      simp only [smul_smul]
      congr 1
      ring

  · have hpos : b.IsPos (-i) := by
      rw [RootPairing.Base.IsPos.neg_iff_not]
      exact hi
    let route := rootRoute (P := P) (b := b) (-i)
    let preJ := reflectionWordPreimage (P := P) route.word j
    let preK := reflectionWordPreimage (P := P) route.word k
    have hpreI : reflectionWordPreimage (P := P) route.word (-i) = route.simple := by
      have ht := congrArg (reflectionWordPreimage (P := P) route.word) route.target
      simpa only [reflectionWordPreimage_reflectionWord] using ht.symm
    have hsub : P.root k = P.root j - P.root (-i) := by
      rw [h]
      simp [sub_eq_add_neg, add_comm]
    have hpre : P.root preK = P.root preJ - P.root route.simple := by
      simpa only [preJ, preK, hpreI] using
        root_sub_reflectionWordPreimage (P := P) (b := b) route.word hsub
    have hsum : P.root (-route.simple) + P.root preJ ∈ Set.range P.root := by
      refine ⟨preK, ?_⟩
      rw [hpre]
      simp [sub_eq_add_neg, add_comm]
    have hlin : LinearIndependent R ![P.root (-route.simple), P.root preJ] :=
      P.linearIndependent_of_add_mem_range_root' hsum
    have hrouteNeg : reflectionWord route.word (-route.simple) = i := by
      rw [reflectionWord_neg, route.target, neg_neg]
    have hbotTop : P.chainBotCoeff (-route.simple) preJ =
        P.chainTopCoeff route.simple preJ := by
      simpa only [P.indexNeg_neg] using P.chainBotCoeff_reflectionPerm_left
    have hcoeff : P.chainTopCoeff route.simple preJ =
        P.chainBotCoeff i j := by
      calc
        P.chainTopCoeff route.simple preJ =
            P.chainBotCoeff (-route.simple) preJ := hbotTop.symm
        _ = P.chainBotCoeff i j := by
          have hc := (chainBotCoeff_reflectionWord (P := P) (b := b)
            route.word (-route.simple) preJ hlin).symm
          simpa only [hrouteNeg, preJ, reflectionWord_preimage] using hc
    rcases exists_rootVector_sign (P := P) (b := b) j with
      ⟨sj, hsj, hj⟩
    rcases exists_rootVector_sign (P := P) (b := b) k with
      ⟨sk, hsk, hk⟩
    let aj := titsWordSign (P := P) route.word preJ
    let ak := titsWordSign (P := P) route.word preK
    have haj : aj * aj = 1 := titsWordSign_mul_self route.word preJ
    have hak : ak * ak = 1 := titsWordSign_mul_self route.word preK
    have htransportJ : transportedVector (P := P) route.word (v (b := b) preJ) =
        aj • v (b := b) j := by
      rw [transportedVector, titsWord_mulVec_v, reflectionWord_preimage]
    have htransportK : transportedVector (P := P) route.word (v (b := b) preK) =
        ak • v (b := b) k := by
      rw [transportedVector, titsWord_mulVec_v, reflectionWord_preimage]
    have hvj : v (b := b) j = aj •
        transportedVector (P := P) route.word (v (b := b) preJ) := by
      rw [htransportJ, smul_smul, haj, one_smul]
    have hjT : rootVector (P := P) (b := b) j =
        (sj * aj) • transportedVector (P := P) route.word (v (b := b) preJ) := by
      rw [hj, hvj, smul_smul]
    have hkT : transportedVector (P := P) route.word (v (b := b) preK) =
        (ak * sk) • rootVector (P := P) (b := b) k := by
      rw [htransportK, hk, smul_smul, mul_assoc, hsk, mul_one]
    have haction : rootOperator (P := P) (b := b) i *ᵥ
        transportedVector (P := P) route.word (v (b := b) preJ) =
          (P.chainTopCoeff route.simple preJ + 1 : ℤ) •
            transportedVector (P := P) route.word (v (b := b) preK) := by
      simpa only [neg_neg] using
        rootOperator_neg_mulVec_root_sub_of_pos (P := P) (b := b)
          (-i) hpos hpre
    refine ⟨sj * aj * ak * sk, ?_, ?_⟩
    · calc
        (sj * aj * ak * sk) * (sj * aj * ak * sk) =
            (sj * sj) * (aj * aj) * (ak * ak) * (sk * sk) := by ring
        _ = 1 := by rw [hsj, haj, hak, hsk]; norm_num
    · rw [hjT, Matrix.mulVec_smul, haction, hcoeff, hkT]
      simp only [smul_smul]
      congr 1
      ring

/-- Absolute-value form of the all-root Chevalley root-string coefficient. -/
lemma rootOperator_mulVec_root_add {i j k : ι}
    (h : P.root k = P.root i + P.root j) :
    ∃ c : ℤ, c.natAbs = P.chainBotCoeff i j + 1 ∧
      rootOperator (P := P) (b := b) i *ᵥ rootVector (P := P) (b := b) j =
        c • rootVector (P := P) (b := b) k := by
  obtain ⟨ε, hε, hbracket⟩ :=
    rootOperator_mulVec_root_add_signed (P := P) (b := b) h
  refine ⟨ε * (P.chainBotCoeff i j + 1 : ℤ), ?_, hbracket⟩
  rw [Int.natAbs_mul]
  have habs : ε.natAbs = 1 := by
    rcases (mul_self_eq_one_iff.mp hε) with rfl | rfl <;> simp
  rw [habs]
  rw [one_mul, show (P.chainBotCoeff i j + 1 : ℤ) =
    ((P.chainBotCoeff i j + 1 : ℕ) : ℤ) by norm_num, Int.natAbs_natCast]

/-- Away from an opposite pair, the bracket vanishes when the root sum is absent. -/
lemma rootOperator_mulVec_root_eq_zero {i j : ι}
    (hopposite : letI := P.indexNeg; j ≠ -i)
    (hadd : P.root i + P.root j ∉ Set.range P.root) :
    rootOperator (P := P) (b := b) i *ᵥ rootVector (P := P) (b := b) j = 0 := by
  letI := P.indexNeg
  by_cases hi : b.IsPos i
  · let route := rootRoute (P := P) (b := b) i
    let preJ := reflectionWordPreimage (P := P) route.word j
    have hpreNeg : preJ ≠ -route.simple := by
      intro heq
      apply hopposite
      calc
        j = reflectionWord route.word preJ :=
          (reflectionWord_preimage (P := P) (b := b) route.word j).symm
        _ = reflectionWord route.word (-route.simple) := congrArg _ heq
        _ = -i := by rw [reflectionWord_neg, route.target]
    have hpreAdd : P.root route.simple + P.root preJ ∉ Set.range P.root := by
      intro hmem
      apply hadd
      have hm := (root_add_mem_range_reflectionWord_iff (P := P) (b := b)
        route.word route.simple preJ).2 hmem
      simpa only [route.target, preJ, reflectionWord_preimage] using hm
    rcases exists_rootVector_transport_sign (P := P) (b := b) route.word j with
      ⟨s, -, hj⟩
    rw [hj, Matrix.mulVec_smul,
      rootOperator_mulVec_transport_of_pos i hi,
      eMatrix_mulVec_v_zero hpreNeg hpreAdd]
    simp [transportedVector]
  · have hpos : b.IsPos (-i) := by
      rw [RootPairing.Base.IsPos.neg_iff_not]
      exact hi
    let route := rootRoute (P := P) (b := b) (-i)
    let preJ := reflectionWordPreimage (P := P) route.word j
    have hpreSame : preJ ≠ route.simple := by
      intro heq
      apply hopposite
      calc
        j = reflectionWord route.word preJ :=
          (reflectionWord_preimage (P := P) (b := b) route.word j).symm
        _ = reflectionWord route.word route.simple := congrArg _ heq
        _ = -i := route.target
    have hrouteNeg : reflectionWord route.word (-route.simple) = i := by
      rw [reflectionWord_neg, route.target, neg_neg]
    have hpreAdd : P.root (-route.simple) + P.root preJ ∉ Set.range P.root := by
      intro hmem
      apply hadd
      have hm := (root_add_mem_range_reflectionWord_iff (P := P) (b := b)
        route.word (-route.simple) preJ).2 hmem
      simpa only [hrouteNeg, preJ, reflectionWord_preimage] using hm
    have hpreSub : P.root preJ - P.root route.simple ∉ Set.range P.root := by
      intro hmem
      apply hpreAdd
      simpa [sub_eq_add_neg, add_comm] using hmem
    rcases exists_rootVector_transport_sign (P := P) (b := b) route.word j with
      ⟨s, -, hj⟩
    have htransport : rootOperator (P := P) (b := b) i *ᵥ
        transportedVector (P := P) route.word (v (b := b) preJ) = 0 := by
      simpa only [neg_neg] using
        (rootOperator_neg_mulVec_transport_of_pos (P := P) (b := b)
          (-i) hpos (v (b := b) preJ)).trans (by
            rw [fMatrix_mulVec_v_zero hpreSame hpreSub]
            simp [transportedVector])
    rw [hj, Matrix.mulVec_smul, htransport, smul_zero]

/-- The paired opposite-root formulas in the transported Geck normalization. -/
lemma rootOperator_mulVec_opposite_pair (i : ι) (hi : b.IsPos i) :
    letI := P.indexNeg
    rootOperator (P := P) (b := b) i *ᵥ rootVector (P := P) (b := b) (-i) =
        rootCartanVector (P := P) (b := b) i ∧
      rootOperator (P := P) (b := b) (-i) *ᵥ rootVector (P := P) (b := b) i =
        rootCartanVector (P := P) (b := b) i := by
  letI := P.indexNeg
  exact ⟨rootOperator_mulVec_opposite i hi, rootOperator_neg_mulVec i hi⟩

end

end

end RootPairing.IntegralGeckConstruction
