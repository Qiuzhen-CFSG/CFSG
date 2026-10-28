module
public import Theory.Representation.Mathieu.M22James.Ambient
public import Theory.Mathieu.M22.Properties.PairHexadIncidence

/-!
# The commutant of the actual binary hexad preimage

Three short words in the genuine triple-cover generators fix the standard
native hexad. Twelve short products give cyclic row coordinates, and one
rank-ten annihilator confines a commuting matrix to the span of identity
and the cubic scalar. A unit is therefore one of the three scalars. Every
actual outer actor inverts the scalar, so commuting with it leaves only
identity. The word and matrix certificates are checked by the kernel.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
This supplies the section commutant calculation without assuming a module
classification. The native ATLAS matrices and their attribution and license
are inherited from the imported M22James model and its LinearModel/source.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison.HexadCommutant
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Sporadic.Mathieu
open scoped Matrix
private def u0 : Matrix12 := fromRows ![3005,3006,1362,3150,2304,652,3355,1639,2748,3931,1309,2732]
private def u1 : Matrix12 := fromRows ![13,2372,3819,1177,2875,3579,2059,3074,3093,208,2544,1875]
private def u2 : Matrix12 := fromRows ![2602,222,4,1038,204,2636,2743,3757,1498,2295,1244,1642]
private def gen : Fin 3 → Matrix12 := ![u0,u1,u2]
private theorem scalar_commutes (k : Fin 3) : Commute matrixJ (gen k) := by
  change matrixJ * gen k = gen k * matrixJ
  fin_cases k <;> decide +kernel
private def w0 : Matrix12 := 1
private def w1 : Matrix12 := fromRows ![3005,3006,1362,3150,2304,652,3355,1639,2748,3931,1309,2732]
private def w2 : Matrix12 := fromRows ![13,2372,3819,1177,2875,3579,2059,3074,3093,208,2544,1875]
private def w3 : Matrix12 := fromRows ![2602,222,4,1038,204,2636,2743,3757,1498,2295,1244,1642]
private def w4 : Matrix12 := fromRows ![2859,610,3985,1438,2886,1696,1117,2930,1843,3206,1185,3080]
private def w5 : Matrix12 := fromRows ![330,3006,2979,3285,944,592,2394,1568,3770,2842,4074,3702]
private def w6 : Matrix12 := fromRows ![673,2137,1367,3465,2186,2480,1761,1039,2142,636,224,1250]
private def w7 : Matrix12 := fromRows ![2687,3494,2641,2653,134,3503,2691,2023,2942,3890,2447,3916]
private def w8 : Matrix12 := fromRows ![3616,2307,2797,1177,3901,1804,2192,616,2132,1238,3370,2430]
private def w9 : Matrix12 := fromRows ![139,222,1362,1983,608,496,3405,1696,2605,3853,3709,545]
private def w10 : Matrix12 := fromRows ![292,247,375,2592,1676,388,223,2763,1877,1129,2546,2374]
private def w11 : Matrix12 := fromRows ![614,19,3750,3465,891,2534,1483,3202,3045,2445,113,1061]
private theorem step1 : w0 * gen 0 = w1 := by decide +kernel
private theorem commute1 {M : Matrix12} (hm : ∀ k, Commute M (gen k)) : Commute M w1 := by
  rw [←step1]
  exact (show Commute M w0 from by change Commute M 1; exact Commute.one_right M).mul_right (hm 0)
private theorem step2 : w0 * gen 1 = w2 := by decide +kernel
private theorem commute2 {M : Matrix12} (hm : ∀ k, Commute M (gen k)) : Commute M w2 := by
  rw [←step2]
  exact (show Commute M w0 from by change Commute M 1; exact Commute.one_right M).mul_right (hm 1)
private theorem step3 : w0 * gen 2 = w3 := by decide +kernel
private theorem commute3 {M : Matrix12} (hm : ∀ k, Commute M (gen k)) : Commute M w3 := by
  rw [←step3]
  exact (show Commute M w0 from by change Commute M 1; exact Commute.one_right M).mul_right (hm 2)
private theorem step4 : w1 * gen 1 = w4 := by decide +kernel
private theorem commute4 {M : Matrix12} (hm : ∀ k, Commute M (gen k)) : Commute M w4 := by
  rw [←step4]
  exact (commute1 hm).mul_right (hm 1)
private theorem step5 : w1 * gen 2 = w5 := by decide +kernel
private theorem commute5 {M : Matrix12} (hm : ∀ k, Commute M (gen k)) : Commute M w5 := by
  rw [←step5]
  exact (commute1 hm).mul_right (hm 2)
private theorem step6 : w2 * gen 0 = w6 := by decide +kernel
private theorem commute6 {M : Matrix12} (hm : ∀ k, Commute M (gen k)) : Commute M w6 := by
  rw [←step6]
  exact (commute2 hm).mul_right (hm 0)
private theorem step7 : w2 * gen 1 = w7 := by decide +kernel
private theorem commute7 {M : Matrix12} (hm : ∀ k, Commute M (gen k)) : Commute M w7 := by
  rw [←step7]
  exact (commute2 hm).mul_right (hm 1)
private theorem step8 : w2 * gen 2 = w8 := by decide +kernel
private theorem commute8 {M : Matrix12} (hm : ∀ k, Commute M (gen k)) : Commute M w8 := by
  rw [←step8]
  exact (commute2 hm).mul_right (hm 2)
private theorem step9 : w3 * gen 0 = w9 := by decide +kernel
private theorem commute9 {M : Matrix12} (hm : ∀ k, Commute M (gen k)) : Commute M w9 := by
  rw [←step9]
  exact (commute3 hm).mul_right (hm 0)
private theorem step10 : w6 * gen 1 = w10 := by decide +kernel
private theorem commute10 {M : Matrix12} (hm : ∀ k, Commute M (gen k)) : Commute M w10 := by
  rw [←step10]
  exact (commute6 hm).mul_right (hm 1)
private theorem step11 : w8 * gen 0 = w11 := by decide +kernel
private theorem commute11 {M : Matrix12} (hm : ∀ k, Commute M (gen k)) : Commute M w11 := by
  rw [←step11]
  exact (commute8 hm).mul_right (hm 0)
private def words : Fin 12 → Matrix12 := ![w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11]
private def cyclicRows : Matrix12 := fromRows ![1,3005,13,2602,2859,330,673,2687,3616,139,292,614]
private def cyclicRowsInv : Matrix12 := fromRows ![1,675,2266,2271,534,3267,2629,2173,25,1279,2932,584]
private theorem cyclicRows_spec (i : Fin 12) : cyclicRows i = words i 0 := by
  have hh : @Eq Matrix12 cyclicRows (fun i j => words i 0 j) := by
    exact @of_decide_eq_true _ (Matrix.decidableEq _ _) rfl
  exact congrFun hh i
private theorem cyclicRows_left_inv : cyclicRowsInv * cyclicRows = 1 := by decide +kernel
private theorem commute_words {M : Matrix12} (hm : ∀ k, Commute M (gen k))
    (i : Fin 12) : Commute M (words i) := by
  fin_cases i
  · exact Commute.one_right M
  · exact commute1 hm
  · exact commute2 hm
  · exact commute3 hm
  · exact commute4 hm
  · exact commute5 hm
  · exact commute6 hm
  · exact commute7 hm
  · exact commute8 hm
  · exact commute9 hm
  · exact commute10 hm
  · exact commute11 hm
private theorem commuting_ext_firstRow {M N : Matrix12}
    (hm : ∀ k, Commute M (gen k)) (hn : ∀ k, Commute N (gen k))
    (hrow : M 0=N 0) : M=N := by
  have he : cyclicRows*M=cyclicRows*N := by
    funext i
    rw [Matrix.mul_apply_eq_vecMul,Matrix.mul_apply_eq_vecMul,cyclicRows_spec]
    change (words i*M) 0=(words i*N) 0
    rw [←(commute_words hm i).eq,←(commute_words hn i).eq,
      Matrix.mul_apply_eq_vecMul,Matrix.mul_apply_eq_vecMul,hrow]
  calc
    M=(cyclicRowsInv*cyclicRows)*M := by rw [cyclicRows_left_inv,one_mul]
    _=(cyclicRowsInv*cyclicRows)*N := by rw [mul_assoc,he,←mul_assoc]
    _=N := by rw [cyclicRows_left_inv,one_mul]
private def annihilator : Matrix12 := fromRows ![0,2818,477,4000,503,3262,2827,1378,2163,3770,1326,1661]
private def rightFactor : Matrix12 := fromRows ![2216,3642,544,2282,1808,824,3658,3336,968,0,0,3568]
private def complement : Matrix12 := fromRows ![0,2,1528,8,16,32,64,128,256,512,1024,2048]
private theorem annihilator_eq : w3*gen 1 + w0 + w1 + w2 + w4 + w5 + w6 + w7 + w8 + w9 = annihilator := by decide +kernel
private theorem annihilator_firstRow : annihilator 0=0 := by decide +kernel
private theorem annihilator_mul : annihilator * rightFactor=complement := by decide +kernel
private theorem complement_projection :
    complement + (Matrix.vecMulVec (Pi.single 0 1) ((1 : Matrix12) 0) +
      Matrix.vecMulVec (Pi.single 2 1) (matrixJ 0)) = 1 := by decide +kernel
private theorem commute_annihilator {M : Matrix12} (hm : ∀ k, Commute M (gen k)) :
    Commute M annihilator := by
  rw [←annihilator_eq]
  exact ((((((((((commute3 hm).mul_right (hm 1)).add_right (show Commute M w0 from Commute.one_right M)).add_right (commute1 hm)).add_right (commute2 hm)).add_right (commute4 hm)).add_right (commute5 hm)).add_right (commute6 hm)).add_right (commute7 hm)).add_right (commute8 hm)).add_right (commute9 hm)
private theorem firstRow_in_plane {M : Matrix12} (hm : ∀ k, Commute M (gen k)) :
    M 0=M 0 0 • (1 : Matrix12) 0 + M 0 2 • matrixJ 0 := by
  have hz : Matrix.vecMul (M 0) annihilator=0 := by
    change (M*annihilator) 0=0
    rw [(commute_annihilator hm).eq,Matrix.mul_apply_eq_vecMul,
      annihilator_firstRow,Matrix.zero_vecMul]
  have hp : Matrix.vecMul (M 0) complement=0 := by
    rw [←annihilator_mul,←Matrix.vecMul_vecMul,hz,Matrix.zero_vecMul]
  calc
    M 0=Matrix.vecMul (M 0) (1 : Matrix12) := (Matrix.vecMul_one _).symm
    _=M 0 0 • (1 : Matrix12) 0 + M 0 2 • matrixJ 0 := by
      conv_lhs => rw [←complement_projection]
      rw [Matrix.vecMul_add,hp,zero_add,Matrix.vecMul_add,
        Matrix.vecMul_vecMulVec,Matrix.vecMul_vecMulVec,
        dotProduct_single_one,dotProduct_single_one]

private theorem commuting_matrix_form {M : Matrix12} (hm : ∀ k, Commute M (gen k)) :
    M=M 0 0 • (1 : Matrix12) + M 0 2 • matrixJ := by
  apply commuting_ext_firstRow hm
  · intro k
    exact ((Commute.one_left (gen k)).smul_left _).add_left
      ((scalar_commutes k).smul_left _)
  · exact firstRow_in_plane hm


private theorem coe_inv_of_mul (u : Matrix12ˣ) (m : Matrix12) (hm : (u : Matrix12)*m=1) :
    (↑u⁻¹ : Matrix12)=m := by
  calc
    (↑u⁻¹ : Matrix12) = (↑u⁻¹ : Matrix12)*((u : Matrix12)*m) := by rw [hm,mul_one]
    _ = m := by rw [←mul_assoc,←Units.val_mul,inv_mul_cancel,Units.val_one,one_mul]
private def invA : Matrix12 := fromRows ![100,32,2,1,7,1705,3524,8,16,561,2074,1024]
private theorem coe_invA : (↑coreA⁻¹ : Matrix12)=invA := by
  apply coe_inv_of_mul
  rw [coe_coreA]
  decide +kernel
private def invB : Matrix12 := fromRows ![16,2,31,8,1,778,2048,938,2666,2624,3163,64]
private theorem coe_invB : (↑coreB⁻¹ : Matrix12)=invB := by
  apply coe_inv_of_mul
  rw [coe_coreB]
  decide +kernel
private def prefix0_1 : Matrix12 := fromRows ![2927,1705,32,100,70,3311,452,1,7,1275,1062,2074]
private theorem step0_1 : invA * invA = prefix0_1 := by decide +kernel
private def prefix0_2 : Matrix12 := fromRows ![2917,1699,778,2837,2077,1214,479,16,13,1248,3916,75]
private theorem step0_2 : prefix0_1 * matrixB = prefix0_2 := by decide +kernel
private def prefix0_3 : Matrix12 := fromRows ![224,164,1513,509,1040,570,3144,256,148,957,2154,147]
private theorem step0_3 : prefix0_2 * matrixA = prefix0_3 := by decide +kernel
private def prefix0_4 : Matrix12 := fromRows ![3005,3006,1362,3150,2304,652,3355,1639,2748,3931,1309,2732]
private theorem step0_4 : prefix0_3 * matrixA = prefix0_4 := by decide +kernel
private def lift0 : derivedGroup := coreGeneratorA⁻¹*coreGeneratorA⁻¹*coreGeneratorB*coreGeneratorA*coreGeneratorA
private theorem lift0_matrix : ((lift0 : Matrix12ˣ) : Matrix12)=u0 := by
  change (((coreA⁻¹*coreA⁻¹*coreB*coreA*coreA : Matrix12ˣ)) : Matrix12)=u0
  simp only [Units.val_mul,coe_coreA,coe_coreB,coe_invA,step0_1,step0_2,step0_3,step0_4]
  rfl
private theorem lift0_hexad : m22Hexad123.image (corePermutationAction lift0)=m22Hexad123 := by
  simp only [lift0,map_mul,map_inv,corePermutationAction_coreGeneratorA,corePermutationAction_coreGeneratorB]
  decide +kernel
private def prefix1_1 : Matrix12 := fromRows ![256,4,400,128,8,1513,1412,3659,1559,1681,3095,31]
private theorem step1_1 : invB * matrixA = prefix1_1 := by decide +kernel
private def prefix1_2 : Matrix12 := fromRows ![1639,28,3271,2976,128,1362,1499,3613,2586,418,3220,400]
private theorem step1_2 : prefix1_1 * matrixA = prefix1_2 := by decide +kernel
private def prefix1_3 : Matrix12 := fromRows ![2823,412,1579,2891,2976,3964,1108,3866,1802,3521,1848,3271]
private theorem step1_3 : prefix1_2 * matrixA = prefix1_3 := by decide +kernel
private def prefix1_4 : Matrix12 := fromRows ![103,2518,1291,2160,202,1837,1093,3130,3195,3531,3954,1980]
private theorem step1_4 : prefix1_3 * matrixB = prefix1_4 := by decide +kernel
private def prefix1_5 : Matrix12 := fromRows ![13,2372,3819,1177,2875,3579,2059,3074,3093,208,2544,1875]
private theorem step1_5 : prefix1_4 * matrixA = prefix1_5 := by decide +kernel
private def lift1 : derivedGroup := coreGeneratorB⁻¹*coreGeneratorA*coreGeneratorA*coreGeneratorA*coreGeneratorB*coreGeneratorA
private theorem lift1_matrix : ((lift1 : Matrix12ˣ) : Matrix12)=u1 := by
  change (((coreB⁻¹*coreA*coreA*coreA*coreB*coreA : Matrix12ˣ)) : Matrix12)=u1
  simp only [Units.val_mul,coe_coreA,coe_coreB,coe_invB,step1_1,step1_2,step1_3,step1_4,step1_5]
  rfl
private theorem lift1_hexad : m22Hexad123.image (corePermutationAction lift1)=m22Hexad123 := by
  simp only [lift1,map_mul,map_inv,corePermutationAction_coreGeneratorA,corePermutationAction_coreGeneratorB]
  decide +kernel
private def prefix2_1 : Matrix12 := fromRows ![7,32,64,1,100,512,1024,1185,3453,3061,412,3524]
private theorem step2_1 : invB * invA = prefix2_1 := by decide +kernel
private def prefix2_2 : Matrix12 := fromRows ![70,1705,3524,100,2927,561,2074,3807,1799,3365,28,452]
private theorem step2_2 : prefix2_1 * invA = prefix2_2 := by decide +kernel
private def prefix2_3 : Matrix12 := fromRows ![2077,1699,3524,2837,2917,2395,75,3573,3196,1396,22,479]
private theorem step2_3 : prefix2_2 * matrixB = prefix2_3 := by decide +kernel
private def prefix2_4 : Matrix12 := fromRows ![1040,164,64,509,224,624,147,330,3077,3942,280,3144]
private theorem step2_4 : prefix2_3 * matrixA = prefix2_4 := by decide +kernel
private def prefix2_5 : Matrix12 := fromRows ![2304,3006,31,3150,3005,535,2732,1788,3472,2284,2023,3355]
private theorem step2_5 : prefix2_4 * matrixA = prefix2_5 := by decide +kernel
private def prefix2_6 : Matrix12 := fromRows ![2602,222,4,1038,204,2636,2743,3757,1498,2295,1244,1642]
private theorem step2_6 : prefix2_5 * matrixB = prefix2_6 := by decide +kernel
private def lift2 : derivedGroup := coreGeneratorB⁻¹*coreGeneratorA⁻¹*coreGeneratorA⁻¹*coreGeneratorB*coreGeneratorA*coreGeneratorA*coreGeneratorB
private theorem lift2_matrix : ((lift2 : Matrix12ˣ) : Matrix12)=u2 := by
  change (((coreB⁻¹*coreA⁻¹*coreA⁻¹*coreB*coreA*coreA*coreB : Matrix12ˣ)) : Matrix12)=u2
  simp only [Units.val_mul,coe_coreA,coe_coreB,coe_invA,coe_invB,step2_1,step2_2,step2_3,step2_4,step2_5,step2_6]
  rfl
private theorem lift2_hexad : m22Hexad123.image (corePermutationAction lift2)=m22Hexad123 := by
  simp only [lift2,map_mul,map_inv,corePermutationAction_coreGeneratorA,corePermutationAction_coreGeneratorB]
  decide +kernel
private def liftGen : Fin 3 → derivedGroup := ![lift0,lift1,lift2]
private theorem liftGen_matrix (k : Fin 3) : ((liftGen k : Matrix12ˣ) : Matrix12)=gen k := by
  fin_cases k
  · exact lift0_matrix
  · exact lift1_matrix
  · exact lift2_matrix
private theorem liftGen_hexad (k : Fin 3) : m22Hexad123.image (corePermutationAction (liftGen k))=m22Hexad123 := by
  fin_cases k
  · exact lift0_hexad
  · exact lift1_hexad
  · exact lift2_hexad

/-- A unit commuting with the actual even hexad preimage is a cubic scalar. -/
theorem even_hexad_commuting_units (u : Matrix12ˣ)
    (hu : ∀ g : derivedGroup, m22Hexad123.image (corePermutationAction g)=m22Hexad123 →
      Commute u g.val) : u=1 ∨ u=scalarUnit ∨ u=scalarUnit^2 := by
  have hc (k : Fin 3) : Commute (u : Matrix12) (gen k) := by
    rw [←liftGen_matrix]
    exact (hu (liftGen k) (liftGen_hexad k)).map (Units.coeHom Matrix12)
  have he := commuting_matrix_form hc
  have ha : (u : Matrix12) 0 0=0 ∨ (u : Matrix12) 0 0=1 := by
    have hh : ∀ x : ZMod 2, x=0 ∨ x=1 := by decide +kernel
    exact hh _
  have hb : (u : Matrix12) 0 2=0 ∨ (u : Matrix12) 0 2=1 := by
    have hh : ∀ x : ZMod 2, x=0 ∨ x=1 := by decide +kernel
    exact hh _
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · simp only [ha,hb,zero_smul,zero_add] at he
    exact (Units.ne_zero u he).elim
  · rw [ha,hb,zero_smul,one_smul,zero_add] at he
    exact Or.inr (Or.inr (Units.ext (he.trans coe_scalarUnit_sq.symm)))
  · rw [ha,hb,zero_smul,one_smul,add_zero] at he
    exact Or.inl (Units.ext he)
  · rw [ha,hb,one_smul,one_smul] at he
    exact Or.inr (Or.inl (Units.ext (he.trans coe_scalarUnit.symm)))

open Janko4.InvolutionCentralizers.First.QuotientExtension M22TripleCover.Ambient

private theorem cube_eq_one_of_eq_inv {J : Type*} [Group J] (s : J)
    (hs : s^3=1) (he : s=s⁻¹) : s=1 := by
  have htwo : s*s=1 := (congrArg (fun x => x*s) he).trans (inv_mul_cancel s)
  have hthree : s*s*s=1 := by simpa only [pow_succ,pow_zero,one_mul] using hs
  rwa [htwo,one_mul] at hthree

private theorem cube_commute_of_square {J : Type*} [Group J] (s t : J)
    (hs : s^3=1) (hc : Commute (s^2) t) : Commute s t := by
  have he : s^2=s⁻¹ := eq_inv_of_mul_eq_one_left (by simpa only [←pow_succ] using hs)
  rw [he] at hc
  simpa only [inv_inv] using hc.inv_left

/-- The actual outer actor removes both nonidentity cubic scalars. -/
theorem even_hexad_outer_commuting_units (u : Matrix12ˣ)
    (hu : ∀ g : derivedGroup, m22Hexad123.image (corePermutationAction g)=m22Hexad123 →
      Commute u g.val) (t : actionGroup) (ht : t ∉ coverSubgroup)
    (hut : Commute u t.val) : u=1 := by
  have hn : ¬ Commute scalarUnit t.val := by
    intro hc
    have he := congrArg Subtype.val (triple_outer_conj_scalar t ht)
    change t.val*scalarUnit*t.val⁻¹=scalarUnit⁻¹ at he
    rw [hc.eq.symm,mul_assoc,mul_inv_cancel,mul_one] at he
    exact scalarUnit_ne_one (cube_eq_one_of_eq_inv scalarUnit scalarUnit_pow_three he)
  rcases even_hexad_commuting_units u hu with he | he | he
  · exact he
  · exact (hn (he ▸ hut)).elim
  · exact (hn (cube_commute_of_square scalarUnit t.val scalarUnit_pow_three (he ▸ hut))).elim
end Theory.GroupTheory.Recognition.JankoFour.SourceComparison.HexadCommutant
