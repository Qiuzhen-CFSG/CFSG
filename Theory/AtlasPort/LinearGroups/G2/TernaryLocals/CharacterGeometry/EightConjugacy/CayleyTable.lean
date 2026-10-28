module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.EightConjugacy.Frames
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.EightConjugacy.CayleyTable.Algebra
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The Cayley basis and table from an orthogonal triple

For an imaginary orthogonal triple `a,b,c`, with norms `1,1,r` and `c`
orthogonal to `ab`, the eight products `(1,a,b,ab,c,ac,bc,(ab)c)` have the
published Cayley multiplication table. The polarized triple identity gives
`a(bc) = -(ab)c`; the square and Moufang identities give the other upper
products. Conjugation reverses the products to give the lower half.

Taking traces of the table proves orthogonality. Multiplicativity of the norm
gives norms `1,1,1,1,r,r,r,r`, so nonzero `r` makes the frame independent.
Every identity is derived from the geometric hypotheses in `IsCayleyTriple`;
no automorphism, reference-frame conjugacy or multiplication table is assumed.

This is the octonion input to the two elementary-eight orbits in the actual
ternary G₂ model, used for Aschbacher–Smith, *The Classification of Quasithin
Groups*, Theorem 0.1.2(4), printed pp.3–4 and 481–482. The recognition
configuration on printed p.417 is not used as a coverage theorem. Coordinates
follow the licensed ATLAS port and Wilson's integral table, Eq. (4.11);
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.TernaryLocals.CharacterGeometry.EightConjugacy
open Atlas.SplitOctonion CayleyTable
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem pure_reassociate (x y z : V)
    (hx : trace x = 0) (hy : trace y = 0) (hz : trace z = 0)
    (hxy : normPolar x y = 0) (hxz : normPolar x z = 0)
    (hyz : normPolar y z = 0) (hxyz : normPolar (mul x y) z = 0) :
    mul x (mul y z) = -mul (mul x y) z := by
  apply eq_neg_of_add_eq_zero_left
  simpa [hxy, hxz, hyz, hxyz] using pure_triple_identity x y z hx hy hz

private theorem doubled_product (x y c : V) (hc : trace c = 0)
    (hxc : mul x c = -mul c x)
    (hcxy : mul c (mul x y) = -mul (mul x y) c) :
    mul (mul x c) (mul y c) = -norm c • mul x y := by
  rw [hxc, mul_neg_left, moufang_middle, hcxy, mul_neg_left, neg_neg,
    pure_right_square _ c hc]

/-- Every nonidentity vector of a geometric Cayley frame is imaginary. -/
theorem cayley_frame_trace (r : ZMod 3) (a b c : V) (h : IsCayleyTriple r a b c)
    (i : Fin 8) (hi : i ≠ 0) : trace (frame a b c i) = 0 := by
  have tp : trace (mul a b) = 0 := by
    rw [pure_mul_trace _ _ h.trace_a h.trace_b, h.polar_ab, neg_zero]
  have tq : trace (mul a c) = 0 := by
    rw [pure_mul_trace _ _ h.trace_a h.trace_c, h.polar_ac, neg_zero]
  have ts : trace (mul b c) = 0 := by
    rw [pure_mul_trace _ _ h.trace_b h.trace_c, h.polar_bc, neg_zero]
  have tt : trace (mul (mul a b) c) = 0 := by
    rw [pure_mul_trace _ _ tp h.trace_c, h.polar_abc, neg_zero]
  fin_cases i <;> simp_all [frame, h.trace_a, h.trace_b, h.trace_c]

/-- The first four norms are one; the last four norms equal the third generator norm. -/
theorem cayley_frame_norm (r : ZMod 3) (a b c : V) (h : IsCayleyTriple r a b c)
    (i : Fin 8) : norm (frame a b c i) = if i.val < 4 then 1 else r := by
  have hu : norm (unit : V) = 1 := by decide +kernel
  fin_cases i <;> simp [frame, hu, SplitOctonion.norm_mul, h.norm_a, h.norm_b, h.norm_c]

private theorem table_upper (r : ZMod 3) (a b c : V) (h : IsCayleyTriple r a b c)
    (i j : Fin 8) (hij : i ≤ j) :
    mul (frame a b c i) (frame a b c j) =
      coefficient r i j • frame a b c (CayleyEight.gradeSum i j) := by
  have tp : trace (mul a b) = 0 := cayley_frame_trace r a b c h 3 (by decide)
  have tq : trace (mul a c) = 0 := cayley_frame_trace r a b c h 5 (by decide)
  have ts : trace (mul b c) = 0 := cayley_frame_trace r a b c h 6 (by decide)
  have tt : trace (mul (mul a b) c) = 0 := cayley_frame_trace r a b c h 7 (by decide)
  have np : norm (mul a b) = 1 := by rw [SplitOctonion.norm_mul, h.norm_a, h.norm_b, mul_one]
  have nq : norm (mul a c) = r := by rw [SplitOctonion.norm_mul, h.norm_a, h.norm_c, one_mul]
  have ns : norm (mul b c) = r := by rw [SplitOctonion.norm_mul, h.norm_b, h.norm_c, one_mul]
  have nt : norm (mul (mul a b) c) = r := by rw [SplitOctonion.norm_mul, np, h.norm_c, one_mul]
  have ba : mul b a = -mul a b := flip_of_pure a b h.trace_a h.trace_b tp
  have ca : mul c a = -mul a c := flip_of_pure a c h.trace_a h.trace_c tq
  have cb : mul c b = -mul b c := flip_of_pure b c h.trace_b h.trace_c ts
  have cp : mul c (mul a b) = -mul (mul a b) c := flip_of_pure _ _ tp h.trace_c tt
  have ap : mul a (mul a b) = -b := by
    simpa only [h.norm_a, neg_one_smul] using pure_left_square a b h.trace_a
  have bp : mul b (mul a b) = a := by
    have he := pure_left_square b a h.trace_b
    rw [ba, mul_neg_right, h.norm_b, neg_one_smul] at he
    exact neg_injective he
  have aq : mul a (mul a c) = -c := by
    simpa only [h.norm_a, neg_one_smul] using pure_left_square a c h.trace_a
  have bs : mul b (mul b c) = -c := by
    simpa only [h.norm_b, neg_one_smul] using pure_left_square b c h.trace_b
  have pt : mul (mul a b) (mul (mul a b) c) = -c := by
    simpa only [np, neg_one_smul] using pure_left_square (mul a b) c tp
  have a_s : mul a (mul b c) = -mul (mul a b) c :=
    pure_reassociate _ _ _ h.trace_a h.trace_b h.trace_c
      h.polar_ab h.polar_ac h.polar_bc h.polar_abc
  have b_q : mul b (mul a c) = mul (mul a b) c := by
    have hp : normPolar b a = 0 := (normPolar_symm _ _).trans h.polar_ab
    have hp' : normPolar (mul b a) c = 0 := by simp [ba, h.polar_abc]
    simpa only [ba, mul_neg_left, neg_neg] using
      pure_reassociate _ _ _ h.trace_b h.trace_a h.trace_c
        hp h.polar_bc h.polar_ac hp'
  have a_t : mul a (mul (mul a b) c) = mul b c := by
    have he := pure_left_square a (mul b c) h.trace_a
    rw [a_s, mul_neg_right, h.norm_a, neg_one_smul] at he
    exact neg_injective he
  have b_t : mul b (mul (mul a b) c) = -mul a c := by
    have he := pure_left_square b (mul a c) h.trace_b
    simpa only [b_q, h.norm_b, neg_one_smul] using he
  have t_a : mul (mul (mul a b) c) a = -mul b c := by
    rw [flip_of_pure _ _ h.trace_a tt (by rw [a_t]; exact ts), a_t]
  have t_b : mul (mul (mul a b) c) b = mul a c := by
    rw [flip_of_pure _ _ h.trace_b tt (by rw [b_t, trace_neg, tq, neg_zero]), b_t,
      neg_neg]
  have p_q : mul (mul a b) (mul a c) = -mul b c := by
    have he := moufang_middle a b c
    rw [ca, mul_neg_right, a_s, mul_neg_left, t_a] at he
    exact neg_injective he
  have p_s : mul (mul a b) (mul b c) = mul a c := by
    have he := moufang_middle b a c
    simpa only [ba, cb, mul_neg_left, mul_neg_right, neg_neg, b_q, t_b] using he
  have c_q : mul c (mul a c) = r • a := by
    have he := pure_left_square c a h.trace_c
    rw [ca, mul_neg_right, h.norm_c, neg_smul] at he
    exact neg_injective he
  have c_s : mul c (mul b c) = r • b := by
    have he := pure_left_square c b h.trace_c
    rw [cb, mul_neg_right, h.norm_c, neg_smul] at he
    exact neg_injective he
  have c_t : mul c (mul (mul a b) c) = r • mul a b := by
    have he := pure_left_square c (mul a b) h.trace_c
    rw [cp, mul_neg_right, h.norm_c, neg_smul] at he
    exact neg_injective he
  have q_s : mul (mul a c) (mul b c) = -r • mul a b := by
    exact (doubled_product a b c h.trace_c
      (pure_anticomm a c h.trace_a h.trace_c h.polar_ac) cp).trans (by rw [h.norm_c])
  have q_t : mul (mul a c) (mul (mul a b) c) = r • b := by
    have hp : mul c (mul a (mul a b)) = -mul (mul a (mul a b)) c := by
      simp only [ap, mul_neg_left, mul_neg_right, cb, neg_neg]
    simpa only [h.norm_c, ap, smul_neg, neg_smul, neg_neg] using
      doubled_product a (mul a b) c h.trace_c
        (pure_anticomm a c h.trace_a h.trace_c h.polar_ac) hp
  have s_t : mul (mul b c) (mul (mul a b) c) = -r • a := by
    have hp : mul c (mul b (mul a b)) = -mul (mul b (mul a b)) c := by rw [bp, ca]
    simpa only [h.norm_c, bp] using
      doubled_product b (mul a b) c h.trace_c
        (pure_anticomm b c h.trace_b h.trace_c h.polar_bc) hp
  have aa := pure_square a h.trace_a
  have bb := pure_square b h.trace_b
  have cc := pure_square c h.trace_c
  have pp := pure_square (mul a b) tp
  have qq := pure_square (mul a c) tq
  have ss := pure_square (mul b c) ts
  have tt' := pure_square (mul (mul a b) c) tt
  fin_cases i <;> fin_cases j <;>
    simp_all [frame, coefficient, CayleyEight.gradeSum, CayleyEight.twist,
      unit_mul, mul_unit, h.norm_a, h.norm_b, h.norm_c] <;> rfl

private theorem gradeSum_comm (i j : Fin 8) :
    CayleyEight.gradeSum i j = CayleyEight.gradeSum j i :=
  (by decide +kernel : ∀ i j, CayleyEight.gradeSum i j = CayleyEight.gradeSum j i) i j

private theorem gradeSum_ne_zero (i j : Fin 8) (hij : i ≠ j) :
    CayleyEight.gradeSum i j ≠ 0 :=
  (by decide +kernel : ∀ i j, i ≠ j → CayleyEight.gradeSum i j ≠ 0) i j hij

private theorem coefficient_skew (r : ZMod 3) (i j : Fin 8)
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    coefficient r j i = -coefficient r i j :=
  (by decide +kernel : ∀ r i j, i ≠ 0 → j ≠ 0 → i ≠ j →
    coefficient r j i = -coefficient r i j) r i j hi hj hij

/-- All 64 multiplication identities, derived from the geometric triple hypotheses. -/
theorem cayley_frame_mul (r : ZMod 3) (a b c : V) (h : IsCayleyTriple r a b c)
    (i j : Fin 8) :
    mul (frame a b c i) (frame a b c j) =
      coefficient r i j • frame a b c (CayleyEight.gradeSum i j) := by
  by_cases hij : i ≤ j
  · exact table_upper r a b c h i j hij
  by_cases hj : j = 0
  · subst j
    have hc : coefficient r i 0 = 1 :=
      (by decide +kernel : ∀ r i, coefficient r i 0 = 1) r i
    have hg : CayleyEight.gradeSum i 0 = i :=
      (by decide +kernel : ∀ i, CayleyEight.gradeSum i 0 = i) i
    rw [hc, hg, one_smul]
    exact mul_unit _
  have hi : i ≠ 0 := by
    intro hi
    subst i
    exact hij (Fin.zero_le _)
  have hne : i ≠ j := by
    intro he
    subst j
    exact hij le_rfl
  have hji := table_upper r a b c h j i (le_of_not_ge hij)
  have htji : trace (mul (frame a b c j) (frame a b c i)) = 0 := by
    rw [hji, trace_smul, cayley_frame_trace r a b c h _ (gradeSum_ne_zero j i hne.symm), mul_zero]
  rw [flip_of_pure _ _ (cayley_frame_trace r a b c h j hj)
    (cayley_frame_trace r a b c h i hi) htji, hji, coefficient_skew r i j hi hj hne,
    neg_smul, neg_neg, gradeSum_comm j i]

/-- Distinct vectors of a geometric Cayley frame are orthogonal for the norm pairing. -/
theorem cayley_frame_orthogonal (r : ZMod 3) (a b c : V) (h : IsCayleyTriple r a b c)
    (i j : Fin 8) (hij : i ≠ j) : normPolar (frame a b c i) (frame a b c j) = 0 := by
  have hm : trace (frame a b c i) * trace (frame a b c j) = 0 := by
    by_cases hi : i = 0
    · have hj : j ≠ 0 := by intro hj; exact hij (hi.trans hj.symm)
      rw [cayley_frame_trace r a b c h j hj, mul_zero]
    · rw [cayley_frame_trace r a b c h i hi, zero_mul]
  have he := trace_mul_identity (frame a b c i) (frame a b c j)
  rw [cayley_frame_mul r a b c h, trace_smul,
    cayley_frame_trace r a b c h _ (gradeSum_ne_zero i j hij), mul_zero, hm, zero_sub] at he
  exact neg_eq_zero.mp he.symm

/-- The Cayley basis and complete table for any normalized geometric triple. -/
theorem cayley_basis_and_table (r : ZMod 3) (a b c : V) (h : IsCayleyTriple r a b c) :
    LinearIndependent (ZMod 3) (frame a b c) ∧ ∀ i j,
      mul (frame a b c i) (frame a b c j) =
        coefficient r i j • frame a b c (CayleyEight.gradeSum i j) := by
  refine ⟨?_, cayley_frame_mul r a b c h⟩
  apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := normPolar)
  · exact cayley_frame_orthogonal r a b c h
  · intro i
    rw [normPolar_self, cayley_frame_norm r a b c h]
    apply mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0)
    split_ifs
    · exact one_ne_zero
    · exact h.norm_c_ne

end Atlas.G2.TernaryLocals.CharacterGeometry.EightConjugacy
