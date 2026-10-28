module

public import Theory.SpecificGroups.PSL3.SylowFixedActions.Standard.TwoSubgroup
public import Theory.SpecificGroups.PSL3.SylowFixedActions.Standard.ScalarLift
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm
public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Theory.SpecificGroups.SL2.SylowInnerFixer
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Involutions fixing Sylow two-subgroups of odd-prime PSL₃ are inner

Choose a Sylow two-subgroup of the actual determinant-corrected GL₂ block
containing the diagonal sign matrices and coordinate interchange. Its image
in PSL₃ is contained in an ambient Sylow, which can be conjugated to the
prescribed Sylow. The odd-prime automorphism normal form leaves a linear
actor or a linear-times-graph actor.

The sign tests force the graph conjugator to be diagonal, with equal first
two entries. Cubic central discrepancies vanish on every element of two-power
order. Thus every fixed matrix in the determinant-one block has the form
`!![a,b;-b,a]`, and these matrices commute. Restriction to the normal
determinant kernel gives an actual SL₂ Sylow two-subgroup, contradicting its
noncommutativity over an odd field of order greater than three. The remaining
linear involution is inner by the determinant correction for its cube.

The normality used for Sylow restriction is precisely normality of the GL₂
determinant kernel. No claim about an arbitrary centralizer intersection is
needed, and the canonical projective quotient retains its cubic center.

Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.503 (PDF p.520) of
`refs/quasithin.pdf`, the assertion that Sylow fixation makes the odd A₂
involution inner. Standard automorphism coverage is the checked GLS3
Theorem 2.5.12(a) and §2.7 development imported by `OddInvolutionFixed.NormalForm`.
-/

public section

open scoped MatrixGroups
open Subgroup
namespace Matrix.PSL3.SylowFixedActions.OddPrime
open Matrix.PSL3.OuterSolvable Matrix.PSL3.SylowFixedActions.Standard
variable {F : Type*} [Field F] [Finite F]

/-- The cubic scalar kernel separates elements of two-power order. -/
theorem eq_of_projection_eq_of_two_pow {x y : SL(3, F)} {n : ℕ}
    (hx : x ^ (2 ^ n) = 1) (hy : y ^ (2 ^ n) = 1)
    (h : projection F x = projection F y) : x = y := by
  let z := x⁻¹ * y
  have hz : z ∈ center SL(3, F) := QuotientGroup.eq.mp h
  have hcomm : Commute x z := mem_center_iff.mp hz x
  have hyz : y = x * z := by simp [z]
  have hzn : z ^ (2 ^ n) = 1 := by
    rw [hyz, hcomm.mul_pow, hx, one_mul] at hy
    exact hy
  have hz3 : orderOf z ∣ 3 := by
    have h := (orderOf_dvd_natCard (⟨z, hz⟩ : center SL(3, F))).trans
      (Matrix.SL3.card_center_dvd_three F)
    rwa [← orderOf_injective (center SL(3, F)).subtype Subtype.val_injective ⟨z, hz⟩] at h
  have hd : orderOf z ∣ 1 := by
    have hcop : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by decide : Nat.Coprime 2 3)
    simpa only [hcop.gcd_eq_one] using
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzn) hz3
  have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  simpa only [hz1, mul_one] using hyz.symm

/-- Projective fixation lifts literally on every element of two-power order. -/
theorem centerAction_fixes_of_two_pow (a : MulAut SL(3, F))
    (x : SL(3, F)) {n : ℕ} (hx : x ^ (2 ^ n) = 1)
    (hfix : centerAction F a (projection F x) = projection F x) : a x = x := by
  apply eq_of_projection_eq_of_two_pow (x := a x) (y := x) _ hx hfix
  rw [← map_pow, hx, map_one]

omit [Finite F] in
private theorem neg_one_pow_four : (-1 : Fˣ) ^ 4 = 1 := by
  apply Units.ext
  norm_num

omit [Finite F] in
private theorem sign_graph (x : SL(3, F)) (hx : x ^ 2 = 1)
    (ht : x.val.transpose = x.val) : graphSL F x = x := by
  change (SpecialLinearGroup.transpose x)⁻¹ = x
  have he : SpecialLinearGroup.transpose x = x := Subtype.ext ht
  rw [he]
  exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)

omit [Finite F] in
private theorem graph_fixes_sign_tests (x : SL(3, F))
    (hx : x = testDiagonal₁ F (-1) ∨ x = testDiagonal₂ F (-1) ∨ x = interchange F) :
    graphSL F x = x := by
  rcases hx with rfl | rfl | rfl
  · apply sign_graph
    · change diagonalSL F (-1, (-1)⁻¹) ^ 2 = 1
      rw [← map_pow]
      have h : ((-1, (-1)⁻¹) : Fˣ × Fˣ) ^ 2 = 1 := by ext <;> simp
      rw [h, map_one]
    · exact Matrix.isSymm_diagonal _
  · apply sign_graph
    · change diagonalSL F (1, -1) ^ 2 = 1
      rw [← map_pow]
      have h : ((1, -1) : Fˣ × Fˣ) ^ 2 = 1 := by ext <;> simp
      rw [h, map_one]
    · exact Matrix.isSymm_diagonal _
  · apply sign_graph _ (interchange_sq F)
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

private theorem linear_commutes_of_sign_fix (g : GL (Fin 3) F) (x : SL(3, F))
    (hx : x ^ 4 = 1) (hgraph : graphSL F x = x)
    (hfix : (linearConj F g * graph F) (projection F x) = projection F x) :
    g.val * x.val = x.val * g.val := by
  have hs := (centerAction_fixes_iff_of_pow_four F
    (linearConjSL F g * graphSL F) x hx).mp hfix
  change linearConjSL F g (graphSL F x) = x at hs
  rw [hgraph] at hs
  have he := congrArg SpecialLinearGroup.toGL hs
  rw [linearConjSL_toGL] at he
  exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp he)

omit [Finite F] in
private theorem intertwining_entry_zero (g : Matrix (Fin 3) (Fin 3) F)
    (d : Fin 3 → F) (h : g * Matrix.diagonal d = Matrix.diagonal d * g)
    (i j : Fin 3) (hne : d j ≠ d i) : g i j = 0 := by
  have he := congrArg (fun m => m i j) h
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  by_contra hn
  exact hne (mul_left_cancel₀ hn (he.trans (mul_comm _ _)))

/-- Fixing the two diagonal signs and interchange determines the graph
conjugator up to scalars on the two coordinate blocks. -/
theorem graph_sign_fixer_shape (h2 : (2 : F) ≠ 0) (g : GL (Fin 3) F)
    (hfix : ∀ x ∈ testSet F (-1), (linearConj F g * graph F) x = x) :
    (∀ i j, i ≠ j → g.val i j = 0) ∧ g.val 0 0 = g.val 1 1 := by
  have h₁ := linear_commutes_of_sign_fix g (testDiagonal₁ F (-1))
    (testDiagonal₁_pow_four F (-1) neg_one_pow_four)
    (graph_fixes_sign_tests _ (Or.inl rfl)) (hfix _ (by simp [testSet]))
  have h₂ := linear_commutes_of_sign_fix g (testDiagonal₂ F (-1))
    (testDiagonal₂_pow_four F (-1) neg_one_pow_four)
    (graph_fixes_sign_tests _ (Or.inr (Or.inl rfl))) (hfix _ (by simp [testSet]))
  have hv₁ : (testDiagonal₁ F (-1)).val = Matrix.diagonal ![-1, -1, 1] := by
    simp [testDiagonal₁]
  have hv₂ : (testDiagonal₂ F (-1)).val = Matrix.diagonal ![1, -1, -1] := by
    simp [testDiagonal₂]
  rw [hv₁] at h₁
  rw [hv₂] at h₂
  have hn : (-1 : F) ≠ 1 := by intro h; apply h2; linear_combination -h
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact False.elim (hij rfl)
      | exact intertwining_entry_zero g.val _ h₁ _ _ hn
      | exact intertwining_entry_zero g.val _ h₁ _ _ hn.symm
      | exact intertwining_entry_zero g.val _ h₂ _ _ hn
      | exact intertwining_entry_zero g.val _ h₂ _ _ hn.symm
  · have hw4 : interchange F ^ 4 = 1 := by
      rw [show 4 = 2 * 2 from rfl, pow_mul, interchange_sq, one_pow]
    have hw := linear_commutes_of_sign_fix g (interchange F) hw4
      (graph_fixes_sign_tests _ (Or.inr (Or.inr rfl))) (hfix _ (by simp [testSet]))
    have he := congrArg (fun m => m 0 1) hw
    simpa [interchange, Matrix.mul_apply, Fin.sum_univ_three] using he

omit [Finite F] in
/-- Place all three sign tests in the projective image of one Sylow
two-subgroup of the actual GL₂ block. -/
theorem exists_block_sylow_containing_sign_tests (h2 : (2 : F) ≠ 0) :
    ∃ T : Sylow 2 (GL (Fin 2) F), ∀ x ∈ testSet F (-1),
      ∃ A ∈ T, projection F (SL3.blockEmbedding F A) = x := by
  let K := (powMonoidHom 2 : (Fˣ × Fˣ) →* (Fˣ × Fˣ)).ker
  let D := K.map (diagonalSL F)
  have hK : IsPGroup 2 K := by
    intro a
    refine ⟨1, ?_⟩
    exact Subtype.ext a.property
  have hD : IsPGroup 2 D := hK.map (diagonalSL F)
  have hconj : ∀ x ∈ D, interchange F * x * (interchange F)⁻¹ ∈ D := by
    rintro x ⟨a, ha, rfl⟩
    refine ⟨(a.2, a.1), ?_, (interchange_diagonalSL F a).symm⟩
    change (a.2, a.1) ^ 2 = (1 : Fˣ × Fˣ)
    change a ^ 2 = 1 at ha
    exact Prod.ext (congrArg Prod.snd ha) (congrArg Prod.fst ha)
  have hn : interchange F ∈ normalizer D := by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hconj x, fun hx => ?_⟩
    have hh := hconj _ hx
    have heq : interchange F * (interchange F * x * (interchange F)⁻¹) *
        (interchange F)⁻¹ = x := by
      calc
        _ = interchange F ^ 2 * x * (interchange F ^ 2)⁻¹ := by
          simp only [pow_two, _root_.mul_inv_rev, mul_assoc]
        _ = x := by rw [interchange_sq]; simp
    rwa [heq] at hh
  have hw : IsPGroup 2 (zpowers (interchange F)) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (interchange_sq F))
  let H := D ⊔ zpowers (interchange F)
  have hH : IsPGroup 2 H := hD.to_sup_of_normal_left' hw (zpowers_le.mpr hn)
  have hrange : H ≤ (SL3.blockEmbedding F).range := by
    rw [SL3.blockEmbedding_range F h2]
    apply sup_le
    · rintro x ⟨u, _, rfl⟩
      apply (SL3.mem_standardInvolution_centralizer_iff F h2 _).mpr
      exact ⟨by simp, by simp, by simp, by simp⟩
    · apply zpowers_le.mpr
      apply (SL3.mem_standardInvolution_centralizer_iff F h2 _).mpr
      exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨T, hT⟩ := (hH.comap_of_injective (SL3.blockEmbedding F)
    (SL3.blockEmbedding_injective F)).exists_le_sylow
  have hlift (x : SL(3, F)) (hx : x ∈ H) :
      ∃ A ∈ T, projection F (SL3.blockEmbedding F A) = projection F x := by
    obtain ⟨A, rfl⟩ := hrange hx
    exact ⟨A, hT hx, rfl⟩
  refine ⟨T, ?_⟩
  intro x hx
  simp only [testSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · apply hlift
    apply (le_sup_left : D ≤ H)
    refine ⟨(-1, (-1)⁻¹), ?_, rfl⟩
    change ((-1, (-1)⁻¹) : Fˣ × Fˣ) ^ 2 = 1
    ext <;> simp
  · apply hlift
    apply (le_sup_left : D ≤ H)
    refine ⟨(1, -1), ?_, rfl⟩
    change ((1, -1) : Fˣ × Fˣ) ^ 2 = 1
    ext <;> simp
  · exact hlift _ ((le_sup_right : zpowers (interchange F) ≤ H) (mem_zpowers _))

omit [Finite F] in
private theorem blockSL_val (x : SL(2, F)) :
    (SL3.blockEmbedding F (SpecialLinearGroup.toGL x)).val =
      !![x 0 0, x 0 1, 0; x 1 0, x 1 1, 0; 0, 0, 1] := by
  change !![x 0 0, x 0 1, 0; x 1 0, x 1 1, 0;
    0, 0, ↑((GeneralLinearGroup.det (SpecialLinearGroup.toGL x))⁻¹)] = _
  rw [SpecialLinearGroup.coeToGL_det]
  rfl

private theorem graph_fixed_block_shape (g : GL (Fin 3) F)
    (hd : ∀ i j, i ≠ j → g.val i j = 0) (heq : g.val 0 0 = g.val 1 1)
    (x : SL(2, F)) {n : ℕ} (hx : (SpecialLinearGroup.toGL x) ^ (2 ^ n) = 1)
    (hfix : (linearConj F g * graph F)
      (projection F (SL3.blockEmbedding F (SpecialLinearGroup.toGL x))) =
        projection F (SL3.blockEmbedding F (SpecialLinearGroup.toGL x))) :
    x 0 0 = x 1 1 ∧ x 0 1 = -x 1 0 := by
  have hpow : (SL3.blockEmbedding F (SpecialLinearGroup.toGL x)) ^ (2 ^ n) = 1 := by
    rw [← map_pow, hx, map_one]
  have hf := centerAction_fixes_of_two_pow (linearConjSL F g * graphSL F)
    (SL3.blockEmbedding F (SpecialLinearGroup.toGL x)) hpow hfix
  change linearConjSL F g (graphSL F _) = _ at hf
  have hm := congrArg SpecialLinearGroup.toGL hf
  rw [linearConjSL_toGL, OddInvolutionFixed.graphSL_toGL] at hm
  have hm' := congrArg Units.val (mul_inv_eq_iff_eq_mul.mp hm)
  change g.val * (SL3.blockEmbedding F (SpecialLinearGroup.toGL x))⁻¹.val.transpose =
    (SL3.blockEmbedding F (SpecialLinearGroup.toGL x)).val * g.val at hm'
  have hi : (SL3.blockEmbedding F (SpecialLinearGroup.toGL x))⁻¹ =
      SL3.blockEmbedding F (SpecialLinearGroup.toGL x⁻¹) := by rw [map_inv, map_inv]
  rw [hi, blockSL_val, blockSL_val] at hm'
  have hdet : g.val 0 0 * g.val 1 1 * g.val 2 2 ≠ 0 := by
    have h := (GeneralLinearGroup.det g).ne_zero
    change Matrix.det g.val ≠ 0 at h
    simpa [Matrix.det_fin_three, hd 0 1 (by decide), hd 0 2 (by decide),
      hd 1 0 (by decide), hd 1 2 (by decide), hd 2 0 (by decide), hd 2 1 (by decide)] using h
  have ha : g.val 0 0 ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hdet).1).1
  have h00 := congrArg (fun m => m 0 0) hm'
  have h01 := congrArg (fun m => m 0 1) hm'
  have hiv : x⁻¹.val = !![x 1 1, -x 0 1; -x 1 0, x 0 0] :=
    Matrix.adjugate_fin_two x.val
  have hs : g.val 0 0 * x 1 1 = g.val 0 0 * x 0 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, hd, hiv, mul_comm] using h00
  have ht : g.val 0 0 * (-x 1 0) = g.val 0 0 * x 0 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, hd, hiv, ← heq, mul_comm] using h01
  exact ⟨(mul_left_cancel₀ ha hs).symm, (mul_left_cancel₀ ha ht).symm⟩

/-- A graph-coset automorphism cannot fix the chosen GL₂ Sylow image:
its determinant-kernel restriction would make an SL₂ Sylow commutative. -/
theorem graph_not_fixes_block_sylow (ho : Odd (Nat.card F)) (hl : 3 < Nat.card F)
    (T : Sylow 2 (GL (Fin 2) F))
    (htests : ∀ x ∈ testSet F (-1), ∃ A ∈ T,
      projection F (SL3.blockEmbedding F A) = x)
    (g : GL (Fin 3) F)
    (hfix : ∀ A ∈ T, (linearConj F g * graph F)
      (projection F (SL3.blockEmbedding F A)) = projection F (SL3.blockEmbedding F A)) : False := by
  have h2 : (2 : F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F ho
  obtain ⟨hd, heq⟩ := graph_sign_fixer_shape h2 g (by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := htests x hx
    exact hfix A hA)
  let D := (GeneralLinearGroup.det (n := Fin 2) (R := F)).ker
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal D
  let e : SL(2, F) ≃* D := {
    toFun x := ⟨SpecialLinearGroup.toGL x, SpecialLinearGroup.coeToGL_det x⟩
    invFun x := ⟨x.val.val, congrArg Units.val x.property⟩
    left_inv _ := rfl
    right_inv _ := Subtype.ext (Units.ext rfl)
    map_mul' x y := Subtype.ext (SpecialLinearGroup.toGL.map_mul x y) }
  let R : Sylow 2 SL(2, F) := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hRT (x : R) : SpecialLinearGroup.toGL x.val ∈ T := by
    obtain ⟨d, hdS, hdx⟩ := x.property
    have hdT : d.val ∈ T := by
      change d ∈ (T : Subgroup (GL (Fin 2) F)).subgroupOf D
      rw [← hS]
      exact hdS
    have hx : SpecialLinearGroup.toGL x.val = d.val := by
      rw [← hdx]
      exact Units.ext rfl
    rwa [hx]
  have hshape (x : R) : x.val 0 0 = x.val 1 1 ∧ x.val 0 1 = -x.val 1 0 := by
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨SpecialLinearGroup.toGL x.val, hRT x⟩
    have hn' : (SpecialLinearGroup.toGL x.val) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    exact graph_fixed_block_shape g hd heq x.val hn' (hfix _ (hRT x))
  let : Group.IsPerfect SL(2, F) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hl
  apply SpecialLinearGroup.sylow_two_not_isMulCommutative ho R
  apply IsMulCommutative.of_comm
  intro x y
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val * y.val.val = y.val.val * x.val.val
  obtain ⟨hx0, hx1⟩ := hshape x
  obtain ⟨hy0, hy1⟩ := hshape y
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hx0, hx1, hy0, hy1] <;> ring

/-- Every involution fixing a Sylow two-subgroup of simple perfect PSL₃ over
an odd prime field of order greater than three is inner. -/
theorem involution_mem_inner_of_fixes_sylow
    [IsSimpleGroup PSL(3, F)] [Group.IsPerfect PSL(3, F)]
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (Q : Sylow 2 PSL(3, F)) (a : MulAut PSL(3, F)) (ha : orderOf a = 2)
    (hfix : ∀ x ∈ Q, a x = x) : a ∈ MulAut.innerSubgroup PSL(3, F) := by
  have hoF : Odd (Nat.card F) := hF ▸ ho
  have hlF : 3 < Nat.card F := hF ▸ hl
  have h2 : (2 : F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F hoF
  obtain ⟨T, htests⟩ := exists_block_sylow_containing_sign_tests h2
  let f : GL (Fin 2) F →* PSL(3, F) := (projection F).comp (SL3.blockEmbedding F)
  obtain ⟨S, hS⟩ := (T.isPGroup'.map f).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq PSL(3, F) S Q
  let e := MulAut.conj c
  have hm : (S : Subgroup PSL(3, F)).map e.toMonoidHom = Q :=
    congrArg Sylow.toSubgroup hc
  let b : MulAut PSL(3, F) := (MulAut.congr e.symm) a
  have hbfix (A : GL (Fin 2) F) (hA : A ∈ T) : b (f A) = f A := by
    change e.symm (a (e (f A))) = f A
    have hAQ : e (f A) ∈ (Q : Subgroup PSL(3, F)) := by
      rw [← hm]
      exact mem_map_of_mem e.toMonoidHom (hS (mem_map_of_mem f hA))
    rw [hfix _ hAQ, e.symm_apply_apply]
  have hb2 : b ^ 2 = 1 := by
    change ((MulAut.congr e.symm) a) ^ 2 = 1
    rw [← map_pow, show a ^ 2 = 1 from ha ▸ pow_orderOf_eq_one a, map_one]
  have hbinner : b ∈ MulAut.innerSubgroup PSL(3, F) := by
    obtain ⟨g, hg | hg⟩ := OddInvolutionFixed.automorphism_normal_form
      (Group.IsPerfect.not_isSolvable PSL(3, F)) hp ho hF b
    · rw [hg] at hb2 ⊢
      exact OddInvolutionFixed.linearConj_involution_inner g hb2
    · exact (graph_not_fixes_block_sylow hoF hlF T htests g (by
        intro A hA
        have h := hbfix A hA
        rw [hg] at h
        exact h)).elim
  have heq : a = e * b * e⁻¹ := by
    ext x
    change a x = e (e.symm (a (e (e.symm x))))
    simp
  rw [heq]
  exact (MulAut.innerSubgroup_normal PSL(3, F)).conj_mem b hbinner e

end Matrix.PSL3.SylowFixedActions.OddPrime
