module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.CoordinateReduction
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.Weyl
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.CentralSwap
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.ShortCommutators

/-!
# Root conjugators for the middle Ree involution tail

Every nonidentity word x₄(b)y₅(c)y₃(e) is conjugate to one of the two
marked root curves, in the actual fixed Ree group. If b is nonzero, x₁
conjugation removes e; the fixed linear Weyl word interchanges c and e,
and another x₁ conjugation leaves only x₄(b). If b is zero and e is
nonzero, x₈ conjugation removes c and the same Weyl word sends y₃(e)
to y₅(e). The remaining case is already on the long-root curve.

Source: GLS3 Table 2.4 and 2.4.5(d); this is part of the involution-class
calculation used in Guralnick--Malle, *Classification of 2F-modules, II*,
Lemma 8.8, internal p.57. Full tail compression and D₂ transport are
separate obligations assembled by `DConjugacy`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics EvenInvolutionGeometry
open ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.Binary.FixedGeometry
open MatrixRelations.LongCommutators

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (MatrixRelations.longRoot_isLong i), halfFrobenius]

private theorem central_fifth_eq (m : ℕ) (a : CoefficientField m) :
    centralElement m 4 a = longRootElement m a := by
  apply toSplitGroup_injective m
  rw [centralElement_coe, longRootElement_coe]

private theorem main_fourth_eq (m : ℕ) (a : CoefficientField m) :
    mainElement m 3 a = shortRootElement m a := by
  apply toSplitGroup_injective m
  rw [mainElement_coe, shortRootElement_coe]

private theorem middle_product (m : ℕ) (b c e : CoefficientField m) :
    tailElement m ![0, b, c, 0, e] =
      mainElement m 3 b * centralElement m 4 c * centralElement m 2 e := by
  simp [tailElement_eq_product]

private theorem central_fifth_commute (m : ℕ) (a : CoefficientField m)
    (x : Model m) (hx : x ∈ unipotent m) : Commute (centralElement m 4 a) x := by
  rw [central_fifth_eq]
  exact longRootElement_commute_unipotent m a x hx

private theorem first_third_commute (m : ℕ) (a e : CoefficientField m) :
    Commute (mainElement m 0 a) (centralElement m 2 e) := by
  change _ * _ = _ * _
  apply toSplitGroup_injective m
  simp only [map_mul, mainElement_coe, centralElement_coe]
  change Commute (rootWord m 0 a) (centralWord m 2 e)
  have h0 : rootWord m 0 a = MatrixRelations.LongCommutators.X m 0 a * MatrixRelations.LongCommutators.X m 1 (halfFrobenius m a) *
      MatrixRelations.LongCommutators.X m 2 (a * halfFrobenius m a) := by
    simp only [rootWord, fieldEnd_half]
    rfl
  have h2 : centralWord m 2 e = MatrixRelations.LongCommutators.X m 9 e * MatrixRelations.LongCommutators.X m 8 (halfFrobenius m e) := by
    simp only [centralWord, fieldEnd_half]
    rfl
  rw [h0, h2]
  apply Commute.mul_right <;> refine Commute.mul_left (Commute.mul_left ?_ ?_) ?_
  all_goals exact xc m _ _ (by norm_num [V, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]) _ _

private theorem fourth_third_commute (m : ℕ) (b e : CoefficientField m) :
    Commute (mainElement m 3 b) (centralElement m 2 e) := by
  change _ * _ = _ * _
  apply toSplitGroup_injective m
  simp only [map_mul, mainElement_coe, centralElement_coe]
  change Commute (rootWord m 3 b) (centralWord m 2 e)
  have h2 : centralWord m 2 e = MatrixRelations.LongCommutators.X m 9 e * MatrixRelations.LongCommutators.X m 8 (halfFrobenius m e) := by
    simp only [centralWord, fieldEnd_half]
    rfl
  rw [OuterElimination.word_3, h2]
  apply Commute.mul_right <;> apply Commute.mul_left
  all_goals exact xc m _ _ (by norm_num [V, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]) _ _

private theorem first_conj_fourth (m : ℕ) (t b : CoefficientField m) :
    (mainElement m 0 t)⁻¹ * mainElement m 3 b * mainElement m 0 t =
      mainElement m 3 b * centralElement m 2 (t * b) := by
  have h : (mainElement m 0 t)⁻¹ * (mainElement m 3 b)⁻¹ *
      mainElement m 0 t * mainElement m 3 b = centralElement m 2 (t * b) := by
    apply toSplitGroup_injective m
    simpa only [map_mul, map_inv, mainElement_coe, centralElement_coe] using
      rootWord_first_fourth_commutator m t b
  have hb : (mainElement m 3 b)⁻¹ = mainElement m 3 b := by
    apply inv_eq_of_mul_eq_one_left
    rw [← mainElement_add m 3 (by decide), CharTwo.add_self_eq_zero, mainElement_zero]
  calc
    _ = ((mainElement m 0 t)⁻¹ * (mainElement m 3 b)⁻¹ *
        mainElement m 0 t * mainElement m 3 b) * (mainElement m 3 b)⁻¹ := by
      conv_lhs => rw [← hb]
      group
    _ = centralElement m 2 (t * b) * mainElement m 3 b := by rw [h, hb]
    _ = _ := (fourth_third_commute m b (t * b)).eq.symm

/-- Conjugation by the first main curve changes only the central third
parameter of the middle tail. -/
theorem first_conj_middle (m : ℕ) (t b c e : CoefficientField m) :
    (mainElement m 0 t)⁻¹ * tailElement m ![0, b, c, 0, e] * mainElement m 0 t =
      tailElement m ![0, b, c, 0, e + t * b] := by
  let f := MulAut.conj (mainElement m 0 t)⁻¹
  have h4 : f (mainElement m 3 b) =
      mainElement m 3 b * centralElement m 2 (t * b) := by
    simpa only [f, MulAut.conj_apply, inv_inv] using first_conj_fourth m t b
  have h5 : f (centralElement m 4 c) = centralElement m 4 c := by
    change (mainElement m 0 t)⁻¹ * centralElement m 4 c *
      ((mainElement m 0 t)⁻¹)⁻¹ = _
    rw [((central_fifth_commute m c _ (mainElement_mem_unipotent m 0 t)).symm.inv_left).eq]
    simp [mul_assoc]
  have h3 : f (centralElement m 2 e) = centralElement m 2 e := by
    change (mainElement m 0 t)⁻¹ * centralElement m 2 e *
      ((mainElement m 0 t)⁻¹)⁻¹ = _
    rw [(first_third_commute m t e).inv_left.eq]
    simp [mul_assoc]
  change f (tailElement m ![0, b, c, 0, e]) = _
  rw [middle_product, map_mul, map_mul, h4, h5, h3, middle_product]
  have hc := central_fifth_commute m c (centralElement m 2 (t * b))
    (Y_le_unipotent m 2 (centralElement_mem_Y m 2 _))
  calc
    _ = mainElement m 3 b * centralElement m 4 c *
        (centralElement m 2 (t * b) * centralElement m 2 e) := by
      simp only [mul_assoc]
      rw [hc.symm.left_comm]
    _ = _ := by rw [← centralElement_add m 2 (by decide), add_comm (t * b) e]

/-- The fixed linear Weyl representative exchanges the central third and
fifth parameters and fixes the fourth main curve. -/
theorem linearWeyl_middle (m : ℕ) (b c e : CoefficientField m) :
    weylLift m .linear * tailElement m ![0, b, c, 0, e] * (weylLift m .linear)⁻¹ =
      tailElement m ![0, b, e, 0, c] := by
  let f := MulAut.conj (weylLift m .linear)
  change f (tailElement m ![0, b, c, 0, e]) = _
  have h3 := linearWeyl_main_fourth m b
  have h4 := linearWeyl_central_fifth m c
  have h2 := linearWeyl_central_third m e
  change f (mainElement m 3 b) = _ at h3
  change f (centralElement m 4 c) = _ at h4
  change f (centralElement m 2 e) = _ at h2
  rw [middle_product, map_mul, map_mul, h3, h4, h2, middle_product]
  rw [mul_assoc, (central_fifth_commute m e _
    (Y_le_unipotent m 2 (centralElement_mem_Y m 2 c))).eq.symm, ← mul_assoc]

/-- The eighth curve changes the central fifth parameter by e·t. -/
theorem eighth_conj_middle_zero (m : ℕ) (t c e : CoefficientField m) :
    (mainElement m 7 t)⁻¹ * tailElement m ![0, 0, c, 0, e] * mainElement m 7 t =
      tailElement m ![0, 0, c + e * t, 0, e] := by
  have hswap : centralElement m 2 e * mainElement m 7 t =
      mainElement m 7 t * centralElement m 2 e * centralElement m 4 (e * t) := by
    apply toSplitGroup_injective m
    simpa only [map_mul, centralElement_coe, mainElement_coe] using
      central_third_eighth_swap m e t
  have h := congrArg (fun z => (mainElement m 7 t)⁻¹ * z) hswap
  have h3 : (mainElement m 7 t)⁻¹ * centralElement m 2 e * mainElement m 7 t =
      centralElement m 2 e * centralElement m 4 (e * t) := by
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h
  let f := MulAut.conj (mainElement m 7 t)⁻¹
  have h3' : f (centralElement m 2 e) =
      centralElement m 2 e * centralElement m 4 (e * t) := by
    simpa only [f, MulAut.conj_apply, inv_inv] using h3
  have h5 : f (centralElement m 4 c) = centralElement m 4 c := by
    change (mainElement m 7 t)⁻¹ * centralElement m 4 c *
      ((mainElement m 7 t)⁻¹)⁻¹ = _
    rw [((central_fifth_commute m c _ (mainElement_mem_unipotent m 7 t)).symm.inv_left).eq]
    simp [mul_assoc]
  have hh : f (tailElement m ![0, 0, c, 0, e]) =
      tailElement m ![0, 0, c + e * t, 0, e] := by
    rw [middle_product, mainElement_zero, one_mul, map_mul, h5, h3',
      middle_product, mainElement_zero, one_mul]
    rw [← (central_fifth_commute m (e * t) _
      (Y_le_unipotent m 2 (centralElement_mem_Y m 2 e))).eq,
      ← mul_assoc, ← centralElement_add m 4 (by decide)]
  simpa only [f, MulAut.conj_apply, inv_inv] using hh

/-- Both nonzero root curves exhaust the three-coordinate middle tail,
with actual conjugators in the fixed Ree model. -/
theorem root_classes_middle (m : ℕ) (b c e : CoefficientField m)
    (hne : tailElement m ![0, b, c, 0, e] ≠ 1) :
    IsLongRootInvolution (tailElement m ![0, b, c, 0, e]) ∨
      IsShortRootInvolution (tailElement m ![0, b, c, 0, e]) := by
  have conj_first (t b c e : CoefficientField m) :
      IsConj (tailElement m ![0, b, c, 0, e])
        (tailElement m ![0, b, c, 0, e + t * b]) := by
    apply isConj_iff.mpr
    exact ⟨(mainElement m 0 t)⁻¹, by
      simpa only [MulAut.conj_apply, inv_inv] using first_conj_middle m t b c e⟩
  have conj_weyl (b c e : CoefficientField m) :
      IsConj (tailElement m ![0, b, c, 0, e])
        (tailElement m ![0, b, e, 0, c]) :=
    isConj_iff.mpr ⟨weylLift m .linear, linearWeyl_middle m b c e⟩
  by_cases hb : b = 0
  · subst b
    left
    by_cases he : e = 0
    · subst e
      rw [tailElement_longRoot] at hne ⊢
      exact ⟨c, by simpa using hne, IsConj.refl _⟩
    · have ht : e * (c / e) = c := by field_simp
      have hconj : IsConj (tailElement m ![0, 0, c, 0, e])
          (tailElement m ![0, 0, 0, 0, e]) := by
        apply isConj_iff.mpr
        refine ⟨(mainElement m 7 (c / e))⁻¹, ?_⟩
        simpa only [MulAut.conj_apply, inv_inv, ht, CharTwo.add_self_eq_zero] using
          eighth_conj_middle_zero m (c / e) c e
      have htotal := hconj.trans (conj_weyl 0 0 e)
      rw [tailElement_longRoot] at htotal
      exact ⟨e, he, htotal.symm⟩
  · right
    have ht (a : CoefficientField m) : a + (a / b) * b = 0 := by
      rw [div_mul_cancel₀ _ hb, CharTwo.add_self_eq_zero]
    have h1 : IsConj (tailElement m ![0, b, c, 0, e])
        (tailElement m ![0, b, c, 0, 0]) := by
      simpa only [ht] using conj_first (e / b) b c e
    have h2 : IsConj (tailElement m ![0, b, 0, 0, c])
        (tailElement m ![0, b, 0, 0, 0]) := by
      simpa only [ht] using conj_first (c / b) b 0 c
    have htotal := (h1.trans (conj_weyl b c 0)).trans h2
    have hend : tailElement m ![0, b, 0, 0, 0] = shortRootElement m b := by
      simp [middle_product, main_fourth_eq]
    rw [hend] at htotal
    exact ⟨b, hb, htotal.symm⟩

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy
