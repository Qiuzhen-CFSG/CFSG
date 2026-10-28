module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.Basic
public import Theory.Representation.SL2NaturalOffenders.Semilinear
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The full orthogonal centralizer of the marked left SL₂

On the actual minus space, the centralizer of the published left SL₂ is
exactly the image of right SL₂ times the full isometry group of the literal
minus complement. The statement holds over every finite field of odd
characteristic, including F₃, and for every complement parameter `r`.

Commuting with the left negative identity kills both off-diagonal blocks.
The natural SL₂ commutant theorem, applied to each input and output column,
then makes the four-space action right matrix multiplication. Preservation
of the determinant form forces this matrix to have determinant one. The
remaining block is an invertible isometry of the original complement.

The final application combines this calculation with genuine centralizer
lifting from the scalar quotient. It discharges the full-centralizer
splitting premise of the residual assembly; complementary commutator
membership and generation remain separate calculations with their owners.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17,
printed p.39; GLS3 §2.7 for the full orthogonal, commutator Omega, and scalar
quotient conventions. The column argument follows the existing proof in
`Theory/Representation/OrthogonalFourPlusMatrix/Commutant.lean`.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Matrix Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
open FourPlusMatrix TheoremDRootNormalizer.HigherRanks
variable {F : Type*} [Field F]

private def columnInsert (j : Fin 2) (v : Fin 2 → F) : Mat (F := F) :=
  fun i k => if k = j then v i else 0

private lemma columnInsert_left (A : Mat (F := F)) (j : Fin 2) (v : Fin 2 → F) :
    A * columnInsert j v = columnInsert j (A.mulVec v) := by
  ext i k
  fin_cases k <;> fin_cases j <;>
    simp [columnInsert, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]


private theorem left_commutant (f : Mat (F := F) →+ Mat (F := F))
    (hleft : ∀ (A : SpecialLinearGroup (Fin 2) F) M,
      f (A.val * M) = A.val * f M) :
    ∃ C : Mat (F := F), ∀ M, f M = M * C := by
  have hblock (j k : Fin 2) : ∃ c : F, ∀ v : Fin 2 → F,
      (fun i => f (columnInsert k v) i j) = c • v := by
    let b : (Fin 2 → F) →+ (Fin 2 → F) :=
      { toFun := fun v i => f (columnInsert k v) i j
        map_zero' := by
          have he : columnInsert k (0 : Fin 2 → F) = 0 := by ext i l; simp [columnInsert]
          change (fun i => f (columnInsert k 0) i j) = 0
          rw [he, f.map_zero]
          rfl
        map_add' := by
          intro v w
          have he : columnInsert k (v + w) = columnInsert k v + columnInsert k w := by
            ext i l
            by_cases h : l = k <;> simp [columnInsert, h]
          change (fun i => f (columnInsert k (v + w)) i j) = _
          rw [he, f.map_add]
          rfl }
    apply Representation.SL2NaturalOffenders.centralizer_scalar b
    intro A v
    change (fun i => f (columnInsert k (A.val.mulVec v)) i j) = _
    rw [← columnInsert_left, hleft]
    rfl
  choose c hc using hblock
  have hformula (M : Mat (F := F)) (i j : Fin 2) :
      f M i j = c j 0 * M i 0 + c j 1 * M i 1 := by
    have he : M = columnInsert 0 (fun i => M i 0) + columnInsert 1 (fun i => M i 1) := by
      ext i j
      fin_cases j <;> simp [columnInsert]
    have h0 := congrFun (hc j 0 (fun i => M i 0)) i
    have h1 := congrFun (hc j 1 (fun i => M i 1)) i
    conv_lhs => rw [he, map_add]
    exact congrArg₂ (· + ·) h0 h1
  let C : Mat (F := F) := fun i j => c j i
  have hformula' (M : Mat (F := F)) : f M = M * C := by
    ext i j
    rw [hformula]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp only [C]
    ring
  exact ⟨C, hformula'⟩

private theorem eq_zero_of_neg_eq {V : Type*} [AddCommGroup V] [Module F V]
    (h2 : (2 : F) ≠ 0) {v : V} (h : -v = v) : v = 0 := by
  have hz : (2 : F) • v = 0 := by
    rw [two_smul]
    exact (congrArg (· + v) h.symm).trans (neg_add_cancel v)
  exact (smul_eq_zero.mp hz).resolve_left h2

private theorem determinant_sum_centralizer
    {W : Type*} [AddCommGroup W] [Module F W] [Finite W]
    (Q : QuadraticForm F W) (h2 : (2 : F) ≠ 0)
    (e : (Mat (F := F) × W) ≃ₗ[F] (Mat (F := F) × W))
    (hc : ∀ (A : SpecialLinearGroup (Fin 2) F) (M : Mat (F := F)) (w : W),
      e (A.val * M, w) = (A.val * (e (M, w)).1, (e (M, w)).2))
    (hq : ∀ M w, (e (M, w)).1.det + Q (e (M, w)).2 = M.det + Q w) :
    ∃ (B : SpecialLinearGroup (Fin 2) F) (u : W ≃ₗ[F] W),
      (∀ w, Q (u w) = Q w) ∧ ∀ M w, e (M, w) = (M * B.val, u w) := by
  have hn (M : Mat (F := F)) (w : W) :
      e (-M, w) = (-(e (M, w)).1, (e (M, w)).2) := by
    simpa only [negativeSL, neg_mul, one_mul] using hc negativeSL M w
  have h01 (w : W) : (e (0, w)).1 = 0 := by
    apply eq_zero_of_neg_eq h2
    simpa using (congrArg Prod.fst (hn 0 w)).symm
  have h10 (M : Mat (F := F)) : (e (M, 0)).2 = 0 := by
    apply eq_zero_of_neg_eq h2
    have h := congrArg Prod.snd (hn M 0)
    have he : (-M, (0 : W)) = -(M, (0 : W)) := by simp
    rw [he, map_neg] at h
    exact h
  let f : Mat (F := F) →+ Mat (F := F) :=
    (LinearMap.fst F _ _).toAddMonoidHom.comp
      (e.toLinearMap.toAddMonoidHom.comp (LinearMap.inl F _ _).toAddMonoidHom)
  obtain ⟨C, hC⟩ := left_commutant f (fun A M => congrArg Prod.fst (hc A M 0))
  have hdet : C.det = 1 := by
    have h := hq 1 0
    change (f 1).det + Q (e (1, 0)).2 = _ at h
    simpa only [hC, one_mul, h10, map_zero, add_zero, Matrix.det_one] using h
  let v : W →ₗ[F] W := (LinearMap.snd F _ _).comp
    (e.toLinearMap.comp (LinearMap.inr F _ _))
  have hv : Function.Injective v := by
    intro w z hwz
    have he : e (0, w) = e (0, z) := Prod.ext ((h01 w).trans (h01 z).symm) hwz
    exact congrArg Prod.snd (e.injective he)
  let u : W ≃ₗ[F] W := LinearEquiv.ofBijective v
    ⟨hv, Finite.surjective_of_injective hv⟩
  refine ⟨⟨C, hdet⟩, u, ?_, ?_⟩
  · intro w
    change Q (e (0, w)).2 = Q w
    have h := hq 0 w
    simpa only [h01, Matrix.det_zero, zero_add] using h
  · intro M w
    have he : (M, w) = (M, (0 : W)) + (0, w) := by simp
    rw [he, map_add]
    apply Prod.ext
    · change f M + (e (0, w)).1 = M * C
      rw [hC, h01, add_zero]
    · change (e (M, 0)).2 + v w = v w
      rw [h10, zero_add]

private def matrixSplitCoordinates (r : ℕ) : Minus.Space F (r + 2) ≃ₗ[F]
    Mat (F := F) × Minus.Space F r :=
  (splitCoordinates r).trans (coordinates.prodCongr (LinearEquiv.refl F _))

private theorem matrixSplitCoordinates_form [Finite F] (r : ℕ)
    (x : Minus.Space F (r + 2)) :
    Minus.quadraticForm F (r + 3) x = (matrixSplitCoordinates r x).1.det +
      Minus.quadraticForm F (r + 1) (matrixSplitCoordinates r x).2 := by
  change Minus.form F (r + 2) (Minus.parameter F) x =
    (coordinates (splitCoordinates r x).1).det +
      Minus.form F r (Minus.parameter F) (splitCoordinates r x).2
  rw [splitCoordinates_form, coordinates_det]

private theorem fullFundamentalHom_matrixCoordinates [Finite F] (r : ℕ)
    (A : SpecialLinearGroup (Fin 2) F) (x : Minus.Space F (r + 2)) :
    matrixSplitCoordinates r ((fullFundamentalHom r A).val x) =
      (A.val * (matrixSplitCoordinates r x).1, (matrixSplitCoordinates r x).2) := by
  change (coordinates (splitCoordinates r
      ((blockHom r (Minus.parameter F) ((fourLeft A).val, 1)).val x)).1,
    (splitCoordinates r
      ((blockHom r (Minus.parameter F) ((fourLeft A).val, 1)).val x)).2) = _
  rw [blockHom_coordinates]
  apply Prod.ext
  · change coordinates ((toOrthogonal (A, 1)).val (splitCoordinates r x).1) = _
    rw [toOrthogonal_coordinates]
    simp only [inv_one]
    change A.val * coordinates (splitCoordinates r x).1 * (1 : Mat (F := F)) = _
    rw [mul_one]
    rfl
  · rfl

private theorem fullBlockHom_matrixCoordinates [Finite F] (r : ℕ)
    (A : SpecialLinearGroup (Fin 2) F)
    (u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1)))
    (x : Minus.Space F (r + 2)) :
    matrixSplitCoordinates r ((fullBlockHom r (A, u)).val x) =
      ((matrixSplitCoordinates r x).1 * A⁻¹.val, u.val (matrixSplitCoordinates r x).2) := by
  change (coordinates (splitCoordinates r
      ((blockHom r (Minus.parameter F) ((fourRight A).val, u)).val x)).1,
    (splitCoordinates r
      ((blockHom r (Minus.parameter F) ((fourRight A).val, u)).val x)).2) = _
  rw [blockHom_coordinates]
  apply Prod.ext
  · change coordinates ((toOrthogonal (1, A)).val (splitCoordinates r x).1) = _
    rw [toOrthogonal_coordinates]
    change (1 : Mat (F := F)) * coordinates (splitCoordinates r x).1 * A⁻¹.val = _
    rw [one_mul]
    rfl
  · rfl

/-- The full complementary isometries and right SL₂ centralize the marked left SL₂. -/
theorem fullBlockHom_commute [Finite F] (r : ℕ)
    (A : SpecialLinearGroup (Fin 2) F)
    (g : SpecialLinearGroup (Fin 2) F ×
      Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    Commute (fullFundamentalHom r A) (fullBlockHom r g) := by
  change Commute (blockHom r (Minus.parameter F) ((fourLeft A).val, 1))
    (blockHom r (Minus.parameter F) ((fourRight g.1).val, g.2))
  apply Commute.map
  exact Prod.ext (congrArg Subtype.val (fourFactors_commute A g.1).eq) (by simp)

/-- Every full isometry centralizing the marked left SL₂ is a right SL₂ block
and an arbitrary isometry of the literal minus complement. -/
theorem exists_fullBlock_of_centralizes [Finite F] (r : ℕ) (h2 : (2 : F) ≠ 0)
    (y : Minus.Orthogonal F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3)))
    (hy : ∀ A, Commute (fullFundamentalHom r A) y) :
    ∃ (A : SpecialLinearGroup (Fin 2) F)
      (u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1))),
      fullBlockHom r (A, u) = y := by
  let s := matrixSplitCoordinates (F := F) r
  let e := s.symm.trans (y.val.trans s)
  have hc (A : SpecialLinearGroup (Fin 2) F) (M : Mat (F := F)) (w : Minus.Space F r) :
      e (A.val * M, w) = (A.val * (e (M, w)).1, (e (M, w)).2) := by
    have h := congrArg (fun g : Minus.Orthogonal F (Minus.Space F (r + 2))
      (Minus.quadraticForm F (r + 3)) => s (g.val (s.symm (M, w)))) (hy A).eq
    change s ((fullFundamentalHom r A).val (y.val (s.symm (M, w)))) =
      s (y.val ((fullFundamentalHom r A).val (s.symm (M, w)))) at h
    have ha : (fullFundamentalHom r A).val (s.symm (M, w)) = s.symm (A.val * M, w) := by
      apply s.injective
      rw [LinearEquiv.apply_symm_apply]
      change matrixSplitCoordinates r ((fullFundamentalHom r A).val (s.symm (M, w))) = _
      rw [fullFundamentalHom_matrixCoordinates]
      change (A.val * (s (s.symm (M, w))).1, (s (s.symm (M, w))).2) = _
      rw [LinearEquiv.apply_symm_apply]
    rw [ha] at h
    change matrixSplitCoordinates r ((fullFundamentalHom r A).val _) = _ at h
    rw [fullFundamentalHom_matrixCoordinates] at h
    exact h.symm
  have hq (M : Mat (F := F)) (w : Minus.Space F r) :
      (e (M, w)).1.det + Minus.quadraticForm F (r + 1) (e (M, w)).2 =
        M.det + Minus.quadraticForm F (r + 1) w := by
    have h := (matrixSplitCoordinates_form r (y.val (s.symm (M, w)))).symm.trans
      (((mem_quadraticIsometrySubgroup _ _).mp y.property (s.symm (M, w))).trans
        (matrixSplitCoordinates_form r (s.symm (M, w))))
    change (e (M, w)).1.det + Minus.quadraticForm F (r + 1) (e (M, w)).2 =
      (s (s.symm (M, w))).1.det + Minus.quadraticForm F (r + 1) (s (s.symm (M, w))).2 at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  obtain ⟨B, u, hu, he⟩ := determinant_sum_centralizer
    (Minus.quadraticForm F (r + 1)) h2 e hc hq
  refine ⟨B⁻¹, ⟨u, (mem_quadraticIsometrySubgroup _ _).mpr hu⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply s.injective
  change matrixSplitCoordinates r ((fullBlockHom r _).val x) = _
  rw [fullBlockHom_matrixCoordinates, inv_inv]
  have h := (he (s x).1 (s x).2).symm
  change ((s x).1 * B.val, u (s x).2) = s (y.val (s.symm (s x))) at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

/-- The exact full orthogonal centralizer, including the field with three elements. -/
theorem fullBlockHom_range_eq_centralizer [Finite F] (r : ℕ) (h2 : (2 : F) ≠ 0) :
    (fullBlockHom (F := F) r).range =
      Subgroup.centralizer ((fullFundamentalHom (F := F) r).range : Set _) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    exact fullBlockHom_commute r A g
  · intro y hy
    obtain ⟨A, u, h⟩ := exists_fullBlock_of_centralizes r h2 y
      (fun A => Subgroup.mem_centralizer_iff.mp hy _ ⟨A, rfl⟩)
    exact ⟨(A, u), h⟩

/-- A lift from the literal scalar quotient centralizer has full orthogonal
block form. Complementary Omega membership is a separate assertion. -/
theorem projective_centralizer_exists_fullBlock [Finite F]
    (p : ℕ) [CharP F p] (ho : Odd p) (r : ℕ) (hq : 2 < Nat.card F)
    (y : Minus.Omega F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3)))
    (hy : QuotientGroup.mk' (Minus.scalarSubgroup F _ _) y ∈ fundamentalCentralizer r hq) :
    ∃ (A : SpecialLinearGroup (Fin 2) F)
      (u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1))),
      fullBlockHom r (A, u) = y.val := by
  have h2 : (2 : F) ≠ 0 := by
    apply Ring.two_ne_zero
    rw [ringChar.eq F p]
    obtain ⟨k, hk⟩ := ho
    omega
  apply exists_fullBlock_of_centralizes r h2 y.val
  intro A
  exact (projective_centralizer_lifts p ho r hq y hy A).map (commutator _).subtype

end ClassicalOrthogonal.Fundamental.MinusCentralizer
