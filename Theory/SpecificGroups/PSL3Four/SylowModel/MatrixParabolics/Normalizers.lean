module

public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixParabolics.Basic

/-!
# Root-plane normalizers are the geometric parabolics

In the matrix field extension of PSL₃(4), the first root plane has the unique
common fixed projective point `standardPoint`. Dually, the second root plane
has the unique common fixed covector `standardPlane`. Their normalizers must
therefore lie in the respective geometric stabilizers.

For the reverse inclusions, point stabilization forces the two lower entries
of the first matrix column to vanish; plane stabilization forces the first
two entries of the last row to vanish. Expanding the conjugate of a matrix
`1 + N` then proves that each stabilizer preserves its root plane. The field
complement already normalizes both root planes inside the coordinate Sylow
subgroup, completing the identifications in the actual semidirect product.
No quotient identification is assumed.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.2
and §5.3.7, printed pp. 659--661 (PDF pp. 676--678).
-/

public section
noncomputable section
namespace Matrix.PSL3Four.SylowModel.MatrixRealization
open Matrix Projectivization

private lemma fixed_coordinate {v : Fin 3 → F} {i j : Fin 3} {r : Fˣ}
    (hi : (r : F) * v i = v i + v j) (hj : (r : F) * v j = v j) : v j = 0 := by
  by_contra hn
  have hr : (r : F) = 1 := (mul_right_cancel₀ hn) (hj.trans (one_mul _).symm)
  exact hn (by simpa [hr] using hi)

/-- The first root plane has only the standard point as a common fixed point. -/
theorem rootPlane₁_unique_fixed (p : PG)
    (hp : ∀ g ∈ rootPlane₁, pointAction g p = p) : p = standardPoint := by
  induction p using Projectivization.ind with | h v hv =>
  have hfix (x c : F) : specialLinear ⟨x, 0, c⟩ • mk F v hv = mk F v hv :=
    hp _ ((mem_rootPlane₁ _).mpr ⟨x, c, rfl⟩)
  obtain ⟨r, hr⟩ := (mk_eq_mk_iff F _ _ _ _).mp (by
    simpa only [smul_mk] using hfix 1 0)
  obtain ⟨s, hs⟩ := (mk_eq_mk_iff F _ _ _ _).mp (by
    simpa only [smul_mk] using hfix 0 1)
  have hr' : ∀ i, (r : F) * v i = (matrix ⟨1, 0, 0⟩ *ᵥ v) i := fun i => congrFun hr i
  have hs' : ∀ i, (s : F) * v i = (matrix ⟨0, 0, 1⟩ *ᵥ v) i := fun i => congrFun hs i
  simp [matrix, mulVec, dotProduct, Fin.sum_univ_three] at hr' hs'
  have h1 : v 1 = 0 := fixed_coordinate (by simpa using hr' 0) (by simpa using hr' 1)
  have h2 : v 2 = 0 := fixed_coordinate (by simpa using hs' 0) (by simpa using hs' 2)
  have h0 : v 0 ≠ 0 := by
    intro h
    apply hv
    ext i
    fin_cases i <;> simp [h, h1, h2]
  apply (mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨Units.mk0 (v 0) h0, ?_⟩
  ext i
  fin_cases i <;> simp [h1, h2]

/-- In the covector action, the second root plane fixes only the standard plane. -/
theorem rootPlane₂_unique_fixed (p : PG)
    (hp : ∀ g ∈ rootPlane₂, lineAction g p = p) : p = standardPlane := by
  induction p using Projectivization.ind with | h v hv =>
  have hfix (y c : F) : SpecialLinearGroup.inverseTranspose (specialLinear ⟨0, y, c⟩) •
      mk F v hv = mk F v hv := hp _ ((mem_rootPlane₂ _).mpr ⟨y, c, rfl⟩)
  have he (y c : F) : ∃ r : Fˣ, ∀ i, (r : F) * v i =
      ((matrix (⟨0, y, c⟩ : U)⁻¹).transpose *ᵥ v) i := by
    obtain ⟨r, hr⟩ := (mk_eq_mk_iff F _ _ _ _).mp (by
      simpa only [smul_mk] using hfix y c)
    refine ⟨r, ?_⟩
    change r • v = ((specialLinear (⟨0, y, c⟩ : U))⁻¹.val.transpose) *ᵥ v at hr
    rw [← map_inv] at hr
    exact fun i => congrFun hr i
  have hinv (y c : F) : matrix (⟨0, y, c⟩ : U)⁻¹ =
      !![1, 0, -c; 0, 1, -y; 0, 0, 1] := by
    change !![1, -0, 0 * y - c; 0, 1, -y; 0, 0, 1] = _
    simp
  obtain ⟨r, hr⟩ := he 0 (-1)
  obtain ⟨s, hs⟩ := he (-1) 0
  simp [hinv, mulVec, dotProduct, Fin.sum_univ_three] at hr hs
  have h0 : v 0 = 0 := fixed_coordinate (i := 2) (r := r)
    (by simpa [add_comm] using hr 2) (by simpa using hr 0)
  have h1 : v 1 = 0 := fixed_coordinate (i := 2) (r := s)
    (by simpa [add_comm] using hs 2) (by simpa using hs 1)
  have h2 : v 2 ≠ 0 := by
    intro h
    apply hv
    ext i
    fin_cases i <;> simp [h, h0, h1]
  apply (mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨Units.mk0 (v 2) h2, ?_⟩
  ext i
  fin_cases i <;> simp [h0, h1]

private lemma normalizer_fixes_unique {G X : Type*} [Group G]
    (f : G →* Equiv.Perm X) (H : Subgroup G) (p : X)
    (hfix : ∀ a ∈ H, f a p = p)
    (hunique : ∀ q, (∀ a ∈ H, f a q = q) → q = p)
    (g : G) (hg : g ∈ Subgroup.normalizer (H : Set G)) : f g p = p := by
  apply hunique
  intro a ha
  have h := hfix _ ((Subgroup.mem_normalizer_iff''.mp hg a).mp ha)
  have he := congrArg (f g) h
  simpa [map_mul, map_inv, Equiv.Perm.mul_apply] using he

theorem local₁_le_parabolic₁ : local₁ ≤ parabolic₁ := by
  intro g hg
  apply normalizer_fixes_unique pointAction rootPlane₁ standardPoint _
    rootPlane₁_unique_fixed g hg
  intro a ha
  obtain ⟨x, c, rfl⟩ := (mem_rootPlane₁ _).mp ha
  exact (mem_parabolic₁_iff_left _).mpr (projective_mem_parabolic₁ _)

theorem local₂_le_parabolic₂ : local₂ ≤ parabolic₂ := by
  intro g hg
  apply normalizer_fixes_unique lineAction rootPlane₂ standardPlane _
    rootPlane₂_unique_fixed g hg
  intro a ha
  obtain ⟨y, c, rfl⟩ := (mem_rootPlane₂ _).mp ha
  exact (mem_parabolic₂_iff_left _).mpr (projective_mem_parabolic₂ _)


private theorem point_column (A : SL) (hA : (A : PSL) ∈ projectiveParabolic₁) :
    A 1 0 = 0 ∧ A 2 0 = 0 := by
  change A • standardPoint = standardPoint at hA
  rw [standardPoint, smul_mk, mk_eq_mk_iff] at hA
  obtain ⟨r, hr⟩ := hA
  have h1 := congrFun hr 1
  have h2 := congrFun hr 2
  change (r : F) * (![1,0,0] : Fin 3 → F) 1 = (A.val *ᵥ ![1,0,0]) 1 at h1
  change (r : F) * (![1,0,0] : Fin 3 → F) 2 = (A.val *ᵥ ![1,0,0]) 2 at h2
  simp [mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

private theorem plane_row (A : SL) (hA : (A : PSL) ∈ projectiveParabolic₂) :
    A 2 0 = 0 ∧ A 2 1 = 0 := by
  have hi : ((A⁻¹ : SL) : PSL) ∈ projectiveParabolic₂ :=
    projectiveParabolic₂.inv_mem hA
  change SpecialLinearGroup.inverseTranspose A⁻¹ • standardPlane = standardPlane at hi
  rw [standardPlane, smul_mk, mk_eq_mk_iff] at hi
  obtain ⟨r, hr⟩ := hi
  change r • (![0,0,1] : Fin 3 → F) = (A⁻¹⁻¹.val.transpose *ᵥ ![0,0,1]) at hr
  rw [inv_inv] at hr
  have h0 := congrFun hr 0
  have h1 := congrFun hr 1
  change (r : F) * (![0,0,1] : Fin 3 → F) 0 = (A.val.transpose *ᵥ ![0,0,1]) 0 at h0
  change (r : F) * (![0,0,1] : Fin 3 → F) 1 = (A.val.transpose *ᵥ ![0,0,1]) 1 at h1
  simp [mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
  exact ⟨h0.symm, h1.symm⟩

private theorem conjugate_first_row (A : SL) (hA : (A : PSL) ∈ projectiveParabolic₁)
    (x c : F) :
    A * specialLinear ⟨x, 0, c⟩ * A⁻¹ =
      specialLinear ⟨A 0 0 * (x * A⁻¹ 1 1 + c * A⁻¹ 2 1), 0,
        A 0 0 * (x * A⁻¹ 1 2 + c * A⁻¹ 2 2)⟩ := by
  obtain ⟨ha1, ha2⟩ := point_column A hA
  obtain ⟨hb1, hb2⟩ := point_column A⁻¹ (projectiveParabolic₁.inv_mem hA)
  have hab : A.val * A⁻¹.val = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  have hm : matrix ⟨x, 0, c⟩ = 1 + !![0,x,c;0,0,0;0,0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrix]
  apply Subtype.ext
  change A.val * matrix ⟨x, 0, c⟩ * A⁻¹.val = matrix _
  rw [hm, mul_add, mul_one, add_mul, hab]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-SpecialLinearGroup.coe_inv, matrix, Matrix.mul_apply, Fin.sum_univ_three,
      ha1, ha2, hb1, hb2] <;> ring

private theorem conjugate_last_column (A : SL) (hA : (A : PSL) ∈ projectiveParabolic₂)
    (y c : F) :
    A * specialLinear ⟨0, y, c⟩ * A⁻¹ =
      specialLinear ⟨0, (A 1 0 * c + A 1 1 * y) * A⁻¹ 2 2,
        (A 0 0 * c + A 0 1 * y) * A⁻¹ 2 2⟩ := by
  obtain ⟨ha0, ha1⟩ := plane_row A hA
  obtain ⟨hb0, hb1⟩ := plane_row A⁻¹ (projectiveParabolic₂.inv_mem hA)
  have hab : A.val * A⁻¹.val = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  have hm : matrix ⟨0, y, c⟩ = 1 + !![0,0,c;0,0,y;0,0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrix]
  apply Subtype.ext
  change A.val * matrix ⟨0, y, c⟩ * A⁻¹.val = matrix _
  rw [hm, mul_add, mul_one, add_mul, hab]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-SpecialLinearGroup.coe_inv, matrix, Matrix.mul_apply, Fin.sum_univ_three,
      ha0, ha1, hb0, hb1]

private theorem linear_mem_local₁ (p : PSL) (hp : p ∈ projectiveParabolic₁) :
    linearInclusion p ∈ local₁ := by
  induction p using QuotientGroup.induction_on with | H A =>
  apply Subgroup.mem_normalizer_fintype
  intro a ha
  obtain ⟨x, c, rfl⟩ := (mem_rootPlane₁ _).mp ha
  have he := congrArg
    (fun B : SL => linearInclusion ((QuotientGroup.mk' (Subgroup.center SL)) B))
    (conjugate_first_row A hp x c)
  simp only [map_mul, map_inv] at he
  change linearInclusion (A : PSL) * linearInclusion (projective ⟨x, 0, c⟩) *
    (linearInclusion (A : PSL))⁻¹ = _ at he
  rw [he]
  exact (mem_rootPlane₁ _).mpr ⟨_, _, rfl⟩

private theorem linear_mem_local₂ (p : PSL) (hp : p ∈ projectiveParabolic₂) :
    linearInclusion p ∈ local₂ := by
  induction p using QuotientGroup.induction_on with | H A =>
  apply Subgroup.mem_normalizer_fintype
  intro a ha
  obtain ⟨y, c, rfl⟩ := (mem_rootPlane₂ _).mp ha
  have he := congrArg
    (fun B : SL => linearInclusion ((QuotientGroup.mk' (Subgroup.center SL)) B))
    (conjugate_last_column A hp y c)
  simp only [map_mul, map_inv] at he
  change linearInclusion (A : PSL) * linearInclusion (projective ⟨0, y, c⟩) *
    (linearInclusion (A : PSL))⁻¹ = _ at he
  rw [he]
  exact (mem_rootPlane₂ _).mpr ⟨_, _, rfl⟩

private theorem field_mem_sylow (t : C2) :
    fieldInclusion t ∈ (sylow : Subgroup FieldExtension) := by
  refine ⟨SemidirectProduct.inr t, ?_⟩
  apply SemidirectProduct.ext
  · change projective 1 = 1
    exact map_one _
  · rfl

theorem parabolic₁_le_local₁ : parabolic₁ ≤ local₁ := by
  intro g hg
  rw [← linear_mul_field g]
  exact local₁.mul_mem (linear_mem_local₁ _ ((mem_parabolic₁_iff_left _).mp hg))
    (sylow_le_local₁ (field_mem_sylow _))

theorem parabolic₂_le_local₂ : parabolic₂ ≤ local₂ := by
  intro g hg
  rw [← linear_mul_field g]
  exact local₂.mul_mem (linear_mem_local₂ _ ((mem_parabolic₂_iff_left _).mp hg))
    (sylow_le_local₂ (field_mem_sylow _))

/-- The first root-plane normalizer is exactly the point parabolic. -/
theorem local₁_eq_parabolic₁ : local₁ = parabolic₁ :=
  le_antisymm local₁_le_parabolic₁ parabolic₁_le_local₁

/-- The second root-plane normalizer is exactly the plane parabolic. -/
theorem local₂_eq_parabolic₂ : local₂ = parabolic₂ :=
  le_antisymm local₂_le_parabolic₂ parabolic₂_le_local₂

end Matrix.PSL3Four.SylowModel.MatrixRealization
