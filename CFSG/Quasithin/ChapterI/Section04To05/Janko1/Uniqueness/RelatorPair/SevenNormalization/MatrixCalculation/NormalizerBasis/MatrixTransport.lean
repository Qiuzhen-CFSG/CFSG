module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.NormalizerBasis.SylowWeights

/-!
# Converting the normalizer eigenbasis to matrix conjugation

The linear equivalence carrying the supplied basis to standard coordinates is
an invertible matrix c. Its conjugation sends the literal x, u, y actions on
basis vectors to `normalX`, `normalU`, `sourceY`, with column-vector conventions.
The inverse is taken in the matrix group before coercing to a matrix.

This is the change-of-coordinates step in Gorenstein, *Finite Groups*, §16.6,
pp.482–483, equations (6.1)–(6.2). The basis is an explicit premise here and is
constructed from the marked Sylow character spaces in `Eigenbasis`.
-/

open Module Matrix
namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation

local notation "Vec" => Fin 7 → ZMod 11
local notation "Mat" => Matrix (Fin 7) (Fin 7) (ZMod 11)

private theorem normalU_entry (i j : Fin 7) :
    (if 2 * j + 3 = i then (1 : ZMod 11) else 0) = normalU i j := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem sourceY_entry (i j : Fin 7) :
    (if j - 1 = i then (1 : ZMod 11) else 0) = sourceY i j := by
  fin_cases i <;> fin_cases j <;> rfl

private noncomputable def basisChange (b : Basis (Fin 7) (ZMod 11) Vec) : Janko1.Ambient :=
  Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun)

private theorem basisChange_mulVec (b : Basis (Fin 7) (ZMod 11) Vec) (v : Vec) :
    (basisChange b : Mat) *ᵥ v = b.equivFun v := by
  have he : ((basisChange b : Mat).mulVecLin) = b.equivFun.toLinearMap := by
    rw [← Matrix.GeneralLinearGroup.coe_toLin]
    exact congrArg Units.val (Matrix.GeneralLinearGroup.toLin.apply_symm_apply
      (LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun))
  exact LinearMap.congr_fun he v

private theorem basisChange_inv_mulVec (b : Basis (Fin 7) (ZMod 11) Vec) (v : Vec) :
    (((basisChange b)⁻¹ : Janko1.Ambient) : Mat) *ᵥ v = b.equivFun.symm v := by
  apply b.equivFun.injective
  calc
    b.equivFun ((((basisChange b)⁻¹ : Janko1.Ambient) : Mat) *ᵥ v) =
        (basisChange b : Mat) *ᵥ ((((basisChange b)⁻¹ : Janko1.Ambient) : Mat) *ᵥ v) :=
      (basisChange_mulVec b _).symm
    _ = ((basisChange b : Mat) * (((basisChange b)⁻¹ : Janko1.Ambient) : Mat)) *ᵥ v :=
      Matrix.mulVec_mulVec v _ _
    _ = v := by rw [Units.mul_inv, Matrix.one_mulVec]
    _ = b.equivFun (b.equivFun.symm v) := (b.equivFun.apply_symm_apply v).symm

private theorem ambient_mulVec_mul (A B : Janko1.Ambient) (v : Vec) :
    ((A * B : Janko1.Ambient) : Mat) *ᵥ v = (A : Mat) *ᵥ ((B : Mat) *ᵥ v) :=
  (Matrix.mulVec_mulVec v (A : Mat) (B : Mat)).symm

private theorem basisChange_entry (b : Basis (Fin 7) (ZMod 11) Vec)
    (A : Janko1.Ambient) (i j : Fin 7) :
    (basisChange b * A * (basisChange b)⁻¹ : Mat) i j =
      b.equivFun ((A : Mat) *ᵥ b j) i := by
  have hj : Pi.single j (1 : ZMod 11) = b.equivFun (b j) := by
    funext k
    simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
  calc
    (basisChange b * A * (basisChange b)⁻¹ : Mat) i j =
        (((basisChange b * A * (basisChange b)⁻¹ : Janko1.Ambient) : Mat) *ᵥ
          Pi.single j 1) i :=
      (congr_fun (Matrix.mulVec_single_one
        (basisChange b * A * (basisChange b)⁻¹ : Mat) j) i).symm
    _ = ((basisChange b : Mat) *ᵥ ((A : Mat) *ᵥ
        ((((basisChange b)⁻¹ : Janko1.Ambient) : Mat) *ᵥ Pi.single j 1))) i := by
      rw [ambient_mulVec_mul, ambient_mulVec_mul]
    _ = b.equivFun ((A : Mat) *ᵥ b j) i := by
      rw [basisChange_mulVec b, basisChange_inv_mulVec b, hj, LinearEquiv.symm_apply_apply]

variable {G : Type*} [Group G]

public theorem exists_normalizer_images_of_basis (ρ : G →* Janko1.Ambient)
    (x u y : G) (b : Basis (Fin 7) (ZMod 11) Vec)
    (hx : ∀ i, vectorRepresentation ρ x (b i) = normalX i i • b i)
    (hu : ∀ i, vectorRepresentation ρ u (b i) = b (2 * i + 3))
    (hy : ∀ i, vectorRepresentation ρ y (b i) = b (i - 1)) :
    ∃ c : Janko1.Ambient,
      (c * ρ x * c⁻¹ : Mat) = normalX ∧
      (c * ρ u * c⁻¹ : Mat) = normalU ∧
      (c * ρ y * c⁻¹ : Mat) = sourceY := by
  refine ⟨basisChange b, ?_, ?_, ?_⟩
  · apply Matrix.ext
    intro i j
    rw [basisChange_entry]
    rw [← vectorRepresentation_apply ρ x]
    rw [hx, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, Basis.equivFun_self]
    by_cases he : i = j
    · subst j
      simp
    · simp [he, Ne.symm he, normalX, Matrix.diagonal_apply_ne]
  · apply Matrix.ext
    intro i j
    rw [basisChange_entry]
    rw [← vectorRepresentation_apply ρ u]
    rw [hu, Basis.equivFun_self]
    exact normalU_entry i j
  · apply Matrix.ext
    intro i j
    rw [basisChange_entry]
    rw [← vectorRepresentation_apply ρ y]
    rw [hy, Basis.equivFun_self]
    exact sourceY_entry i j

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation
