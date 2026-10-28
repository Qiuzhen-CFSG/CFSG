module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.InnerModel.Embedding.Matrices
public import Theory.Alternating.Theorem523A6

/-!
# Projective Suzuki relations

Scalar defects vanish in the literal projective matrix image. The proved
Suzuki presentation therefore gives a homomorphism from A₇; its root generator
is not scalar, so simplicity of A₇ makes this homomorphism injective.
-/

@[expose] public noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding
open Matrix GLS3.Chapter5.SchurPresentation
open scoped commutatorElement

private theorem projective_eq_one_of_scalar (x : matrixForm.specialSubgroup)
    (a : F25) (hx : x.val.val = Matrix.scalar (Fin 3) a) :
    matrixForm.specialToProjective x = 1 := by
  apply Subtype.ext
  have hc : Matrix.ProjGenLinGroup.mk x.val = 1 :=
    Matrix.ProjGenLinGroup.mk_eq_one.mpr
      (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨a, hx.symm⟩)
  simpa only [matrixForm.specialToProjective_apply_val, Subgroup.coe_one] using hc

theorem projective_root_cube : projectiveGenerator 0 ^ 3 = 1 := by
  rw [projectiveGenerator, ← map_pow]
  apply projective_eq_one_of_scalar _ 1
  change generatorMatrix 0 ^ 3 = Matrix.scalar (Fin 3) 1
  simpa using generator_root_cube

theorem projective_tail_square (i : Fin 5) (hi : i ≠ 0) :
    projectiveGenerator i ^ 2 = 1 := by
  rw [projectiveGenerator, ← map_pow]
  exact projective_eq_one_of_scalar _ _ (generator_tail_square i hi)

theorem projective_adjacent_cube (i : Fin 4) :
    (projectiveGenerator i.castSucc * projectiveGenerator i.succ) ^ 3 = 1 := by
  simp only [projectiveGenerator, ← map_mul, ← map_pow]
  apply projective_eq_one_of_scalar _ 1
  change (generatorMatrix i.castSucc * generatorMatrix i.succ) ^ 3 = Matrix.scalar (Fin 3) 1
  simpa using generator_adjacent_cube i

theorem projective_root_far_square (j : Fin 5) (hj : 1 < j.val) :
    (projectiveGenerator 0 * projectiveGenerator j) ^ 2 = 1 := by
  simp only [projectiveGenerator, ← map_mul, ← map_pow]
  exact projective_eq_one_of_scalar _ _ (generator_root_far_square j hj)

theorem projective_tail_far_commute (i j : Fin 5) (hi : i ≠ 0) (hj : j ≠ 0)
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Commute (projectiveGenerator i) (projectiveGenerator j) := by
  have h : Commute (specialGenerator i) (specialGenerator j) := by
    apply Subtype.ext
    apply Units.ext
    exact generator_tail_far_commute i j hi hj hfar
  exact h.map matrixForm.specialToProjective

theorem projective_relator (r : SuzukiRelator 2) :
    FreeGroup.lift projectiveGenerator r.word = 1 := by
  cases r with
  | rootCube =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using projective_root_cube
  | tailSquare i hi =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using projective_tail_square i hi
  | rootAdjacentCube =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using projective_adjacent_cube 0
  | tailAdjacentCube i _ =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using projective_adjacent_cube i
  | rootFarSquare j hj =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using projective_root_far_square j hj
  | tailFarCommutator i j hi hj hfar =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using
        (projective_tail_far_commute i j hi hj hfar).commutator_eq

theorem projective_root_ne_one : projectiveGenerator 0 ≠ 1 := by
  intro h
  have hc : linearGenerator 0 ∈ Subgroup.center (GL (Fin 3) F25) :=
    Matrix.ProjGenLinGroup.mk_eq_one.mp (by
      simpa only [projectiveGenerator, specialGenerator, matrixForm.specialToProjective_apply_val, Subgroup.coe_one] using
        congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
  have he := congrFun (congrFun ha 0) 1
  change (0 : F25) = ⟨2, 2⟩ at he
  exact (by decide : (0 : F25) ≠ ⟨2, 2⟩) he

/-- The explicit matrix presentation embeds A₇ in the projective unitary image. -/
theorem exists_embedding_matrixForm :
    ∃ f : alternatingGroup (Fin 7) →* ProjectiveSpecialUnitaryMatrixGroup matrixForm,
      Function.Injective f := by
  let h : SuzukiPresentedGroup 2 →* ProjectiveSpecialUnitaryMatrixGroup matrixForm :=
    PresentedGroup.toGroup (by rintro _ ⟨r, rfl⟩; exact projective_relator r)
  let e : SuzukiPresentedGroup 2 ≃* alternatingGroup (Fin 7) :=
    MulEquiv.ofBijective (suzukiPresentedProjection 2)
      ⟨suzukiPresentedProjection_injective 2, suzukiPresentedProjection_surjective 2⟩
  let f := h.comp e.symm.toMonoidHom
  have hfx : f (e (PresentedGroup.of (0 : Fin 5))) = projectiveGenerator 0 := by
    simp [f, h]
  refine ⟨f, ?_⟩
  let _ : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact f.ker_eq_bot_iff.mp hbot
  · exfalso
    apply projective_root_ne_one
    rw [← hfx]
    exact MonoidHom.mem_ker.mp (by rw [htop]; trivial)

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding
