module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers.Geometry
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers.Line.Scalars

/-!
# The projective coordinate-line stabilizer in PSU₄(3)

The full SU₄ stabilizer is the determinant-corrected block copy of GU₃ constructed
in `Line.Blocks`. A block becomes scalar in dimension four exactly when its
three-dimensional determinant correction is the identity. Both maps therefore
have the same kernel: the four norm-one scalar matrices. The first isomorphism
theorem identifies the projective line stabilizer with SU₃, whose own projection
onto the shared `Carrier 3` is injective.

All maps use the actual identity-Hermitian groups over `FiniteField.Nine`, with
cube conjugation. No order recognition or subgroup classification is used.
Source: GLS3, chapter 2, §2.7 (`refs/KGroup/GLS3/chapter2.tex`), unitary and
projective conventions. This proves the fixed nondegenerate-line calculation
needed for Aschbacher–Smith, Theorem 0.1.2(4), condition K, printed pp.4,482 of
`refs/quasithin.pdf`; transport of arbitrary subspaces belongs to the parent.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers.Line

/-- The determinant-corrected block followed by the actual SU₄ projection. -/
def projectiveBlock : FullUnitaryThree →* Carrier 4 :=
  (project 4).comp blockEmbedding

/-- The image is precisely the projective coordinate-line stabilizer. -/
theorem projectiveBlock_range :
    projectiveBlock.range = projectiveStabilizer (coordinateSubspace 1) := by
  rw [projectiveBlock, MonoidHom.range_comp, blockEmbedding_range]
  rfl

private theorem scalar_block (u : FiniteField.Nineˣ) :
    (GeneralLinearGroup.scalar (Fin 4) u).val =
      block u.val (GeneralLinearGroup.scalar (Fin 3) u).val := by
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply, eq_comm]

/-- The four-dimensional projective projection kills exactly the matrices killed
by the three-dimensional determinant correction. -/
theorem projectiveBlock_kernel : projectiveBlock.ker = correction.ker := by
  ext B
  rw [correction_kernel_iff]
  constructor
  · intro h
    have hp := congrArg Subtype.val (MonoidHom.mem_ker.mp h)
    change ProjGenLinGroup.mk (blockEmbedding B).val = 1 at hp
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
    obtain ⟨u, hu⟩ := hp
    have hm := congrArg Units.val hu
    rw [blockEmbedding_val] at hm
    have hzero : u.val = B.val.val.det⁻¹ :=
      congrArg (fun M : Matrix (Fin 4) (Fin 4) FiniteField.Nine => M 0 0) hm
    apply Units.ext
    apply Matrix.ext
    intro i j
    have he := congrArg
      (fun M : Matrix (Fin 4) (Fin 4) FiniteField.Nine => M i.succ j.succ) hm
    simpa only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      block_succ_succ, Fin.succ_inj, GeneralLinearGroup.val_det_apply,
      Units.val_inv_eq_inv_val, hzero] using he.symm
  · intro hB
    apply Subtype.ext
    change ProjGenLinGroup.mk (blockEmbedding B).val = 1
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨(GeneralLinearGroup.det B.val)⁻¹, ?_⟩
    apply Units.ext
    rw [blockEmbedding_val]
    have hv := congrArg Units.val hB
    rw [scalar_block, ← hv, Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply]


/-- The projective block map has scalar kernel of order four. -/
theorem projectiveBlock_kernel_card : Nat.card projectiveBlock.ker = 4 := by
  rw [projectiveBlock_kernel]
  exact scalarKernel_card

/-- Its kernel consists exactly of the norm-one scalar matrices in GU₃. -/
theorem projectiveBlock_kernel_eq_scalars : projectiveBlock.ker = scalarUnitary.range :=
  projectiveBlock_kernel.trans scalarUnitary_range.symm

/-- The line stabilizer is the quotient of GU₃ by its actual projective kernel. -/
def lineQuotientEquiv : FullUnitaryThree ⧸ projectiveBlock.ker ≃*
    projectiveStabilizer (coordinateSubspace 1) :=
  (QuotientGroup.quotientKerEquivRange projectiveBlock).trans
    (MulEquiv.subgroupCongr projectiveBlock_range)

/-- The projective stabilizer of the first coordinate line is the concrete PSU₃(3). -/
def coordinateLineStabilizerEquiv :
    projectiveStabilizer (coordinateSubspace 1) ≃* Carrier 3 :=
  lineQuotientEquiv.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq projectiveBlock_kernel).trans
      (unitaryQuotientEquiv.trans specialProjectiveEquiv))

/-- The unconditional fixed-line input for nondegenerate-stabilizer assembly. -/
theorem coordinateLineStabilizer_nonempty :
    Nonempty (projectiveStabilizer (coordinateSubspace 1) ≃* Carrier 3) :=
  ⟨coordinateLineStabilizerEquiv⟩

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers.Line
