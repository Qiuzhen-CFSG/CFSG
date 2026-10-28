module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Position.Block

/-!
# The graph generator in the marked centralizer quotient

For a two-by-two matrix A, transpose(A) J A J⁻¹ is the scalar det(A).
The determinant-corrected three-by-three blocks satisfy the corresponding
identity. Scalars vanish in the radical quotient, so inverse transpose
acts there by conjugation with the class of J. The marked projective map
is surjective and the radical quotient is centerless; hence the graph
generator itself has precisely that projective image.

This supplies the graph calculation for the actual full actor in the
prime-five branch of Aschbacher--Smith E.1.14(7), p.214.
-/

public section
open Subgroup Theory.GroupTheory Matrix GorensteinWalter
open scoped MatrixGroups Matrix

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection.Position
open FiveSourceAudit PSUThreeGeneration
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

@[expose] def skew : GL (Fin 2) (ZMod 5) :=
  ⟨!![0,1;4,0], !![0,4;1,0], by decide +kernel, by decide +kernel⟩

theorem skew_det : skew.det = 1 := by decide +kernel

theorem transpose_block_mul (A : GL (Fin 2) (ZMod 5)) :
    (block A).transpose * block (skew * A * skew⁻¹) =
      block (GeneralLinearGroup.scalar (Fin 2) A.det) := by
  apply Subtype.ext
  change (block A).val.transpose * (block (skew * A * skew⁻¹)).val =
    (block (GeneralLinearGroup.scalar (Fin 2) A.det)).val
  rw [block_formula, block_formula, block_formula]
  have hd : (skew * A * skew⁻¹).det = A.det := by
    simp only [map_mul, map_inv, skew_det, one_mul, inv_one, mul_one]
  rw [hd, GeneralLinearGroup.det_scalar]
  have h4 : (4 : ZMod 5) = -1 := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.coe_scalar,
      skew, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two,
      GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, pow_two, h4] <;> ring

theorem graph_block (A : GL (Fin 2) (ZMod 5)) :
    (block A).transpose⁻¹ = block (skew * A * skew⁻¹) *
      (block (GeneralLinearGroup.scalar (Fin 2) A.det))⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, transpose_block_mul, mul_inv_cancel]

@[expose] noncomputable def graphC : C :=
  ⟨graphElement, standardSylow_le_centralizer graph_mem_standardSylow⟩

theorem graphC_embed (A : GL (Fin 2) (ZMod 5)) :
    graphC * embed A = embed (skew * A * skew⁻¹) *
      (embed (GeneralLinearGroup.scalar (Fin 2) A.det))⁻¹ * graphC := by
  apply Subtype.ext
  change graphElement * FiveSourceAudit.innerSL (block A) =
    FiveSourceAudit.innerSL (block (skew * A * skew⁻¹)) *
      (FiveSourceAudit.innerSL (block (GeneralLinearGroup.scalar (Fin 2) A.det)))⁻¹ *
        graphElement
  rw [graph_innerSL, graph_block, map_mul, map_inv]

theorem quotient_embed_scalar (u : (ZMod 5)ˣ) :
    q (embed (GeneralLinearGroup.scalar (Fin 2) u)) = 1 := by
  rw [← projective_mk, ProjGenLinGroup.mk_scalar, map_one]

theorem graph_quotient_action (A : GL (Fin 2) (ZMod 5)) :
    q graphC * q (embed A) =
      q (embed skew) * q (embed A) * (q (embed skew))⁻¹ * q graphC := by
  have h := congrArg q (graphC_embed A)
  simpa only [map_mul, map_inv, quotient_embed_scalar, inv_one, mul_one] using h

theorem graph_quotient (hmodel : Nonempty (Q ≃* Equiv.Perm (Fin 5))) :
    q graphC = projective (ProjGenLinGroup.mk skew) := by
  rw [projective_mk]
  have hc : (q (embed skew))⁻¹ * q graphC ∈ center Q := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨p,rfl⟩ := projective_surjective hmodel y
    obtain ⟨A,rfl⟩ := ProjGenLinGroup.mk_surjective p
    rw [projective_mk]
    calc
      _ = (q (embed skew))⁻¹ *
          (q (embed skew) * q (embed A) * (q (embed skew))⁻¹ * q graphC) := by group
      _ = (q (embed skew))⁻¹ * (q graphC * q (embed A)) := by rw [← graph_quotient_action]
      _ = _ := by group
  rw [center_quotient, mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection.Position
