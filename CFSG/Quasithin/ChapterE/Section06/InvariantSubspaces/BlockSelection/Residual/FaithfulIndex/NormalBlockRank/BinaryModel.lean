module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.NormalBlockRank.RankTransfer
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.OuterFixed.Basic
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Mathlib.Tactic.FinCases

/-!
# Fixed cubic elements for the genuine binary PSL₂ outer complements

Every automorphism is inner times an entrywise field automorphism. Trace
preservation shows that the intersection of these two subgroups is trivial.
Field automorphisms fix the explicit cubic matrix with prime-field entries.
These facts construct the complement needed by the normal-extension rank proof.

The A₅ instance is transported through the proved projective-line isomorphism
PSL₂(4) ≃ A₅. This identifies only the core quotient, and makes no identification
between the different natural A₅ and L₂(4) block modules.

Source: the binary PSL₂ automorphism theorem (GLS, Volume 4, Chapter 4,
Lemma 3.1(a)), and the block inference in Aschbacher--Smith, combined manuscript
(1 March 2004), proof of E.6.14, printed p.251.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.NormalBlockRank
open BenderSuzuki.MatrixGroups BenderSuzuki.ZD.Linear

private noncomputable def fieldActionHom {F : Type*} [Field F] [CharP F 2] :
    (F ≃+* F) →* MulAut (PSL2MatrixGroup F) where
  toFun := fieldAut
  map_one' := fieldAut_refl
  map_mul' σ τ := fieldAut_trans σ τ

private def cubicMatrix (F : Type*) [Field F] :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩

private theorem cubicMatrix_order (F : Type*) [Field F] : orderOf (cubicMatrix F) = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    change (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h01 := congrArg (fun a : Matrix.SpecialLinearGroup (Fin 2) F => a.val 1 0) h
    simp [cubicMatrix] at h01

/-- The actual field automorphisms complement inner automorphisms and fix the
cubic matrix with entries in the prime field. -/
noncomputable def binaryCubicOuterComplement (F : Type*) [Field F] [Finite F]
    [CharP F 2] : CubicOuterComplement (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) where
  center_eq_bot := by
    apply bot_unique
    intro x hx
    apply psl2_conj_eq_one_implies x
    ext y
    change x * y * x⁻¹ = y
    rw [← mem_center_iff.mp hx y, mul_inv_cancel_right]
  outer := (fieldActionHom (F := F)).range
  disjoint := by
    apply disjoint_def.mpr
    intro a ha hb
    obtain ⟨g, rfl⟩ := ha
    obtain ⟨σ, hσ⟩ := hb
    have hs := fieldAut_eq_conj_implies_refl σ g hσ
    change fieldAut σ = MulAut.conj g at hσ
    rw [hs, fieldAut_refl] at hσ
    exact hσ.symm
  factor := by
    intro a
    obtain ⟨g, σ, ha⟩ := semilinear_coverage a
    exact ⟨g, fieldAut σ, ⟨σ, rfl⟩, ha⟩
  cubic := sl2QuotientEquiv F (cubicMatrix F)
  cubic_order :=
    (orderOf_injective (sl2QuotientEquiv F).toMonoidHom
      (sl2QuotientEquiv F).injective _).trans (cubicMatrix_order F)
  fixed := by
    rintro b ⟨σ, rfl⟩
    change fieldAut σ (BenderSuzuki.Converse.pi F (cubicMatrix F)) =
      BenderSuzuki.Converse.pi F (cubicMatrix F)
    rw [fieldAut_apply_pi]
    congr 1
    ext i j
    change σ ((cubicMatrix F).val i j) = (cubicMatrix F).val i j
    fin_cases i <;> fin_cases j <;> simp [cubicMatrix]

/-- Transport through the actual projective-line isomorphism PSL₂(4) ≃ A₅.
Only the core quotient is identified; the A₅ and L₂(4) modules stay distinct. -/
noncomputable def alternatingFiveCubicOuterComplement :
    CubicOuterComplement (alternatingGroup (Fin 5)) := by
  let e := Classical.choice
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; decide))
  exact (binaryCubicOuterComplement (GaloisField 2 2)).congr e.symm

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.NormalBlockRank
