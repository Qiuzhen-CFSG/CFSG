module

public import GorensteinWalter.PGL2ConcreteSplitTorusCentralizer
public import GorensteinWalter.PGL2DeterminantSquare
public import GorensteinWalter.PSL2InvolutionFusion
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.Multiplicity

/-!
# The actual inner split-torus marking

The determinant-square criterion puts every full-torus square inside
PSL₂. Over an odd quadratic field, minus one is a square, so the canonical
full split-torus involution has an actual involution lift in PSL₂.
Source application: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2
 theorem full_split_torus_square_mem_psl
    {F : Type*} [Field F] (a : Fˣ) :
    pGammaL2FullSplitTorus F (a ^ 2) ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  change Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F (a ^ 2)) ∈ _
  apply (pgl2_mk_mem_psl2_range_iff_det_isSquare _).mpr
  change IsSquare (Matrix.det (Matrix.diagonal ![((a ^ 2 : Fˣ) : F), 1]))
  simp only [Matrix.det_diagonal, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, Units.val_pow_eq_pow_val]
  exact ⟨a, by simp only [pow_two]⟩

 theorem square_field_split_involution_psl
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) :
    ∃ t : PSL2 F, IsInvolution t ∧
      Matrix.ProjectiveSpecialLinearGroup.toPGL t = pGammaL2FullSplitTorus F (-1) := by
  let : Fintype F := Fintype.ofFinite F
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, 2, Fact.out, ho, by decide, hF⟩
  have hsq : IsSquare (-1 : F) := by
    apply FiniteField.isSquare_neg_one_iff.mpr
    rw [← Nat.card_eq_fintype_card, hF]
    have hh : (p : ℤ) ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd (by exact_mod_cast ho)
    have hh' : p ^ 2 % 4 = 1 := by exact_mod_cast hh
    omega
  have hm : pGammaL2FullSplitTorus F (-1) ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    change Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F (-1)) ∈ _
    apply (pgl2_mk_mem_psl2_range_iff_det_isSquare _).mpr
    change IsSquare (Matrix.det (Matrix.diagonal ![((-1 : Fˣ) : F), 1]))
    simpa only [Matrix.det_diagonal, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, Units.val_neg, Units.val_one] using hsq
  obtain ⟨t, ht⟩ := hm
  have hi := (pgl2_fullSplitTorus_centralizer_data F hodd).choose_spec.2.2.2.1
  refine ⟨t, ⟨?_, ?_⟩, ht⟩
  · intro he
    exact hi.1 (by simpa only [he, map_one] using ht.symm)
  · apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    simpa only [map_pow, map_one, ht] using hi.2
end Theory.PSL2
