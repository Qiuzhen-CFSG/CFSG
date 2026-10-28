module

public import Theory.SpecificGroups.PSL3.SevenAction.NormalForm

/-!
# Involutions in the pointwise fixer of the SL₂(7) block

A linear automorphism fixing the projective block lifts to an automorphism
fixing its SL₂(7) preimage, because maps from a perfect group into a central
extension are determined by their projections. The two elementary block
matrices force its conjugating matrix to be diag(a,a,c). If the automorphism
has square one, then a² = c², leaving the identity and the standard inner
involution.

For a linear-times-graph automorphism, the same equations force a skew block
with a one-dimensional symmetric complement. Its square is the standard
inner involution, so it cannot have order dividing two. All calculations use
the canonical SL₃(7) projection, whose order-three center is retained.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, the PSL₃(7)
case in the proof of 15.3.38, printed p.1137; the linear centralizer is the
one used in A.3.21(a), printed p.55.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3.SevenAction
local notation "𝔽" => ZMod 7
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem centerAction_injective : Function.Injective (centerAction 𝔽) := by
  let : Group.IsPerfect SL(3,𝔽) := Atlas.sl_perfect 3 (by decide)
  have he : centerAction 𝔽 = Subgroup.quotientAut (center SL(3,𝔽)) := by
    ext a x
    obtain ⟨y, rfl⟩ := projection_surjective 𝔽 x
    change centerAction 𝔽 a (QuotientGroup.mk y) =
      (center SL(3,𝔽)).quotientAut a (QuotientGroup.mk' (center SL(3,𝔽)) y)
    rw [centerAction_mk, Subgroup.quotientAut_apply_mk]
    rfl
  rw [he]
  exact MulAut.quotient_center_injective

private theorem fixes_block_lift (α : MulAut SL(3,𝔽))
    (h : ∀ x : block, centerAction 𝔽 α x = x) :
    ∀ x : SL(2,𝔽), α (blockSL x) = blockSL x := by
  let : Group.IsPerfect SL(2,𝔽) :=
    ⟨Matrix.SL2.commutator_eq_top (a := (2 : 𝔽)) (by decide) (by decide)⟩
  have he := PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
    (projection 𝔽) (le_of_eq (projection_ker 𝔽))
    (α.toMonoidHom.comp blockSL) blockSL (by
      ext x
      exact h ⟨blockMap x, ⟨x,rfl⟩⟩)
  exact fun x => DFunLike.congr_fun he x

private def upper : SL(2,𝔽) := ⟨!![1,1;0,1], by decide⟩
private def lower : SL(2,𝔽) := ⟨!![1,0;1,1], by decide⟩
private def root : SL(3,𝔽) := ⟨!![1,0,1;0,1,0;0,0,1], by decide⟩

private theorem upper_val : (blockSL upper).val = !![1,1,0;0,1,0;0,0,1] := by
  change SL3.blockMatrix 𝔽 (SpecialLinearGroup.toGL upper) = _
  decide
private theorem lower_val : (blockSL lower).val = !![1,0,0;1,1,0;0,0,1] := by
  change SL3.blockMatrix 𝔽 (SpecialLinearGroup.toGL lower) = _
  decide

private theorem linear_shape (g : GL (Fin 3) 𝔽)
    (h : ∀ x : SL(2,𝔽), linearConjSL 𝔽 g (blockSL x) = blockSL x) :
    g.val = !![g.val 0 0,0,0;0,g.val 0 0,0;0,0,g.val 2 2] := by
  have hc (x : SL(2,𝔽)) : g.val * (blockSL x).val = (blockSL x).val * g.val := by
    have he := congrArg SpecialLinearGroup.toGL (h x)
    rw [linearConjSL_toGL] at he
    exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp he)
  have hu := hc upper
  have hl := hc lower
  rw [upper_val] at hu
  rw [lower_val] at hl
  have h10 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 0 0) hu
  have h11 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 0 1) hu
  have h12 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 0 2) hu
  have h20 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 2 1) hu
  have h01 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 0 0) hl
  have h02 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 1 2) hl
  have h21 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 2 0) hl
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h10 h11 h12 h20 h01 h02 h21
  have hd : g.val 1 1 = g.val 0 0 := by linear_combination -h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, hd, h12, h20, h01, h02, h21]

private theorem graph_shape (g : GL (Fin 3) 𝔽)
    (h : ∀ x : SL(2,𝔽),
      (linearConjSL 𝔽 g * graphSL 𝔽) (blockSL x) = blockSL x) :
    g.val = !![0,g.val 0 1,0;-g.val 0 1,0,0;0,0,g.val 2 2] := by
  have hc (x : SL(2,𝔽)) :
      (blockSL x).val * g.val * (blockSL x).val.transpose = g.val := by
    have he := congrArg SpecialLinearGroup.toGL (h x)
    change SpecialLinearGroup.toGL (linearConjSL 𝔽 g (graphSL 𝔽 (blockSL x))) = _ at he
    rw [linearConjSL_toGL, graphSL_toGL] at he
    have he' : g = SpecialLinearGroup.toGL (blockSL x) * g *
        (inverseTransposeGL (SpecialLinearGroup.toGL (blockSL x)))⁻¹ := by
      calc
        g = (g * inverseTransposeGL (SpecialLinearGroup.toGL (blockSL x)) * g⁻¹) *
            g * (inverseTransposeGL (SpecialLinearGroup.toGL (blockSL x)))⁻¹ := by group
        _ = _ := by rw [he]
    exact congrArg Units.val he'.symm
  have hu := hc upper
  have hl := hc lower
  rw [upper_val] at hu
  rw [lower_val] at hl
  have h11 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 0 1) hu
  have h10 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 0 0) hu
  have h12 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 0 2) hu
  have h21 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 2 0) hu
  have h00 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 1 0) hl
  have h02 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 1 2) hl
  have h20 := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 2 1) hl
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at h11 h10 h12 h21 h00 h02 h20
  have hskew : g.val 1 0 = - g.val 0 1 := by linear_combination h10 - h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h12, h21, h02, h20, hskew]

private theorem graph_square (g : GL (Fin 3) 𝔽)
    (h : ∀ x : block, (linearConj 𝔽 g * graph 𝔽) x = x) :
    (linearConj 𝔽 g * graph 𝔽) ^ 2 = actor := by
  have hf : ∀ x : block, centerAction 𝔽 (linearConjSL 𝔽 g * graphSL 𝔽) x = x := by
    rw [map_mul]
    exact h
  have hg := graph_shape g (fixes_block_lift _ hf)
  have hm : g * inverseTransposeGL g = SpecialLinearGroup.toGL (SL3.standardInvolution 𝔽) := by
    apply (eq_mul_inv_iff_mul_eq).mp
    apply Units.ext
    change g.val = (SL3.standardInvolution 𝔽).val * g.val.transpose
    rw [hg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SL3.standardInvolution, Matrix.mul_apply, Fin.sum_univ_three]
  calc
    _ = linearConj 𝔽 g * (graph 𝔽 * linearConj 𝔽 g) * graph 𝔽 := by
      rw [pow_two]; group
    _ = linearConj 𝔽 (g * inverseTransposeGL g) := by
      rw [graph_linearConj, map_mul]
      have hs : graph 𝔽 * graph 𝔽 = 1 := by simpa only [pow_two] using graph_sq 𝔽
      simp only [mul_assoc, hs, mul_one]
    _ = actor := by rw [hm, linearConj_toGL]; rfl

private theorem actor_ne_one : actor ≠ 1 := by
  intro he
  have hdesc : centerAction 𝔽 (MulAut.conj (SL3.standardInvolution 𝔽)) = actor := by
    ext x
    obtain ⟨y, rfl⟩ := projection_surjective 𝔽 x
    rfl
  have hlift : MulAut.conj (SL3.standardInvolution 𝔽) = 1 := by
    apply centerAction_injective
    rw [hdesc, he, map_one]
  have hn : MulAut.conj (SL3.standardInvolution 𝔽) root ≠ root := by decide
  exact hn (DFunLike.congr_fun hlift root)

private theorem linear_involution_fixer (g : GL (Fin 3) 𝔽)
    (hsq : linearConj 𝔽 g ^ 2 = 1)
    (h : ∀ x : block, linearConj 𝔽 g x = x) :
    linearConj 𝔽 g = 1 ∨ linearConj 𝔽 g = actor := by
  have hg := linear_shape g (fixes_block_lift _ h)
  have hc : g.val 2 2 ≠ 0 := by
    intro he
    apply GeneralLinearGroup.det_ne_zero g
    rw [hg]
    simp [Matrix.det_fin_three, he]
  have hlift : linearConjSL 𝔽 g ^ 2 = 1 := by
    apply centerAction_injective
    rw [map_pow, map_one]
    exact hsq
  have hr : linearConjSL 𝔽 (g ^ 2) root = root := by rw [map_pow, hlift]; rfl
  have he := congrArg SpecialLinearGroup.toGL hr
  rw [linearConjSL_toGL] at he
  have hm := congrArg Units.val (mul_inv_eq_iff_eq_mul.mp he)
  have hs := congrArg (fun m : Matrix (Fin 3) (Fin 3) 𝔽 => m 0 2) hm
  simp only [pow_two, Units.val_mul] at hs
  change ((g.val * g.val) * root.val) 0 2 = (root.val * (g.val * g.val)) 0 2 at hs
  rw [hg] at hs
  simp [root, Matrix.mul_apply, Fin.sum_univ_three] at hs
  let u : 𝔽ˣ := Units.mk0 (g.val 2 2) hc
  have scalar_trivial : linearConj 𝔽 (GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := projection_surjective 𝔽 y
    change QuotientGroup.mk (linearConjSL 𝔽 (GeneralLinearGroup.scalar (Fin 3) u) x) =
      QuotientGroup.mk x
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [linearConjSL_toGL, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]
  rcases mul_self_eq_mul_self_iff.mp hs with hpos | hneg
  · left
    have he : g = GeneralLinearGroup.scalar (Fin 3) u := by
      apply Units.ext
      rw [hg]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [GeneralLinearGroup.coe_scalar, Matrix.scalar, u, hpos]
    rw [he, scalar_trivial]
  · right
    have he : g = GeneralLinearGroup.scalar (Fin 3) u *
        SpecialLinearGroup.toGL (SL3.standardInvolution 𝔽) := by
      apply Units.ext
      change g.val = (GeneralLinearGroup.scalar (Fin 3) u).val *
        (SL3.standardInvolution 𝔽).val
      rw [hg]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [GeneralLinearGroup.coe_scalar, Matrix.scalar, u, hneg,
          SL3.standardInvolution, Matrix.mul_apply, Fin.sum_univ_three]
    rw [he, map_mul, scalar_trivial, one_mul, linearConj_toGL]
    rfl

/-- The only automorphisms of order dividing two fixing the actual projective
SL₂(7) block pointwise are the identity and its standard inner involution. -/
theorem involutive_block_fixer (α : MulAut Model) (hsq : α ^ 2 = 1)
    (h : ∀ x : block, α x = x) : α = 1 ∨ α = actor := by
  obtain ⟨g, rfl | rfl⟩ := automorphism_normal_form α
  · exact linear_involution_fixer g hsq h
  · exact (actor_ne_one ((graph_square g h).symm.trans hsq)).elim

end Matrix.PSL3.SevenAction
