module

public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortLifts
public import Theory.SpecificGroups.Monster.Construction.LocalC.TensorSpace

/-!
# The orthogonal sum used by the local Monster construction

For an explicitly supplied source lattice comparison, the natural-spin,
short-extraspecial, and symmetric summands form a positive definite real
space of dimension 196,884. Its form is their orthogonal direct sum, with
unit short vectors and the existing trace form on symmetric matrices.
Block maps preserving the three forms preserve the sum. The block sign
involution fixes exactly the last two summands.

This is an independent conditional assembly: the final fixed space must
instantiate the Section 27 comparison, and the local-group construction
must identify its actual central involution with the block sign map.
Neither that comparison nor the group `C` is postulated here.

Source: Aschbacher, *Sporadic Groups*, the orthogonal-space construction
at the end of Section 27 and Lemma 27.9, printed p. 150.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.LocalC

variable (e : LatticeComparison)

/-- The three source summands. This construction still requires the actual
source lattice comparison before it gives the fixed final Griess space. -/
abbrev OrthogonalSpace := MinusSpace × (ShortSpace e × SymmetricPart)

def minusProjection : OrthogonalSpace e →ₗ[ℝ] MinusSpace := LinearMap.fst ℝ _ _
def shortProjection : OrthogonalSpace e →ₗ[ℝ] ShortSpace e :=
  (LinearMap.fst ℝ _ _).comp (LinearMap.snd ℝ _ _)
def symmetricProjection : OrthogonalSpace e →ₗ[ℝ] SymmetricPart :=
  (LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)

def gamma : LinearMap.BilinForm ℝ (OrthogonalSpace e) :=
  minusForm.compl₁₂ (minusProjection e) (minusProjection e) +
    (shortForm e).compl₁₂ (shortProjection e) (shortProjection e) +
    symmetricGammaForm.compl₁₂ (symmetricProjection e) (symmetricProjection e)

theorem gamma_apply (v w : OrthogonalSpace e) : gamma e v w =
    minusForm v.1 w.1 + shortForm e v.2.1 w.2.1 + symmetricGamma v.2.2 w.2.2 := rfl

theorem orthogonalSpace_finrank : Module.finrank ℝ (OrthogonalSpace e) = 196884 := by
  rw [Module.finrank_prod, Module.finrank_prod, minusSpace_finrank,
    shortSpace_finrank, symmetricPart_finrank]

theorem gamma_symmetric (v w : OrthogonalSpace e) : gamma e v w = gamma e w v := by
  simp only [gamma_apply, minusForm_symmetric v.1, shortForm_symmetric e v.2.1,
    symmetricGamma_comm v.2.2]

theorem gamma_nonneg (v : OrthogonalSpace e) : 0 ≤ gamma e v v :=
  add_nonneg (add_nonneg (minusForm_nonneg _)
    ((shortLiftSigns e).form_nonneg _)) (symmetricGamma_nonneg _)

theorem gamma_pos (v : OrthogonalSpace e) (hv : v ≠ 0) : 0 < gamma e v v := by
  have hm := minusForm_nonneg v.1
  have hr := (shortLiftSigns e).form_nonneg v.2.1
  have hs := symmetricGamma_nonneg v.2.2
  change 0 ≤ shortForm e v.2.1 v.2.1 at hr
  rw [gamma_apply]
  by_cases h₁ : v.1 = 0
  · by_cases h₂ : v.2.1 = 0
    · have h₃ : v.2.2 ≠ 0 := by
        intro h₃
        apply hv
        exact Prod.ext h₁ (Prod.ext h₂ h₃)
      have hp := symmetricGamma_pos v.2.2 h₃
      linarith
    · have hp := shortForm_pos e v.2.1 h₂
      linarith
  · have hp := minusForm_pos v.1 h₁
    linarith

theorem gamma_eq_zero_iff (v : OrthogonalSpace e) : gamma e v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    exact (ne_of_gt (gamma_pos e v hv)) h
  · rintro rfl
    exact map_zero (gamma e 0)

def minusInclusion : MinusSpace →ₗ[ℝ] OrthogonalSpace e := LinearMap.inl ℝ _ _
def shortInclusion : ShortSpace e →ₗ[ℝ] OrthogonalSpace e :=
  (LinearMap.inr ℝ _ _).comp (LinearMap.inl ℝ _ _)
def symmetricInclusion : SymmetricPart →ₗ[ℝ] OrthogonalSpace e :=
  (LinearMap.inr ℝ _ _).comp (LinearMap.inr ℝ _ _)

theorem gamma_minus (v w : MinusSpace) :
    gamma e (minusInclusion e v) (minusInclusion e w) = minusForm v w := by
  change minusForm v w + shortForm e 0 0 + symmetricGammaForm 0 0 = _
  simp

theorem gamma_short (v w : ShortSpace e) :
    gamma e (shortInclusion e v) (shortInclusion e w) = shortForm e v w := by
  change minusForm 0 0 + shortForm e v w + symmetricGammaForm 0 0 = _
  simp

theorem gamma_symmetricPart (v w : SymmetricPart) :
    gamma e (symmetricInclusion e v) (symmetricInclusion e w) = symmetricGamma v w := by
  change minusForm 0 0 + shortForm e 0 0 + symmetricGammaForm v w = _
  simp only [map_zero, zero_add]
  rfl

theorem gamma_minus_short (v : MinusSpace) (w : ShortSpace e) :
    gamma e (minusInclusion e v) (shortInclusion e w) = 0 := by
  change minusForm v 0 + shortForm e 0 w + symmetricGammaForm 0 0 = 0
  simp

theorem gamma_minus_symmetric (v : MinusSpace) (w : SymmetricPart) :
    gamma e (minusInclusion e v) (symmetricInclusion e w) = 0 := by
  change minusForm v 0 + shortForm e 0 0 + symmetricGammaForm 0 w = 0
  simp

theorem gamma_short_symmetric (v : ShortSpace e) (w : SymmetricPart) :
    gamma e (shortInclusion e v) (symmetricInclusion e w) = 0 := by
  change minusForm 0 0 + shortForm e v 0 + symmetricGammaForm 0 w = 0
  simp

/-- The block action used when assembling the three orthogonal representations. -/
def blockMap (f : Module.End ℝ MinusSpace) (g : Module.End ℝ (ShortSpace e))
    (h : Module.End ℝ SymmetricPart) : Module.End ℝ (OrthogonalSpace e) :=
  f.prodMap (g.prodMap h)

theorem blockMap_preserves_gamma
    (f : Module.End ℝ MinusSpace) (g : Module.End ℝ (ShortSpace e))
    (h : Module.End ℝ SymmetricPart)
    (hf : ∀ v w, minusForm (f v) (f w) = minusForm v w)
    (hg : ∀ v w, shortForm e (g v) (g w) = shortForm e v w)
    (hh : ∀ v w, symmetricGamma (h v) (h w) = symmetricGamma v w)
    (v w : OrthogonalSpace e) :
    gamma e (blockMap e f g h v) (blockMap e f g h w) = gamma e v w := by
  change minusForm (f v.1) (f w.1) + shortForm e (g v.2.1) (g w.2.1) +
    symmetricGamma (h v.2.2) (h w.2.2) = _
  rw [hf, hg, hh]
  rfl

/-- The sign involution on the orthogonal sum. Its identification with the
actual image of `z1N` belongs to the local-group assembly. -/
def parityEquiv : OrthogonalSpace e ≃ₗ[ℝ] OrthogonalSpace e where
  toFun v := (-v.1, v.2)
  invFun v := (-v.1, v.2)
  left_inv v := by simp
  right_inv v := by simp
  map_add' v w := Prod.ext (neg_add v.1 w.1) rfl
  map_smul' a v := by ext <;> simp

theorem parity_preserves_gamma (v w : OrthogonalSpace e) :
    gamma e (parityEquiv e v) (parityEquiv e w) = gamma e v w := by
  change minusForm (-v.1) (-w.1) + shortForm e v.2.1 w.2.1 +
    symmetricGamma v.2.2 w.2.2 = _
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  rfl

theorem parity_fixed_iff (v : OrthogonalSpace e) : parityEquiv e v = v ↔ v.1 = 0 := by
  change (-v.1, v.2) = (v.1, v.2) ↔ _
  simp only [Prod.mk.injEq, and_true]
  constructor
  · intro h
    have hs : (2 : ℝ) • v.1 = 0 := by
      rw [two_smul]
      calc
        v.1 + v.1 = -v.1 + v.1 := congrArg (fun u => u + v.1) h.symm
        _ = 0 := neg_add_cancel _
    exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
  · intro h
    simp [h]

end Sporadic.Monster.Construction.LocalC
