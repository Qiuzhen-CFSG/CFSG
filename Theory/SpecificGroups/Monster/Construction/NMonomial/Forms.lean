module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.Spaces

/-!
# Source forms and orthogonality on the non-octad coordinates

All forms here are restrictions of the existing fixed `griessGamma` and
`griessBeta`. The matrix and short-family orthogonality proves that the three
non-octad inclusions are pairwise orthogonal, as is their sum to the octad
span. Thus the linear comparison of `Spaces` is an orthogonal decomposition.
The marked pair generators use exactly `wPlus = v+u` and `wMinus = v-u`.

Source: Aschbacher, *Sporadic Groups*, 27.8(5), 29.1, printed pp. 150, 154.
Invariance under the extended `N` actions is a separate assertion: this module
constructs the forms those actions must preserve, and proves their positivity.
-/

@[expose] public section
noncomputable section
open scoped BigOperators TensorProduct
namespace Sporadic.Monster.Construction.NMonomial
open LocalC ShortFamilies TrialitySpin Atlas.Codes Atlas.Fischer

/-- The marked natural coordinate vector corresponding to the source point `x`. -/
def pointVector (x : Omega) : NaturalSpace := Pi.single (coordinateMarking.symm x) 1

/-- The `xy` generator of the first pair summand, in the fixed coordinate marking. -/
def ePairOne (x y : Omega) (hxy : x ≠ y) : ESpace :=
  (⟨pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y),
    pairMatrix_mem_offDiagonal _ _ (fun h => hxy (coordinateMarking.symm.injective h))⟩, 0, 0)

/-- The second pair generator has the unscaled source normalization `v+u`. -/
def ePairTwo (x y : Omega) (hxy : x ≠ y) : ESpace :=
  (0, ⟨wPlus x y hxy, Submodule.subset_span ⟨⟨(x,y), hxy⟩, rfl⟩⟩, 0)

/-- The third pair generator has the unscaled source normalization `v-u`. -/
def ePairThree (x y : Omega) (hxy : x ≠ y) : ESpace :=
  (0, 0, ⟨wMinus x y hxy, Submodule.subset_span ⟨⟨(x,y), hxy⟩, rfl⟩⟩)

/-- The odd short generator, which 29.8 compares with a natural--half-spin tensor. -/
def zeroOdd (x : Omega) (b : ParkerLoop) : ZeroSpace :=
  (⟨shortVector sourceLatticeComparison (rOdd x b),
    Submodule.subset_span ⟨(x,b), rfl⟩⟩, 0)

/-- A tensor in the actual second-axis half-spin summand. -/
def zeroTwo (a : NaturalSpace) (s : B1A2) : ZeroSpace := (0, a ⊗ₜ[ℝ] s, 0)

/-- A tensor in the actual third-axis half-spin summand. -/
def zeroThree (a : NaturalSpace) (s : B1A3) : ZeroSpace := (0, 0, a ⊗ₜ[ℝ] s)

@[simp] theorem eInclusion_pairOne (x y : Omega) (hxy : x ≠ y) :
    eInclusion (ePairOne x y hxy) =
      symmetricInclusion sourceLatticeComparison
        (pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y)) := by
  simp [ePairOne, symmetricInclusion]

@[simp] theorem eInclusion_pairTwo (x y : Omega) (hxy : x ≠ y) :
    eInclusion (ePairTwo x y hxy) =
      shortInclusion sourceLatticeComparison (wPlus x y hxy) := by
  simp [ePairTwo, shortInclusion]

@[simp] theorem eInclusion_pairThree (x y : Omega) (hxy : x ≠ y) :
    eInclusion (ePairThree x y hxy) =
      shortInclusion sourceLatticeComparison (wMinus x y hxy) := by
  simp [ePairThree, shortInclusion]

@[simp] theorem zeroInclusion_odd (x : Omega) (b : ParkerLoop) :
    zeroInclusion (zeroOdd x b) =
      shortInclusion sourceLatticeComparison (shortVector sourceLatticeComparison (rOdd x b)) := by
  simp [zeroOdd, shortInclusion]

/-- The actual tensor inclusions use the inverse of the fixed spin restriction. -/
theorem zeroInclusion_two (a : NaturalSpace) (s : B1A2) :
    zeroInclusion (zeroTwo a s) = minusInclusion sourceLatticeComparison
      (a ⊗ₜ[ℝ] SpinActions.spinRestriction.symm (s,0)) := by
  have h : tensorSplitting (a ⊗ₜ[ℝ] SpinActions.spinRestriction.symm (s,0)) =
      (a ⊗ₜ[ℝ] s,0) := by simp
  rw [zeroInclusion_apply]
  change (tensorSplitting.symm (a ⊗ₜ[ℝ] s,0),0,0) = _
  rw [← h, tensorSplitting.symm_apply_apply]
  rfl

theorem zeroInclusion_three (a : NaturalSpace) (s : B1A3) :
    zeroInclusion (zeroThree a s) = minusInclusion sourceLatticeComparison
      (a ⊗ₜ[ℝ] SpinActions.spinRestriction.symm (0,s)) := by
  have h : tensorSplitting (a ⊗ₜ[ℝ] SpinActions.spinRestriction.symm (0,s)) =
      (0,a ⊗ₜ[ℝ] s) := by simp
  rw [zeroInclusion_apply]
  change (tensorSplitting.symm (0,a ⊗ₜ[ℝ] s),0,0) = _
  rw [← h, tensorSplitting.symm_apply_apply]
  rfl

def rGamma : LinearMap.BilinForm ℝ RSpace := griessGamma.compl₁₂ rInclusion rInclusion
def eGamma : LinearMap.BilinForm ℝ ESpace := griessGamma.compl₁₂ eInclusion eInclusion
def zeroGamma : LinearMap.BilinForm ℝ ZeroSpace :=
  griessGamma.compl₁₂ zeroInclusion zeroInclusion

def nonOctadGamma : LinearMap.BilinForm ℝ NonOctadSpace :=
  griessGamma.compl₁₂ nonOctadInclusion nonOctadInclusion

theorem rGamma_apply (a b : RSpace) : rGamma a b = ∑ i, a i * b i := by
  change griessGamma (rInclusion a) (rInclusion b) = _
  exact (gamma_symmetricPart sourceLatticeComparison _ _).trans (diagonal_gamma a b)

theorem griessBeta_rInclusion (a b c : RSpace) :
    griessBeta (rInclusion a) (rInclusion b) (rInclusion c) =
      4 * ∑ i, a i * b i * c i :=
  (griessBeta_SSS _ _ _).trans (diagonal_beta a b c)

theorem r_e_orthogonal (a : RSpace) (b : ESpace) :
    griessGamma (rInclusion a) (eInclusion b) = 0 := by
  rw [rInclusion_apply, eInclusion_apply, griessGamma_components]
  change minusForm 0 0 + shortForm sourceLatticeComparison 0 _ +
    symmetricGamma (diagonal a) b.1.val = 0
  simp [diagonal_offDiagonal_orthogonal]

theorem r_zero_orthogonal (a : RSpace) (b : ZeroSpace) :
    griessGamma (rInclusion a) (zeroInclusion b) = 0 := by
  rw [rInclusion_apply, zeroInclusion_apply, griessGamma_components]
  change minusForm 0 _ + shortForm sourceLatticeComparison 0 _ +
    symmetricGammaForm _ 0 = 0
  simp

theorem e_zero_orthogonal (a : ESpace) (b : ZeroSpace) :
    griessGamma (eInclusion a) (zeroInclusion b) = 0 := by
  rw [eInclusion_apply, zeroInclusion_apply, griessGamma_components]
  change minusForm 0 _ + shortForm sourceLatticeComparison (a.2.1.val + a.2.2.val) b.1.val +
    symmetricGammaForm _ 0 = 0
  have hp := summandSpace_orthogonal (i := .plus) (j := .odd) (by decide) a.2.1.prop b.1.prop
  have hm := summandSpace_orthogonal (i := .minus) (j := .odd) (by decide) a.2.2.prop b.1.prop
  simp [hp, hm]

theorem octad_r_orthogonal (a : octadSpace) (b : RSpace) :
    griessGamma (octadInclusion a) (rInclusion b) = 0 :=
  gamma_short_symmetric sourceLatticeComparison a.val (diagonal b)

theorem octad_e_orthogonal (a : octadSpace) (b : ESpace) :
    griessGamma (octadInclusion a) (eInclusion b) = 0 := by
  rw [octadInclusion_apply, eInclusion_apply, griessGamma_components]
  change minusForm 0 0 + shortForm sourceLatticeComparison a.val (b.2.1.val + b.2.2.val) +
    symmetricGammaForm 0 _ = 0
  have hp := summandSpace_orthogonal (i := .octad) (j := .plus) (by decide) a.prop b.2.1.prop
  have hm := summandSpace_orthogonal (i := .octad) (j := .minus) (by decide) a.prop b.2.2.prop
  simp [hp, hm]

theorem octad_zero_orthogonal (a : octadSpace) (b : ZeroSpace) :
    griessGamma (octadInclusion a) (zeroInclusion b) = 0 := by
  rw [octadInclusion_apply, zeroInclusion_apply, griessGamma_components]
  change minusForm 0 _ + shortForm sourceLatticeComparison a.val b.1.val +
    symmetricGammaForm 0 0 = 0
  have h := summandSpace_orthogonal (i := .octad) (j := .odd) (by decide) a.prop b.1.prop
  simp [h]

theorem octad_nonOctad_orthogonal (a : octadSpace) (b : NonOctadSpace) :
    griessGamma (octadInclusion a) (nonOctadInclusion b) = 0 := by
  simp only [nonOctadInclusion_apply, map_add, octad_r_orthogonal,
    octad_e_orthogonal, octad_zero_orthogonal, add_zero]

/-- The three diagonal blocks are the entire induced bilinear form. -/
theorem nonOctadGamma_components (a b : NonOctadSpace) :
    nonOctadGamma a b = rGamma a.1 b.1 + eGamma a.2.1 b.2.1 + zeroGamma a.2.2 b.2.2 := by
  have her := fun x y => (griessGamma_symmetric (eInclusion x) (rInclusion y)).trans
    (r_e_orthogonal y x)
  have hzr := fun x y => (griessGamma_symmetric (zeroInclusion x) (rInclusion y)).trans
    (r_zero_orthogonal y x)
  have hze := fun x y => (griessGamma_symmetric (zeroInclusion x) (eInclusion y)).trans
    (e_zero_orthogonal y x)
  change griessGamma (nonOctadInclusion a) (nonOctadInclusion b) = _
  simp only [nonOctadInclusion_apply, map_add, LinearMap.add_apply,
    r_e_orthogonal, r_zero_orthogonal, e_zero_orthogonal, her, hzr, hze, add_zero, zero_add]
  rfl

theorem eGamma_components (a b : ESpace) :
    eGamma a b = symmetricGamma a.1.val b.1.val +
      shortForm sourceLatticeComparison a.2.1.val b.2.1.val +
      shortForm sourceLatticeComparison a.2.2.val b.2.2.val := by
  have hp := summandSpace_orthogonal (i := .plus) (j := .minus) (by decide) a.2.1.prop b.2.2.prop
  have hm := summandSpace_orthogonal (i := .minus) (j := .plus) (by decide) a.2.2.prop b.2.1.prop
  change griessGamma (eInclusion a) (eInclusion b) = _
  rw [eInclusion_apply, eInclusion_apply, griessGamma_components]
  simp only [map_add, LinearMap.add_apply, hp, hm, map_zero,
    add_zero, zero_add]
  ring

theorem zeroGamma_components (a b : ZeroSpace) :
    zeroGamma a b = shortForm sourceLatticeComparison a.1.val b.1.val +
      minusForm (tensorSplitting.symm a.2) (tensorSplitting.symm b.2) := by
  change griessGamma (zeroInclusion a) (zeroInclusion b) = _
  rw [zeroInclusion_apply, zeroInclusion_apply, griessGamma_components]
  change minusForm _ _ + shortForm sourceLatticeComparison _ _ + symmetricGammaForm 0 0 = _
  rw [map_zero, add_zero, add_comm]

/-- The full comparison also identifies the existing form, with no scaling. -/
theorem griessSplitting_gamma (a b : octadSpace) (x y : NonOctadSpace) :
    griessGamma (griessSplitting (a,x)) (griessSplitting (b,y)) =
      shortForm sourceLatticeComparison a.val b.val + nonOctadGamma x y := by
  rw [griessSplitting_apply, griessSplitting_apply]
  have h := (griessGamma_symmetric (nonOctadInclusion x) (octadInclusion b)).trans
    (octad_nonOctad_orthogonal b x)
  simp only [map_add, LinearMap.add_apply, octad_nonOctad_orthogonal, h, add_zero, zero_add]
  change gamma sourceLatticeComparison (shortInclusion sourceLatticeComparison a.val)
    (shortInclusion sourceLatticeComparison b.val) + _ = _
  rw [gamma_short]
  rfl

theorem nonOctadGamma_pos (x : NonOctadSpace) (hx : x ≠ 0) :
    0 < nonOctadGamma x x :=
  griessGamma_pos (nonOctadInclusion x)
    (fun h => hx (nonOctadInclusion_injective (h.trans (map_zero nonOctadInclusion).symm)))

theorem nonOctadGamma_nondegenerate : nonOctadGamma.Nondegenerate :=
  Griess.nondegenerate_of_positive (V := NonOctadSpace) nonOctadGamma nonOctadGamma_pos

/-- The squared length of each unscaled `w` generator is two. -/
theorem eGamma_pairTwo (x y : Omega) (hxy : x ≠ y) :
    eGamma (ePairTwo x y hxy) (ePairTwo x y hxy) = 2 := by
  change griessGamma (eInclusion _) (eInclusion _) = _
  rw [eInclusion_pairTwo]
  exact (gamma_short sourceLatticeComparison _ _).trans (form_wPlus_self x y hxy)

theorem eGamma_pairThree (x y : Omega) (hxy : x ≠ y) :
    eGamma (ePairThree x y hxy) (ePairThree x y hxy) = 2 := by
  change griessGamma (eInclusion _) (eInclusion _) = _
  rw [eInclusion_pairThree]
  exact (gamma_short sourceLatticeComparison _ _).trans (form_wMinus_self x y hxy)

end Sporadic.Monster.Construction.NMonomial
