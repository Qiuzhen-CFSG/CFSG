module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.SymmetricSpaces
public import Theory.SpecificGroups.Monster.Construction.GriessCarrier
public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies.Splitting
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.SpinActions.Decomposition
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The literal non-octad summands of the Griess space

`ESpace` consists of the off-diagonal symmetric matrices and the existing
`wPlus`, `wMinus` spans. `ZeroSpace` consists of the existing odd short span
and the natural tensor each of the two genuine half-spin spaces. Together
with the diagonal `RSpace` these form `NonOctadSpace`.

The explicit coordinate shuffle, the matrix splitting, the already proved
short-space splitting, and tensor distribution give a linear equivalence
from `octadSpace × NonOctadSpace` to the fixed `GriessSpace`. Its two
restrictions are the literal source inclusions and have complementary images.
No extension of a representation is assumed by this geometric construction.

Source: Aschbacher, *Sporadic Groups*, 27.8(5), 29.1, printed pp. 150, 154.
-/

public section
noncomputable section
open scoped DirectSum TensorProduct
namespace Sporadic.Monster.Construction.NMonomial
open LocalC ShortFamilies TrialitySpin

/-- The two natural--half-spin spaces in 29.1(4), using the existing spin axes. -/
abbrev TensorTwo := NaturalSpace ⊗[ℝ] B1A2
abbrev TensorThree := NaturalSpace ⊗[ℝ] B1A3

/-- The actual restriction of the spin factor followed by tensor distribution. -/
@[expose] def tensorSplitting : MinusSpace ≃ₗ[ℝ] TensorTwo × TensorThree :=
  (TensorProduct.congr (LinearEquiv.refl ℝ NaturalSpace) SpinActions.spinRestriction).trans
    (TensorProduct.prodRight ℝ ℝ NaturalSpace B1A2 B1A3)

@[simp] theorem tensorSplitting_tmul (a : NaturalSpace) (s : SpinSpace) :
    tensorSplitting (a ⊗ₜ[ℝ] s) =
      (a ⊗ₜ[ℝ] (SpinActions.spinRestriction s).1,
        a ⊗ₜ[ℝ] (SpinActions.spinRestriction s).2) := rfl

/-- The three pieces of `B_E`, with `wPlus = v+u`, `wMinus = v-u`. -/
abbrev ESpace := offDiagonalSpace × (plusSpace × minusSpace)

/-- The three pieces of `B_0`, in source order. -/
abbrev ZeroSpace := oddSpace × (TensorTwo × TensorThree)

/-- Exactly `B_R ⊕ B_E ⊕ B_0`. -/
abbrev NonOctadSpace := RSpace × (ESpace × ZeroSpace)

private abbrev ShortProduct := octadSpace × (oddSpace × (plusSpace × minusSpace))

private instance summandFintype : Fintype Summand :=
  ⟨{.octad, .odd, .plus, .minus}, by intro i; cases i <;> simp⟩

private def shortPiProduct : (∀ i : Summand, summandSpace i) ≃ₗ[ℝ] ShortProduct where
  toFun a := (a .octad, a .odd, a .plus, a .minus)
  invFun a
    | .octad => a.1
    | .odd => a.2.1
    | .plus => a.2.2.1
    | .minus => a.2.2.2
  left_inv _ := by funext i; cases i <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def shortProductEquiv : ShortProduct ≃ₗ[ℝ] Space :=
  shortPiProduct.symm.trans
    ((DirectSum.linearEquivFunOnFintype ℝ Summand (fun i => summandSpace i)).symm.trans
      shortSpace_sumEquiv)

private theorem shortProductEquiv_apply (a : ShortProduct) :
    shortProductEquiv a = a.1.val + a.2.1.val + a.2.2.1.val + a.2.2.2.val := by
  have h : (DirectSum.linearEquivFunOnFintype ℝ Summand (fun i => summandSpace i)).symm
      (shortPiProduct.symm a) =
      DirectSum.lof ℝ Summand (fun i => summandSpace i) .octad a.1 +
      DirectSum.lof ℝ Summand (fun i => summandSpace i) .odd a.2.1 +
      DirectSum.lof ℝ Summand (fun i => summandSpace i) .plus a.2.2.1 +
      DirectSum.lof ℝ Summand (fun i => summandSpace i) .minus a.2.2.2 := by
    apply (DirectSum.linearEquivFunOnFintype ℝ Summand (fun i => summandSpace i)).injective
    simp only [LinearEquiv.apply_symm_apply, map_add, DirectSum.linearEquivFunOnFintype_lof]
    funext i
    cases i <;> simp [shortPiProduct]
  change shortSpace_sumEquiv
    ((DirectSum.linearEquivFunOnFintype ℝ Summand (fun i => summandSpace i)).symm
      (shortPiProduct.symm a)) = _
  rw [h]
  simp only [map_add, shortSpace_sumEquiv_lof]

private def coordinateShuffle : (octadSpace × NonOctadSpace) ≃ₗ[ℝ]
    (TensorTwo × TensorThree) × (ShortProduct × (RSpace × offDiagonalSpace)) where
  toFun a := (a.2.2.2.2, ((a.1, a.2.2.2.1, a.2.2.1.2), (a.2.1, a.2.2.1.1)))
  invFun a := (a.2.1.1, (a.2.2.1, ((a.2.2.2, a.2.1.2.2), (a.2.1.2.1, a.1))))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Addition of the literal octad and non-octad coordinates is a linear isomorphism. -/
def griessSplitting : (octadSpace × NonOctadSpace) ≃ₗ[ℝ] GriessSpace :=
  coordinateShuffle.trans
    (tensorSplitting.symm.prodCongr (shortProductEquiv.prodCongr symmetricSplitting.symm))

/-- The existing octad span included in the fixed Griess space. -/
@[expose] def octadInclusion : octadSpace →ₗ[ℝ] GriessSpace :=
  (shortInclusion sourceLatticeComparison).comp octadSpace.subtype

/-- The diagonal symmetric inclusion. -/
@[expose] def rInclusion : RSpace →ₗ[ℝ] GriessSpace :=
  (symmetricInclusion sourceLatticeComparison).comp diagonal

/-- Off-diagonal matrices and the literal `wPlus` and `wMinus` spans. -/
@[expose] def eInclusion : ESpace →ₗ[ℝ] GriessSpace :=
  ((symmetricInclusion sourceLatticeComparison).comp offDiagonalSpace.subtype).coprod
    ((shortInclusion sourceLatticeComparison).comp (plusSpace.subtype.coprod minusSpace.subtype))

/-- The odd short span and both natural--half-spin tensor spans. -/
@[expose] def zeroInclusion : ZeroSpace →ₗ[ℝ] GriessSpace :=
  ((shortInclusion sourceLatticeComparison).comp oddSpace.subtype).coprod
    ((minusInclusion sourceLatticeComparison).comp tensorSplitting.symm.toLinearMap)

/-- The sum of precisely the three non-octad source inclusions. -/
@[expose] def nonOctadInclusion : NonOctadSpace →ₗ[ℝ] GriessSpace :=
  rInclusion.coprod (eInclusion.coprod zeroInclusion)

@[simp] theorem octadInclusion_apply (a : octadSpace) :
    octadInclusion a = (0, a.val, 0) := rfl

@[simp] theorem rInclusion_apply (a : RSpace) :
    rInclusion a = (0, 0, diagonal a) := rfl

@[simp] theorem eInclusion_apply (a : ESpace) :
    eInclusion a = (0, a.2.1.val + a.2.2.val, a.1.val) := by
  simp [eInclusion, symmetricInclusion, shortInclusion, LinearMap.coprod_apply]

@[simp] theorem zeroInclusion_apply (a : ZeroSpace) :
    zeroInclusion a = (tensorSplitting.symm a.2, a.1.val, 0) := by
  simp [zeroInclusion, minusInclusion, shortInclusion, LinearMap.coprod_apply]

@[simp] theorem nonOctadInclusion_apply (a : NonOctadSpace) :
    nonOctadInclusion a = rInclusion a.1 + eInclusion a.2.1 + zeroInclusion a.2.2 := by
  simp [nonOctadInclusion, LinearMap.coprod_apply, add_assoc]

/-- The comparison is addition in the existing ambient space. -/
theorem griessSplitting_apply (z : octadSpace) (a : NonOctadSpace) :
    griessSplitting (z,a) = octadInclusion z + nonOctadInclusion a := by
  change (tensorSplitting.symm a.2.2.2,
    shortProductEquiv (z, a.2.2.1, a.2.1.2), diagonal a.1 + a.2.1.1.val) = _
  rw [shortProductEquiv_apply]
  simp only [octadInclusion_apply, nonOctadInclusion_apply, rInclusion_apply,
    eInclusion_apply, zeroInclusion_apply, Prod.mk_add_mk, zero_add, add_zero]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · abel
    · rfl

/-- The included octad and non-octad spaces are complementary submodules. -/
theorem octad_nonOctad_isCompl : IsCompl octadInclusion.range nonOctadInclusion.range := by
  have hl : griessSplitting.toLinearMap.comp (LinearMap.inl ℝ octadSpace NonOctadSpace) =
      octadInclusion := by
    apply LinearMap.ext
    intro z
    change griessSplitting (z,0) = _
    rw [griessSplitting_apply, map_zero, add_zero]
  have hr : griessSplitting.toLinearMap.comp (LinearMap.inr ℝ octadSpace NonOctadSpace) =
      nonOctadInclusion := by
    apply LinearMap.ext
    intro a
    change griessSplitting (0,a) = _
    rw [griessSplitting_apply, map_zero, zero_add]
  rw [← hl, ← hr, LinearMap.range_comp, LinearMap.range_comp]
  exact (Submodule.orderIsoMapComap griessSplitting).isCompl_iff.mp
    LinearMap.isCompl_range_inl_inr

theorem octadInclusion_injective : Function.Injective octadInclusion := by
  intro x y h
  exact Subtype.ext (congrArg (fun a : GriessSpace => a.2.1) h)

theorem nonOctadInclusion_injective : Function.Injective nonOctadInclusion := by
  intro x y h
  have h' : griessSplitting (0,x) = griessSplitting (0,y) := by
    simpa [griessSplitting_apply] using h
  exact congrArg Prod.snd (griessSplitting.injective h')

theorem rInclusion_injective : Function.Injective rInclusion := by
  intro x y h
  have h' := congrArg (fun a : GriessSpace => diagonalEntries a.2.2) h
  simpa using h'

theorem eInclusion_injective : Function.Injective eInclusion := by
  intro x y h
  have h' : nonOctadInclusion (0,x,0) = nonOctadInclusion (0,y,0) := by simpa using h
  exact congrArg (fun a : NonOctadSpace => a.2.1) (nonOctadInclusion_injective h')

theorem zeroInclusion_injective : Function.Injective zeroInclusion := by
  intro x y h
  have h' : nonOctadInclusion (0,0,x) = nonOctadInclusion (0,0,y) := by simpa using h
  exact congrArg (fun a : NonOctadSpace => a.2.2) (nonOctadInclusion_injective h')

end Sporadic.Monster.Construction.NMonomial
