module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Models
public import Theory.Representation.HermitianTensorThree.Marked
public import Theory.GroupTheory.SolvableResidual

/-!
# The binary image and source overgroups of the Hermitian tensor

Restriction of scalars gives an explicit equivalence of the fixed-field and
binary images. The source equation L = M∞ places M in the literal binary
normalizer by relative normality of the residual. The marked field swap
normalizes this image and lies outside it. Fixing its six-dimensional fixed
space pointwise forces an element of the image to be the identity.

`NormalizerCoverage` names a separate, unproved contract for the remaining
normalizer theorem: every normalizer element is matrix congruence followed
by a coefficient automorphism. The matrix is allowed to be in GL₃, retaining
the inner-diagonal extension. No theorem here assumes this coverage.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Chapter H
standing hypotheses on p.377 and H.4.2 / H.4.4(6), printed pp.380–381.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter
variable (n : ℕ) [NeZero n]

/-- Restricting the scalars of a linear equivalence is injective. -/
theorem binaryEquiv_injective : Function.Injective (binaryEquiv n) := by
  intro e f h
  apply LinearEquiv.ext
  intro X
  exact congrArg (fun a : Space n ≃ₗ[ZMod 2] Space n => a X) h

/-- The same image element, acting on the binary vector space. -/
def imageToBinaryImage : Image n →* binaryImage n where
  toFun g := ⟨binaryEquiv n g.val, by
    obtain ⟨a, ha⟩ := g.property
    exact ⟨a, congrArg (binaryEquiv n) ha⟩⟩
  map_one' := Subtype.ext (binaryEquivHom n).map_one
  map_mul' g h := Subtype.ext ((binaryEquivHom n).map_mul g.val h.val)

def binaryImageEquiv : Image n ≃* binaryImage n :=
  MulEquiv.ofBijective (imageToBinaryImage n) ⟨by
    intro g h he
    apply Subtype.ext
    exact binaryEquiv_injective n (congrArg Subtype.val he), by
    intro g
    obtain ⟨a, ha⟩ := g.property
    exact ⟨toImage n a, Subtype.ext ha⟩⟩

theorem binaryImageEquiv_apply (g : Image n) (X : Space n) :
    (binaryImageEquiv n g).val X = imageAction n g X := rfl

theorem binaryImageEquiv_toImage (g : Cover n) :
    (binaryImageEquiv n (toImage n g)).val = binaryActionHom n g := rfl

/-- The literal source hypothesis L = M∞, using the binary image for L. -/
def SourceOvergroup (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) : Prop :=
  (Subgroup.solvableResidual M).map M.subtype = binaryImage n

theorem sourceOvergroup_contains_image (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (hM : SourceOvergroup n M) : binaryImage n ≤ M := by
  rw [← hM]
  exact Subgroup.map_subtype_le _

/-- Relative normality of the residual places the source overgroup in the normalizer. -/
theorem sourceOvergroup_le_normalizer (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (hM : SourceOvergroup n M) : M ≤ binaryNormalizer n := by
  change M ≤ Subgroup.normalizer (binaryImage n : Set (Space n ≃ₗ[ZMod 2] Space n))
  rw [← hM]
  have h := (Subgroup.solvableResidual M).le_normalizer_map M.subtype
  simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using h

/-- Normalizer coverage must retain all inner-diagonal matrices and coefficient automorphisms. -/
def HasCongruenceExpression (e : Space n ≃ₗ[ZMod 2] Space n) : Prop :=
  ∃ (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (τ : E n ≃+* E n),
    ∀ X : Space n, (e X).val = (g : Mat n) * X.val.map τ * adjoint n (g : Mat n)

/-- An explicit pending normalizer theorem, separate from the source overgroup hypothesis. -/
def NormalizerCoverage : Prop :=
  ∀ e ∈ binaryNormalizer n, HasCongruenceExpression n e

theorem fieldSwapBinary_conj (g : Cover n) :
    fieldSwapBinary n * binaryActionHom n g * (fieldSwapBinary n)⁻¹ =
      binaryActionHom n (Matrix.SpecialLinearGroup.map (sigma n).toRingHom g) := by
  apply LinearEquiv.ext
  intro X
  exact fieldSwap_action n g (fieldSwap n X)

theorem fieldSwapBinary_mem_normalizer : fieldSwapBinary n ∈ binaryNormalizer n := by
  change fieldSwapBinary n ∈ Subgroup.normalizer (binaryImage n : Set _)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨Matrix.SpecialLinearGroup.map (sigma n).toRingHom g, (fieldSwapBinary_conj n g).symm⟩
  · rintro _ ⟨g, rfl⟩
    let gs := Matrix.SpecialLinearGroup.map (sigma n).toRingHom g
    refine ⟨binaryActionHom n gs, ⟨gs, rfl⟩, ?_⟩
    change fieldSwapBinary n * binaryActionHom n gs * (fieldSwapBinary n)⁻¹ = _
    rw [fieldSwapBinary_conj]
    congr 1
    apply Subtype.ext
    ext i j
    exact sigma_involutive n (g.val i j)

/-- Within the faithful image, fixing the field involution's fixed space forces identity. -/
theorem image_eq_one_of_fixes_fieldFixed (g : Image n)
    (hg : ∀ X : fieldFixed n, imageAction n g X.val = X.val) : g = 1 := by
  obtain ⟨a, ha⟩ := g.property
  have hfix : ∀ X : Space n, X.val.transpose = X.val →
      a.val * X.val * adjoint n a.val = X.val := by
    intro X hX
    have hmem : X ∈ fieldFixed n := (mem_fieldFixed n X).mpr (Subtype.ext hX)
    have he := congrArg Subtype.val (hg ⟨X, hmem⟩)
    change (g.val X).val = X.val at he
    rw [← ha] at he
    exact he
  obtain ⟨c, he, hc⟩ := eq_scalar_of_fixes_symmetric n a.val hfix
  apply Subtype.ext
  rw [← ha]
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  change a.val * X.val * adjoint n a.val = X.val
  rw [he]
  exact scalar_action n c hc X.val

theorem fieldSwapBinary_not_mem_image : fieldSwapBinary n ∉ binaryImage n := by
  rintro ⟨g, hg⟩
  have hfix : ∀ X : fieldFixed n, imageAction n (toImage n g) X.val = X.val := by
    intro X
    have he := congrArg (fun e : Space n ≃ₗ[ZMod 2] Space n => e X.val) hg
    exact he.trans ((mem_fieldFixed n X.val).mp X.property)
  have hone := congrArg Subtype.val (image_eq_one_of_fixes_fieldFixed n (toImage n g) hfix)
  have hswap : fieldSwap n = 1 := by
    apply LinearEquiv.ext
    intro X
    have he := congrArg (fun e : Space n ≃ₗ[ZMod 2] Space n => e X) hg
    exact he.symm.trans (congrArg (fun e : Space n ≃ₗ[F n] Space n => e X) hone)
  exact fieldSwap_ne_one n hswap
end Representation.HermitianTensorThree.ImageOuter
