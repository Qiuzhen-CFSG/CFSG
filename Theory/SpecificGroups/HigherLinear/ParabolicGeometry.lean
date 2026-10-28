module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.PGroup

/-!
# Subspace parabolics and their radicals in the actual projective linear group

The special-linear parabolic stabilizes a subspace W of Fⁿ. Its radical
fixes W pointwise and is the identity on Fⁿ/W. The projective subgroups are
their images under the literal quotient SLₙ(F) → SLₙ(F)/Z(SLₙ(F)).
Conjugation proves relative normality; in characteristic two each element
of the radical squares to one.

These definitions support separate proofs of Sylow-overgroup placement and
the projective radical centralizer calculation. Neither assertion is built
into the definitions. Source: GLS III, 2.6.5 and its type-A matrix realization;
Aschbacher–Smith B.1.13, printed p.74 (PDF p.85).
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace Matrix.HigherLinear
variable {n : ℕ} {F : Type*} [Field F]

/-- The canonical central quotient, with no abstract covering-group choice. -/
def projection (n : ℕ) (F : Type*) [Field F] : SL(n,F) →* PSL(n,F) :=
  QuotientGroup.mk' (center SL(n,F))

/-- The full setwise stabilizer of a subspace in the determinant-one group. -/
def parabolicSL (W : Submodule F (Fin n → F)) : Subgroup SL(n,F) where
  carrier := {g | ∀ v, SpecialLinearGroup.toLin' g v ∈ W ↔ v ∈ W}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh v
    simpa only [map_mul, LinearEquiv.mul_apply] using (hg (SpecialLinearGroup.toLin' h v)).trans (hh v)
  inv_mem' := by
    intro g hg v
    simpa using (hg (SpecialLinearGroup.toLin' g⁻¹ v)).symm

/-- The subgroup fixing W and Fⁿ/W pointwise in the determinant-one group. -/
def radicalSL (W : Submodule F (Fin n → F)) : Subgroup SL(n,F) where
  carrier := {g | (∀ w ∈ W, SpecialLinearGroup.toLin' g w = w) ∧
    ∀ v, SpecialLinearGroup.toLin' g v - v ∈ W}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hg, hgd⟩ ⟨hh, hhd⟩
    refine ⟨?_, ?_⟩
    · intro w hw
      simp only [map_mul, LinearEquiv.mul_apply, hh w hw, hg w hw]
    · intro v
      simpa only [sub_add_sub_cancel, map_mul, LinearEquiv.mul_apply] using
        W.add_mem (hgd (SpecialLinearGroup.toLin' h v)) (hhd v)
  inv_mem' := by
    rintro g ⟨hg, hgd⟩
    refine ⟨?_, ?_⟩
    · intro w hw
      apply (SpecialLinearGroup.toLin' g).injective
      simpa using (hg w hw).symm
    · intro v
      simpa using W.neg_mem (hgd (SpecialLinearGroup.toLin' g⁻¹ v))

/-- The actual projective subspace stabilizer. -/
def parabolic (W : Submodule F (Fin n → F)) : Subgroup PSL(n,F) :=
  (parabolicSL W).map (projection n F)

/-- The actual projective block-unipotent radical. -/
def radical (W : Submodule F (Fin n → F)) : Subgroup PSL(n,F) :=
  (radicalSL W).map (projection n F)

theorem radicalSL_le_parabolicSL (W : Submodule F (Fin n → F)) :
    radicalSL W ≤ parabolicSL W := by
  intro g hg v
  constructor
  · intro hv
    simpa using W.sub_mem hv (hg.2 v)
  · intro hv
    simpa only [hg.1 v hv] using hv

theorem parabolicSL_le_normalizer (W : Submodule F (Fin n → F)) :
    parabolicSL W ≤ normalizer (radicalSL W : Set SL(n,F)) := by
  rw [le_set_normalizer_iff]
  intro g hg t ht
  refine ⟨?_, ?_⟩
  · intro w hw
    have hi : SpecialLinearGroup.toLin' g⁻¹ w ∈ W :=
      (parabolicSL W).inv_mem hg w |>.mpr hw
    simp only [map_mul, LinearEquiv.mul_apply]
    rw [ht.1 _ hi]
    simp
  · intro v
    have hd := (hg (SpecialLinearGroup.toLin' t (SpecialLinearGroup.toLin' g⁻¹ v) -
      SpecialLinearGroup.toLin' g⁻¹ v)).mpr (ht.2 (SpecialLinearGroup.toLin' g⁻¹ v))
    simpa only [map_sub, map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply,
      map_mul, LinearEquiv.mul_apply] using hd

theorem radical_le_parabolic (W : Submodule F (Fin n → F)) :
    radical W ≤ parabolic W := map_mono (radicalSL_le_parabolicSL W)

theorem parabolic_le_normalizer (W : Submodule F (Fin n → F)) :
    parabolic W ≤ normalizer (radical W : Set PSL(n,F)) := by
  rw [le_set_normalizer_iff]
  rintro _ ⟨g, hg, rfl⟩ _ ⟨t, ht, rfl⟩
  exact ⟨g * t * g⁻¹, (parabolicSL_le_normalizer W hg t).mp ht, by simp⟩

theorem radicalSL_isPGroup [CharP F 2] (W : Submodule F (Fin n → F)) :
    IsPGroup 2 (radicalSL W) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  change (g : SL(n,F)) ^ 2 = 1
  apply SpecialLinearGroup.toLin'_injective
  rw [map_pow, map_one]
  apply LinearEquiv.ext
  intro v
  have hd := g.property.1 (SpecialLinearGroup.toLin' (g : SL(n,F)) v - v)
    (g.property.2 v)
  simp only [map_sub] at hd
  simp only [pow_two, LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq]
  apply sub_eq_zero.mp
  calc
    SpecialLinearGroup.toLin' (g : SL(n,F)) (SpecialLinearGroup.toLin' (g : SL(n,F)) v) - v =
        (SpecialLinearGroup.toLin' (g : SL(n,F)) (SpecialLinearGroup.toLin' (g : SL(n,F)) v) -
          SpecialLinearGroup.toLin' (g : SL(n,F)) v) +
        (SpecialLinearGroup.toLin' (g : SL(n,F)) v - v) := by abel
    _ = 0 := by
      have htwo : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
      rw [hd, ← two_smul F, htwo, zero_smul]

theorem radical_isPGroup [CharP F 2] (W : Submodule F (Fin n → F)) :
    IsPGroup 2 (radical W) := (radicalSL_isPGroup W).map (projection n F)

end Matrix.HigherLinear
