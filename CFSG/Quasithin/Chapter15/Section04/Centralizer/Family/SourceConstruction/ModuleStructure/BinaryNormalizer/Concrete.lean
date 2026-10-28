module

public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.Coordinates
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

/-!
# The full normalizer of the concrete independent binary plane rotations

In the given orthogonal sum of anisotropic planes, a vector is nonsingular
exactly when it is nonzero and fixed by some nonidentity rotation. This small
sixteen-vector calculation is preserved by every automorphism normalizing the
rotation group. Such an automorphism is binary-linear and preserves the given
quadratic form. Conversely the rotations are normal in the actual isometry
group. This identifies the FULL automorphism normalizer with that isometry
group and preserves its vector action pointwise.

Source: Aschbacher--Smith, 15.4.12(6)(ii), printed pp.1160--1161, using the
binary plus-four model specified on pp.1121--1122. No enumeration of GL₄(2)
or abstract group-order recognition is used.
-/

@[expose] public section

open Subgroup
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer

abbrev ModelSpace := Multiplicative Space

def rotationAction : RotationCode →* MulAut ModelSpace := vectorAction.comp rotationHom

def modelRotations : Subgroup (MulAut ModelSpace) := rotationAction.range

theorem vectorAction_injective : Function.Injective vectorAction := by
  intro a b hab
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  exact DFunLike.congr_fun hab (Multiplicative.ofAdd w)

theorem rotationAction_injective : Function.Injective rotationAction :=
  vectorAction_injective.comp rotationHom_injective

theorem modelRotations_card : Nat.card modelRotations = 9 := by
  rw [show modelRotations = rotationAction.range from rfl,
    ←Nat.card_congr (MonoidHom.ofInjective rotationAction_injective).toEquiv,
    Nat.card_eq_fintype_card]
  decide

private theorem model_nonsingular_iff (w : ModelSpace) :
    form w.toAdd = 1 ↔ w ≠ 1 ∧
      ∃ a ∈ modelRotations, a ≠ 1 ∧ a w = w := by
  have hc : ∀ w : Space, form w = 1 ↔ w ≠ 0 ∧
      ∃ i : RotationCode, i ≠ 1 ∧ rotation i w = w := by decide +kernel
  rw [hc]
  constructor
  · rintro ⟨hw,i,hi,hf⟩
    refine ⟨hw,rotationAction i,⟨i,rfl⟩,?_,hf⟩
    exact fun hh => hi ((injective_iff_map_eq_one _).mp rotationAction_injective i hh)
  · rintro ⟨hw,a,⟨i,rfl⟩,hi,hf⟩
    exact ⟨hw,i,(fun h => hi (h ▸ map_one rotationAction)),hf⟩

private theorem fixed_witness_transport {E : Type*} [Group E]
    (B : Subgroup (MulAut E)) (n : normalizer (B : Set (MulAut E))) (w : E)
    (hw : ∃ a ∈ B, a ≠ 1 ∧ a w = w) :
    ∃ a ∈ B, a ≠ 1 ∧ a ((n : MulAut E) w) = (n : MulAut E) w := by
  obtain ⟨a,ha,ha1,haw⟩ := hw
  let b := MulAut.conj (n : MulAut E) a
  refine ⟨b,(mem_normalizer_iff.mp n.property a).mp ha,?_,?_⟩
  · exact fun h => ha1 ((MulAut.conj (n : MulAut E)).injective
      (h.trans (map_one _).symm))
  · change ((n : MulAut E) * a * (n : MulAut E)⁻¹) ((n : MulAut E) w) = _
    simp only [MulAut.mul_apply,MulAut.inv_apply_self,haw]

private theorem normalizer_preserves_form (n : normalizer (modelRotations : Set (MulAut ModelSpace)))
    (w : ModelSpace) : form ((n : MulAut ModelSpace) w).toAdd = form w.toAdd := by
  have he : form ((n : MulAut ModelSpace) w).toAdd = 1 ↔ form w.toAdd = 1 := by
    rw [model_nonsingular_iff,model_nonsingular_iff]
    constructor
    · rintro ⟨hn,hf⟩
      have hh := fixed_witness_transport modelRotations n⁻¹ ((n : MulAut ModelSpace) w) hf
      simp only [Subgroup.coe_inv,MulAut.inv_apply_self] at hh
      exact ⟨fun h => hn (by rw [h,map_one]),hh⟩
    · rintro ⟨hw,hf⟩
      exact ⟨fun h => hw ((n : MulAut ModelSpace).injective (h.trans (map_one _).symm)),
        fixed_witness_transport modelRotations n w hf⟩
  exact (show ∀ x y : F, (x = 1 ↔ y = 1) → x = y by decide +kernel) _ _ he

/-- Every automorphism of the additive binary space is binary-linear. -/
def linearOfAut (a : MulAut ModelSpace) : Space ≃ₗ[F] Space :=
  { AddEquiv.toMultiplicative.symm a with
    map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm a) }

/-- The full automorphism normalizer consists of the actual quadratic isometries. -/
theorem model_normalizer_eq : normalizer (modelRotations : Set (MulAut ModelSpace)) =
    vectorAction.range := by
  apply le_antisymm
  · intro a ha
    let n : normalizer (modelRotations : Set (MulAut ModelSpace)) := ⟨a,ha⟩
    let g : OrthogonalFourBinary.IsometryGroup := ⟨linearOfAut a,
      (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup form _).mpr
        (fun w => normalizer_preserves_form n (Multiplicative.ofAdd w))⟩
    exact ⟨g,rfl⟩
  · rintro a ⟨g,rfl⟩
    have hh := rotations.le_normalizer_map vectorAction
    rw [normalizer_eq_top rotations,←MonoidHom.range_eq_map,rotations,←MonoidHom.range_comp] at hh
    exact hh ⟨g,rfl⟩

/-- Identification of the full normalizer, retaining the literal vector action. -/
noncomputable def modelNormalizerEquiv :
    normalizer (modelRotations : Set (MulAut ModelSpace)) ≃* OrthogonalFourBinary.IsometryGroup :=
  (MulEquiv.subgroupCongr model_normalizer_eq).trans
    (MonoidHom.ofInjective vectorAction_injective).symm

theorem modelNormalizerEquiv_apply
    (n : normalizer (modelRotations : Set (MulAut ModelSpace))) (w : ModelSpace) :
    vectorAction (modelNormalizerEquiv n) w = (n : MulAut ModelSpace) w := by
  have he : vectorAction (modelNormalizerEquiv n) = (n : MulAut ModelSpace) := by
    exact congrArg Subtype.val ((MonoidHom.ofInjective vectorAction_injective).apply_symm_apply
      ((MulEquiv.subgroupCongr model_normalizer_eq) n))
  exact DFunLike.congr_fun he w

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer
