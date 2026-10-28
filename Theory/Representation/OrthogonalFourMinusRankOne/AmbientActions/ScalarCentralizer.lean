module

public import Theory.Representation.OrthogonalFourMinusRankOne.RootActors
public import Theory.Representation.OrthogonalFourMinusBinaryIrreducibility

/-!
# Scalar centralizers and rigidity of the Hermitian field involution

An additive endomorphism commuting with SL₂ preserves the fixed K-line of the
full upper root group. Its value at one nonzero vector therefore agrees with
a K-scalar. The kernel of their difference contains that vector and is invariant;
binary irreducibility forces equality everywhere. For an involutive lift of the
quadratic field automorphism, composition with canonical conjugation centralizes
SL₂. Canonical conjugation is K-linear, so squaring forces the scalar to be one.

This proves the vector-space rigidity used for the outer transvection in
Aschbacher–Smith, K.3.1.2, printed p.454 of `refs/quasithin.pdf`, combined
manuscript of 1 March 2004. The proof includes every positive field parameter.
-/

open Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.HermitianEquiv
open Representation.OrthogonalFourMinus.RankOne

@[expose] public noncomputable section
namespace Representation.OrthogonalFourMinus.RankOne.AmbientActions
variable (s : ℕ) [NeZero s]

/-- Every additive endomorphism commuting with the Hermitian layer is a fixed-field scalar. -/
theorem commuting_addHom_eq_scalar (f : Space s →+ Space s)
    (hf : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) (Field s)) (X : Space s),
      f (action s A X) = action s A (f X)) :
    ∃ c : fixedField s, ∀ X, f X = c • X := by
  let e : Representation.invariants
      ((action s).comp (Matrix.SpecialLinearGroup.upperUnipotent (Field s)).subtype) :=
    (upperFixedEquivK s).symm 1
  have he : e.val ≠ 0 := by
    intro hz
    have hz' : e = 0 := Subtype.ext hz
    have h1 := congrArg (upperFixedEquivK s) hz'
    simp [e] at h1
  have hfe : f e.val ∈ Representation.invariants
      ((action s).comp (Matrix.SpecialLinearGroup.upperUnipotent (Field s)).subtype) := by
    intro g
    change action s g.val (f e.val) = f e.val
    rw [← hf]
    exact congrArg f (e.property g)
  let c : fixedField s := upperFixedEquivK s ⟨f e.val, hfe⟩
  have hce : f e.val = c • e.val := by
    have h : (⟨f e.val, hfe⟩ : Representation.invariants
        ((action s).comp (Matrix.SpecialLinearGroup.upperUnipotent (Field s)).subtype)) = c • e := by
      apply (upperFixedEquivK s).injective
      simp [c, e]
    exact congrArg Subtype.val h
  let W : AddSubgroup (Space s) := (f - (c • (LinearMap.id : Space s →ₗ[fixedField s] Space s)).toAddMonoidHom).ker
  have hW (X : Space s) : X ∈ W ↔ f X = c • X := by
    change f X - c • X = 0 ↔ _
    exact sub_eq_zero
  have hinv (A : Matrix.SpecialLinearGroup (Fin 2) (Field s)) (X : Space s)
      (hX : X ∈ W) : action s A X ∈ W := by
    rw [hW] at hX ⊢
    rw [hf, hX, map_smul]
  rcases BinaryIrreducibility.invariant_addSubgroup_eq_bot_or_top s W hinv with hbot | htop
  · have hm : e.val ∈ W := (hW _).mpr hce
    rw [hbot, AddSubgroup.mem_bot] at hm
    exact (he hm).elim
  · exact ⟨c, fun X => (hW X).mp (htop ▸ AddSubgroup.mem_top X)⟩

/-- The canonical conjugation intertwines the literal matrix field automorphism. -/
theorem conjugationLinear_action (A : Matrix.SpecialLinearGroup (Fin 2) (Field s)) (X : Space s) :
    conjugationLinear s (action s A X) =
      action s (Matrix.SpecialLinearGroup.map (conjugation s).toRingHom A)
        (conjugationLinear s X) := by
  exact congrArg (fun g : ClassicalOrthogonal.Minus.Orthogonal (fixedField s)
    (Space s) (form s) => g.val X) (conjugationOrthogonal_mul_action s A)

theorem conjugationLinear_involutive (X : Space s) :
    conjugationLinear s (conjugationLinear s X) = X := by
  apply Subtype.ext
  rfl

/-- An involutive additive lift of the quadratic field automorphism is exactly
canonical conjugation. No scalar-linearity hypothesis on the lift is needed. -/
theorem involutive_field_lift_eq_conjugation (T : Space s →+ Space s) (hT2 : Function.Involutive T)
    (hT : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) (Field s)) (X : Space s),
      T (action s A X) =
        action s (Matrix.SpecialLinearGroup.map (conjugation s).toRingHom A) (T X)) :
    ∀ X, T X = conjugationLinear s X := by
  have hsigma (A : Matrix.SpecialLinearGroup (Fin 2) (Field s)) :
      Matrix.SpecialLinearGroup.map (conjugation s).toRingHom
        (Matrix.SpecialLinearGroup.map (conjugation s).toRingHom A) = A := by
    ext i j
    exact conjugation_involutive s _
  let f := T.comp (conjugationLinear s).toAddMonoidHom
  have hf (A : Matrix.SpecialLinearGroup (Fin 2) (Field s)) (X : Space s) :
      f (action s A X) = action s A (f X) := by
    change T (conjugationLinear s (action s A X)) =
      action s A (T (conjugationLinear s X))
    rw [conjugationLinear_action, hT, hsigma]
  obtain ⟨c, hc⟩ := commuting_addHom_eq_scalar s f hf
  have hTX (X : Space s) : T X = c • conjugationLinear s X := by
    have h := hc (conjugationLinear s X)
    change T (conjugationLinear s (conjugationLinear s X)) =
      c • conjugationLinear s X at h
    rwa [conjugationLinear_involutive] at h
  have hc2 := hT2 (firstDiagonal s)
  rw [hTX, hTX, map_smul, conjugationLinear_involutive, smul_smul] at hc2
  have he : c * c = 1 := by
    apply Subtype.ext
    have he := congrArg (fun X : Space s => X.val 0 0) hc2
    simpa [firstDiagonal, coordinates_symm_val, Subfield.smul_def, smul_eq_mul] using he
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa only [pow_two, one_mul] using he)
  intro X
  simpa only [hc1, one_smul] using hTX X

section Binary
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- Scalar rigidity for the exact binary representation used by marked models. -/
theorem commuting_binaryEnd_eq_scalar (f : Space s →ₗ[ZMod 2] Space s)
    (hf : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) (Field s)) (X : Space s),
      f (Representation.SL2.BinarySmall.hermitian s A X) =
        Representation.SL2.BinarySmall.hermitian s A (f X)) :
    ∃ c : fixedField s, ∀ X, f X = c • X :=
  commuting_addHom_eq_scalar s f.toAddMonoidHom hf
end Binary

end Representation.OrthogonalFourMinus.RankOne.AmbientActions
