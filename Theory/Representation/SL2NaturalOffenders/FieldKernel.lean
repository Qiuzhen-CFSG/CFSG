module
public import Theory.Representation.SL2NaturalOffenders.OddDegree

/-!
# The field coefficient of a natural SL₂ normalizer

The literal binary normalizer acts semilinearly on the natural module. Its
coefficient defines a homomorphism to the field automorphism group. A
two-element in its kernel is linear; its determinant is one in characteristic
two, so it belongs to the marked SL₂ image. This works in even field degree
as well, without asserting that the coefficient homomorphism vanishes.

Source: Aschbacher--Smith B.4.2(1), printed p.86; application to the original
rank-one moved kernel in Chapter10, printed pp.741 and750.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2NaturalOffenders
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- The coefficient homomorphism detects every nonlinear two-element of the
literal natural normalizer. Its kernel on two-elements is the original SL₂ layer. -/
theorem exists_natural_normalizer_field_control :
    ∃ φ : linearNormalizer (SL2.BinarySmall.natural (K := F)) →* (F ≃+* F),
      ∀ a, (∃ k : ℕ, a ^ (2 ^ k) = 1) → φ a = 1 →
        a ∈ (actionImage (SL2.BinarySmall.natural (K := F))).subgroupOf
          (linearNormalizer (SL2.BinarySmall.natural (K := F))) := by
  let σ := SL2.BinarySmall.natural (K := F)
  let N := linearNormalizer σ
  let L := (actionImage σ).subgroupOf N
  have hi : Function.Injective σ.asGroupHom := by
    intro x y h
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    exact congrArg (fun f => f.val v) h
  let E : SL(2,F) ≃* actionImage σ := MonoidHom.ofInjective hi
  let e : L ≃* SL(2,F) :=
    (subgroupOfEquivOfLe (actionImage σ).le_normalizer).trans E.symm
  let : L.Normal := normal_subgroupOf_of_le_normalizer (le_refl N)
  have hnat : ∀ (g : L) (v : Fin 2 → F), normalizerRepresentation σ (g : N) v =
      Matrix.mulVec (e g).val v := by
    intro g v
    have hh := E.apply_symm_apply ((subgroupOfEquivOfLe (actionImage σ).le_normalizer) g)
    exact (congrArg (fun x : actionImage σ => x.val.val v) hh).symm
  have hf : Function.Injective (normalizerRepresentation σ) := by
    intro x y h
    exact Subtype.ext (Units.ext h)
  let hsemi := normalizer_semilinear L e (normalizerRepresentation σ) hnat
  refine ⟨fieldAction (normalizerRepresentation σ) hsemi, ?_⟩
  intro a ha hfield
  exact mem_of_linear_two_power_one L e (normalizerRepresentation σ) hf hnat ha
    ((fieldAction_eq_one_iff _ hsemi a).mp hfield)

end Representation.SL2NaturalOffenders
