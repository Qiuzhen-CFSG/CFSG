module
public import Theory.Representation.SL2NaturalOffenders
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.SL2.BinarySmallModels

/-!
# Offenders in the full normalizer of the natural SL₂ action

The actual natural action embeds SL₂ as a normal subgroup of its full binary
linear normalizer. The intrinsic natural-module offender theorem puts every
binary offender in that same SL₂ image. This preserves the literal action
used by the original Chapter 10 maximum-elementary-subgroup argument.
Source: Aschbacher–Smith B.4.2(1) and 10.2.9, printed pp.86 and 750–751.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2NaturalOffenders
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- Every offender in the full binary normalizer belongs to its natural SL₂ layer. -/
theorem natural_normalizer_offender_le_layer
    (hF : 2 < Nat.card F)
    (A : Subgroup (linearNormalizer (SL2.BinarySmall.natural (K := F))))
    (hA : IsOffender (normalizerRepresentation (SL2.BinarySmall.natural (K := F))) A) :
    A ≤ (actionImage (SL2.BinarySmall.natural (K := F))).subgroupOf
      (linearNormalizer (SL2.BinarySmall.natural (K := F))) := by
  let σ := SL2.BinarySmall.natural (K := F)
  let N := linearNormalizer σ
  let L := (actionImage σ).subgroupOf N
  have hσ : Function.Injective σ := by
    intro x y h
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    exact LinearMap.congr_fun h v
  have hi : Function.Injective σ.asGroupHom := fun _ _ h =>
    hσ (congrArg Units.val h)
  let E : SL(2,F) ≃* actionImage σ := MonoidHom.ofInjective hi
  let e : L ≃* SL(2,F) := (subgroupOfEquivOfLe (actionImage σ).le_normalizer).trans E.symm
  let : L.Normal := normal_subgroupOf_of_le_normalizer (le_refl N)
  have hn : ∀ (g : L) (v : Fin 2 → F), normalizerRepresentation σ (g : N) v =
      Matrix.mulVec (e g).val v := by
    intro g v
    have hh := E.apply_symm_apply ((subgroupOfEquivOfLe (actionImage σ).le_normalizer) g)
    have hc := congrArg (fun x : actionImage σ => (x : (Module.End (ZMod 2) (Fin 2 → F))ˣ).val v) hh
    exact hc.symm
  have hf : Function.Injective (normalizerRepresentation σ) := by
    intro a b h
    apply Subtype.ext
    exact Units.ext h
  let : Finite (Module.End (ZMod 2) (Fin 2 → F)) :=
    Finite.of_injective (fun x : Module.End (ZMod 2) (Fin 2 → F) => (x : (Fin 2 → F) → (Fin 2 → F))) DFunLike.coe_injective
  obtain ⟨P,hP⟩ := exists_sylow hF L e (normalizerRepresentation σ) hf hn hA
  exact hP ▸ map_subtype_le _
end Representation.SL2NaturalOffenders
