module
public import Theory.Representation.SL2NaturalOffenders.NaturalNormalizer
public import Theory.Representation.SL2NaturalOffenders.AutomorphismRank

/-!
# Two-rank of the full binary normalizer of natural SL₂

The natural SL₂ image is normal in its binary linear normalizer. Its
centralizer contains no involution, so every elementary two-subgroup embeds
in the actual automorphism group of SL₂. The existing automorphism-rank
bound gives rank at most n over a field of order 2ⁿ.

Source: Aschbacher--Smith 10.2.12, printed p.754, using the natural row
of B.4.2 and the binary automorphism bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2NaturalOffenders

theorem natural_normalizer_rank
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = 2^n) :
    letI : Algebra (ZMod 2) F := ZMod.algebra _ 2
    primeRank 2 (linearNormalizer (SL2.BinarySmall.natural (K := F))) ≤ n := by
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  let σ := SL2.BinarySmall.natural (K := F)
  let N := linearNormalizer σ
  let L := (actionImage σ).subgroupOf N
  let : Finite (Module.End (ZMod 2) (Fin 2 → F)) :=
    Finite.of_injective (fun x : Module.End (ZMod 2) (Fin 2 → F) =>
      (x : (Fin 2 → F) → (Fin 2 → F))) DFunLike.coe_injective
  have hσ : Function.Injective σ := by
    intro x y h
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    exact LinearMap.congr_fun h v
  have hi : Function.Injective σ.asGroupHom := fun _ _ h => hσ (congrArg Units.val h)
  let E : SL(2,F) ≃* actionImage σ := MonoidHom.ofInjective hi
  let e : L ≃* SL(2,F) := (subgroupOfEquivOfLe (actionImage σ).le_normalizer).trans E.symm
  let : L.Normal := normal_subgroupOf_of_le_normalizer (le_refl N)
  have hn' : ∀ (g : L) (v : Fin 2 → F), normalizerRepresentation σ (g : N) v =
      Matrix.mulVec (e g).val v := by
    intro g v
    have hh := E.apply_symm_apply ((subgroupOfEquivOfLe (actionImage σ).le_normalizer) g)
    exact (congrArg (fun x : actionImage σ =>
      (x : (Module.End (ZMod 2) (Fin 2 → F))ˣ).val v) hh).symm
  have hf : Function.Injective (normalizerRepresentation σ) := by
    intro a b h
    apply Subtype.ext
    exact Units.ext h
  exact SL2NaturalOffenders.faithful_extension_rank_le L e (normalizerRepresentation σ) hf hn' hn hcard

end Representation.SL2NaturalOffenders
