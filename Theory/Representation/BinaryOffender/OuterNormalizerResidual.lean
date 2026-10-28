module
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.GroupTheory.OuterPGroupSylowSupplement
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
/-!
# A model with trivial commutant and two-group outer automorphisms

The full linear normalizer modulo the component image embeds in the
outer automorphism group when the linear centralizer is trivial.
Consequently its two-residual lies in the original model image. This is
the End=F₂ step used by the binary alternating source families of13.7.6.

Source: Aschbacher--Smith, printed pp.939--940.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {D E : Type*} [Group D] [AddCommGroup E] [Module (ZMod 2) E]
theorem model_residual_le_of_trivial_centralizer_outer_two
    (τ : Representation (ZMod 2) D E) (hτ : Function.Injective τ)
    (hc : centralizer (actionImage τ : Set (Module.End (ZMod 2) E)ˣ) = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer D)) :
    (pResidual 2 (linearNormalizer τ)).map (linearNormalizer τ).subtype ≤ actionImage τ := by
  let N := linearNormalizer τ
  let A := (actionImage τ).subgroupOf N
  have hAN : actionImage τ ≤ N := (actionImage τ).le_normalizer
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer hAN).mpr le_rfl
  have ha : Function.Injective τ.asGroupHom := fun _ _ h => hτ (congrArg Units.val h)
  let e : D ≃* A := (MonoidHom.ofInjective ha).trans
    (subgroupOfEquivOfLe hAN).symm
  have hca : centralizer (A : Set N) = ⊥ := by
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hc]
    intro a ha
    exact congrArg Subtype.val
      (hx (⟨a,hAN ha⟩ : N) (show (⟨a,hAN ha⟩ : N) ∈ A from ha))
  have hq : IsPGroup 2 (N ⧸ A) :=
    (ho.of_equiv (MulAut.outerCongr e)).of_injective (MulAut.outerAction A)
      (MulAut.outerAction_injective A hca)
  have hr : pResidual 2 N ≤ A := sInf_le ⟨inferInstance,hq⟩
  exact (map_mono hr).trans (map_subgroupOf_eq_of_le hAN).le
end Representation.BinaryOffender
