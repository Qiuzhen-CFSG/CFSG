module
public import Theory.Representation.BinaryOffender.OuterNormalizerResidual

/-!
# Residual bounds from a trivial linear centralizer

Conjugation embeds the normalizer of a self-centralizing subgroup in its
automorphism group. A prime-group outer quotient therefore puts the prime
residual inside that subgroup. For a faithful binary representation, a
trivial linear commutant supplies the required centralizer hypothesis.

Source application: the marked model normalizers in Aschbacher–Smith
13.7.6, printed p.940.
-/

public section
open Subgroup
namespace Representation.BinaryNormalizerResidual

open BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem residual_le_of_trivial_commutant (ρ : Representation (ZMod 2) G V)
    (hi : Function.Injective ρ) (ho : IsPGroup 2 (MulAut.Outer G))
    (hc : ∀ f : V ≃ₗ[ZMod 2] V,
      (∀ g v, f (ρ g v) = ρ g (f v)) → f = LinearEquiv.refl _ _) :
    (pResidual 2 (linearNormalizer ρ)).map (linearNormalizer ρ).subtype ≤ actionImage ρ := by
  apply model_residual_le_of_trivial_centralizer_outer_two ρ hi _ ho
  apply bot_unique
  intro x hx
  have he := hc (LinearMap.GeneralLinearGroup.toLinearEquiv x) (by
    intro g v
    have hh := (mem_centralizer_iff.mp hx (ρ.asGroupHom g) ⟨g, rfl⟩).symm
    exact LinearMap.congr_fun (congrArg Units.val hh) v)
  apply mem_bot.mpr
  apply Units.ext
  exact congrArg LinearEquiv.toLinearMap he
end Representation.BinaryNormalizerResidual
