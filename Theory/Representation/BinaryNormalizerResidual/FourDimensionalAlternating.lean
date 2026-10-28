module
public import Theory.Representation.BinaryNormalizerResidual
public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer
public import Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings
public import Theory.Representation.SymplecticNatural
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary

/-!
# Normalizer residuals for alternating binary four-spaces

A faithful four-dimensional binary action of A₇ has self-normalizing image.
For A₆, the actual GL₄(2) ≃ A₈ comparison bounds the full linear normalizer
by 720. Its image has order 360, so the normalizer quotient has order one
or two. Its two-residual therefore lies in the original action image.

The actor-marked forms apply to every faithful four-dimensional action;
no deleted-permutation marking is inferred from the abstract group. The
last theorem applies the A₆ result to the exact derived symplectic natural
action, using the actual Sp₄(2)′ ≃ A₆ equivalence.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript of 1 March 2004, 13.7.6, printed p.940.
The exceptional linear comparison retains its ATLAS attribution through
`Theory.LinearAlgebra.BinaryFourAlternatingEight`.
-/

public section
namespace Representation.BinaryNormalizerResidual
open Subgroup BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem alternatingSix_residual
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4) :
    (pResidual 2 (linearNormalizer ρ)).map (linearNormalizer ρ).subtype ≤ actionImage ρ := by
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).trans
    (BinaryFourAlternatingEight.linearEquivAlternatingEight hd)
  let f := e.toMonoidHom.comp ρ.asGroupHom
  have hi : Function.Injective ρ.asGroupHom := fun _ _ h => hf (congrArg Units.val h)
  have hf' : Function.Injective f := e.injective.comp hi
  have hnmap : (linearNormalizer ρ).map e.toMonoidHom = normalizer (f.range : Set _) := by
    rw [linearNormalizer, map_equiv_normalizer_eq, MonoidHom.range_comp]
    rfl
  have hn := Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.normalizer_card_le f hf'
  rw [← hnmap, card_map_of_injective e.injective] at hn
  let N := linearNormalizer ρ
  let A := (actionImage ρ).subgroupOf N
  have hAN : actionImage ρ ≤ N := (actionImage ρ).le_normalizer
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer hAN).mpr le_rfl
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  have hA : Nat.card A = 360 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv]
    rw [actionImage, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hq : Nat.card (N ⧸ A) ≤ 2 := by
    have hc := card_eq_card_quotient_mul_card_subgroup A
    rw [hA] at hc
    change Nat.card N ≤ 720 at hn
    omega
  have hpos : 0 < Nat.card (N ⧸ A) := Nat.card_pos
  have hqd : Nat.card (N ⧸ A) ∣ 2 ^ 1 := by
    have hh : Nat.card (N ⧸ A) = 1 ∨ Nat.card (N ⧸ A) = 2 := by omega
    rcases hh with hh | hh <;> simp [hh]
  have hp : IsPGroup 2 (N ⧸ A) := IsPGroup.of_card_dvd_pow hqd
  have hr : pResidual 2 N ≤ A := sInf_le ⟨inferInstance, hp⟩
  exact (map_mono hr).trans (map_subgroupOf_eq_of_le hAN).le

/-- Faithful binary four-dimensional actions of A₇ have their linear
normalizer two-residual inside their action image. -/
theorem alternatingSeven_four_residual_le
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (e : G ≃* alternatingGroup (Fin 7)) (hd : Module.finrank (ZMod 2) V = 4) :
    (pResidual 2 (linearNormalizer ρ)).map (linearNormalizer ρ).subtype ≤ actionImage ρ := by
  let σ := ρ.comp e.symm.toMonoidHom
  have hσ : Function.Injective σ := hf.comp e.symm.injective
  apply residual_le_of_equiv ρ σ e (LinearEquiv.refl (ZMod 2) V) _
    (residual_le_of_normalizer_eq σ
      (BinaryAlternatingSevenControl.actionImage_self_normalizing σ hσ hd))
  intro g v
  change ρ g v = ρ (e.symm (e g)) v
  rw [e.symm_apply_apply]

/-- Faithful binary four-dimensional actions of A₆ have their linear
normalizer two-residual inside their action image. -/
theorem alternatingSix_four_residual_le
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (e : G ≃* alternatingGroup (Fin 6)) (hd : Module.finrank (ZMod 2) V = 4) :
    (pResidual 2 (linearNormalizer ρ)).map (linearNormalizer ρ).subtype ≤ actionImage ρ := by
  let σ := ρ.comp e.symm.toMonoidHom
  have hσ : Function.Injective σ := hf.comp e.symm.injective
  apply residual_le_of_equiv ρ σ e (LinearEquiv.refl (ZMod 2) V) _
    (alternatingSix_residual σ hσ hd)
  intro g v
  change ρ g v = ρ (e.symm (e g)) v
  rw [e.symm_apply_apply]

/-- The exact derived symplectic natural action has the same residual bound. -/
theorem symplecticDerived_two_residual_le :
    (pResidual 2 (linearNormalizer (symplecticDerivedNatural (k := ZMod 2) 2))).map
      (linearNormalizer (symplecticDerivedNatural (k := ZMod 2) 2)).subtype ≤
        actionImage (symplecticDerivedNatural (k := ZMod 2) 2) := by
  apply alternatingSix_four_residual_le (symplecticDerivedNatural 2) _
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp))
  · simp
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact Matrix.mulVec_injective (congrArg DFunLike.coe hab)
end Representation.BinaryNormalizerResidual
