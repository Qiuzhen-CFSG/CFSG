module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.Inputs
public import Theory.Representation.Triality.InnerDisplacement.ScalarDescent
public import Theory.Representation.Triality.InnerDisplacement.CoverReduction
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Scalar and central-cover reduction for the inner triality estimate

The component's action may be irreducible without being absolutely
irreducible. Passing to its commuting endomorphism field preserves the
binary dimension of the range of the same involution displacement operator.
If the component center is a two-group, faithfulness in characteristic two
kills it. The actual central-quotient model witness then supplies an
isomorphism of the component with `Standard.BinaryCarrier n hn`.

These reductions retain arbitrary coefficient-field universes, all positive
exponents, and the literal action on the original module. The absolute
model displacement estimate and the prime-to-two cover calculation remain
explicit premises. This module does not yet assert the unconditional
`ComponentInvolutionBound`.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, §8 and
Lemma 8.6, internal pp.53 and 56--57; see `EvenTwisted/Source.md`.
-/

public section

open Representation

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality
universe u v

/-- Apply the exact scalar descent to the published component contract. -/
theorem componentInvolutionBound_of_absoluteBound {R : Type u} [Group R] {n : ℕ}
    (h : _root_.Triality.InnerDisplacement.AbsoluteBound.{u, v} R (5 * n)) :
    ComponentInvolutionBound.{u, v} R n := by
  intro E W _ _ _ _ _ _ _ τ hi hf t ht ht2
  let := hi
  exact _root_.Triality.InnerDisplacement.of_absoluteBound h τ hf t ht ht2

/-- The two remaining source inputs imply the full component contract,
including nonabsolute irreducible actions of every central cover. -/
theorem componentInvolutionBound_of_twoGroup_center {R : Type u} [Group R]
    (n : ℕ) (hn : 0 < n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R))
    (hc : IsPGroup 2 (Subgroup.center R))
    (h : _root_.Triality.InnerDisplacement.AbsoluteBound.{0, v}
      (_root_.Triality.Standard.BinaryCarrier n hn) (5 * n)) :
    ComponentInvolutionBound.{u, v} R n := by
  intro E W _ _ _ _ _ _ _ τ hi hf t ht ht2
  let := hi
  have hz := _root_.Triality.InnerDisplacement.center_eq_bot_of_twoGroup τ hf hc
  obtain ⟨e⟩ := (_root_.Triality.Standard.isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  let c : R ≃* _root_.Triality.Standard.BinaryCarrier n hn :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans e
  let σ := τ.comp c.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff _ c.symm.surjective τ).mpr hi
  have ht' : c t ≠ 1 := fun he => ht (c.injective (he.trans c.map_one.symm))
  have ht2' : (c t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hd := _root_.Triality.InnerDisplacement.of_absoluteBound h σ
    (hf.comp c.symm.injective) (c t) ht' ht2'
  have heq : σ (c t) = τ t := congrArg τ (c.symm_apply_apply t)
  have hr := congrArg (fun f : Module.End E W =>
    Module.finrank E (LinearMap.range (f - LinearMap.id))) heq
  exact lt_of_lt_of_eq hd (congrArg (fun d : ℕ => Module.finrank (ZMod 2) E * d) hr)
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality


