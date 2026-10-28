module
public import CFSG.Quasithin.ChapterE.Section02.TwoConjugateCovers.LinearTwo
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearTwo
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.ActorDimension
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# The original linear-two cubic actor bound

The actual V-image lies in a defining-characteristic Sylow subgroup,
whose order is the field order. The genuine core identification and
chief-factor degree theorem give the matching lower bound for A/Z.
Kernel counting therefore proves the source cubic estimate, including
its application to the literal Aut_X(V) action.

Source: Aschbacher–Smith E.2.13(2–4), printed pp.224–225. The only family
marking is the original X/J isomorphism; there is no remaining core
identification, module-degree, or ratio hypothesis.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem actor_rank_ge_linear_two_star (h : Hypotheses T V M g)
    (hproper : V ≠ ⊤) (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ J M) ≃* SL(2,F)) :
    m ≤ Nat.log 2 ((Z V g).relIndex (A V M g)) := by
  exact h.actor_rank_ge_linear_two hproper hfit m (by omega) hcard
    (h.quotient_core_equiv_linear_two m hm hcard ξ)

omit [Finite X] in
theorem star_card_le_linear_two (h : Hypotheses T V M g)
    (m : ℕ) (hcard : Nat.card F = 2^m) (ξ : (X ⧸ J M) ≃* SL(2,F)) :
    Nat.card (V.map (QuotientGroup.mk' (J M))) ≤ 2^m := by
  let := h.elementary
  let q := QuotientGroup.mk' (J M)
  let E := (V.map q).map ξ.toMonoidHom
  have hp : IsPGroup 2 E := ((IsElementaryAbelian.isPGroup 2 V).map q).map ξ.toMonoidHom
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hc := Nat.card_le_card_of_injective (inclusion hS) (inclusion_injective hS)
  have hSsize : Nat.card S = 2^m := by
    rw [← Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S).toEquiv]
    exact (Nat.card_congr Multiplicative.toAdd).trans hcard
  change Nat.card ((V.map q).map ξ.toMonoidHom) ≤ Nat.card S at hc
  rw [card_map_of_injective ξ.injective,hSsize] at hc
  exact hc

theorem linear_two_cubic_actor
    {D Q : Type*} [Group D] [Finite D] [Group Q] [Finite Q]
    [IsElementaryAbelian 2 Q]
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ J M) ≃* SL(2,F))
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹) :
    f.ker = (Z V g).subgroupOf (A V M g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range ≤ 2 * rank f.range ∧ cubicRatio ρ ≤ 2 := by
  apply h.cubic_actor_of_star_dimension hproper hfit e ρ hρ f ha m
  · exact h.star_card_le_linear_two m hcard ξ
  · exact h.actor_rank_ge_linear_two_star hproper hfit m hm hcard ξ
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses

namespace CFSG.Quasithin.ChapterE.DihedralCubic
open TwoConjugate
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem canonical_cubicRatio_le_two_linear_two
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ J M) ≃* SL(2,F)) :
    letI := h.elementary
    cubicRatio (canonicalAction (normalizer (V : Set X)) V le_rfl) ≤ 2 := by
  let := h.elementary
  let := centralizer_normal (normalizer (V : Set X)) V le_rfl
  have hr := h.linear_two_cubic_actor hproper hfit m hm hcard ξ (MulEquiv.refl V)
    (canonicalAction (normalizer (V : Set X)) V le_rfl)
    (representation_injective _ V le_rfl _ (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)) (localActor h)
    (fun a v => representation_apply _ V le_rfl _ (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) _ _)
  exact hr.2.2.2.2
end CFSG.Quasithin.ChapterE.DihedralCubic
