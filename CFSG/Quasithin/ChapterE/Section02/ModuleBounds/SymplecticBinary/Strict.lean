module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.SymplecticBinary.Orbit
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.SymplecticEquality.Actor

/-!
# The strict binary symplectic actor bound

In the equality range the original P/Z has dimension four. Its action
image has order divisible by 45, so its nonzero vectors form one orbit.
The original core P is elementary, making the same actor an offender and
contradicting ratio at least two. Only the actual Sp₄(2) marking and
Sylow-center placement remain; no natural-chart or TI premise is used.

Source: Aschbacher–Smith E.2.15, printed p.228.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Theory.SpecificGroups.SymplecticFour
open scoped Matrix MatrixGroups IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}
  {D Q : Type*} [Group D] [Finite D] [Group Q] [Finite Q]
  [IsElementaryAbelian 2 Q]

theorem symplectic_four_binary_cubic_actor_strict
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (hcard : Nat.card F = 2)
    (ξ : (X ⧸ J M) ≃* Sp F)
    (S : Sylow 2 (Sp F))
    (hVS : V.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (J M))) ≤
      (center S).map (S : Subgroup _).subtype)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹) :
    f.ker = (Z V g).subgroupOf (A V M g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range < 2 * rank f.range ∧
      actionRatio ρ f.range < 2 ∧ cubicRatio ρ < 2 := by
  have hk := h.actor_kernel e ρ hρ f ha
  have he := h.actor_elementary hproper hfit f hk
  have hc := h.actor_cubic e ρ f ha
  have har : actionRatio ρ f.range < 2 := by
    by_contra! hratio
    have hrank := h.symplectic_four_actor_rank_le_of_two_le_ratio hproper hfit
      1 (by decide) (by simpa using hcard) ξ S hVS e ρ hρ f ha hratio
    have hP := h.P_elementary_of_symplectic_four_binary_rank_le hproper hfit
      hcard ξ hrank
    have hoff := (h.offender_of_P_elementary_and_star_dimension hproper hfit hP
      e ρ hρ f ha 2 (star_card_le_symplectic_center 1 (by decide) (by simpa using hcard) ξ S hVS)
      (h.actor_rank_ge_symplectic_four hfit 1 (by decide) (by simpa using hcard) ξ)).1
    have ha1 := (actionRatio_le_nat_iff ρ he 1).mpr (by simpa using hoff.2)
    have : (2 : ℝ≥0∞) ≤ 1 := hratio.trans (by simpa using ha1)
    norm_num at this
  have hb : fixedCodim ρ f.range < 2 * rank f.range := by
    have h0 : (rank f.range : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he.rank_pos)
    have hh := (ENNReal.div_lt_iff (Or.inl h0) (Or.inl (by simp))).mp har
    exact_mod_cast hh
  exact ⟨hk,he,hc,hb,har,
    (iInf_le_of_le f.range (iInf_le_of_le ⟨he,hc⟩ le_rfl)).trans_lt har⟩
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses

