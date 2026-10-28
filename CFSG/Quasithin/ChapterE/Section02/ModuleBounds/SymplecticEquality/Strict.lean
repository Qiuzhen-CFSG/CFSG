module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.SymplecticEquality.NaturalLift
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.SymplecticEquality.Actor

/-!
# Strict actor bounds in the nonbinary symplectic source family

A ratio at least two forces the original actor rank to be at most 2m.
The actual P/Z action is consequently a natural symplectic module.
Its nonzero orbit makes every element of P an involution. The fixed
summand B then makes the same original actor an offender, contradicting
the assumed ratio. This proves the strict bound with only the original
Sp₄ source marking and Sylow-center placement. TI is unnecessary here.

The local and ambient consumers retain their literal quotient maps.
Source: Aschbacher–Smith E.2.14(5) and E.2.15, printed pp.227–228.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Theory.SpecificGroups.SymplecticFour
open scoped Matrix MatrixGroups IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}
  {D Q : Type*} [Group D] [Finite D] [Group Q] [Finite Q]
  [IsElementaryAbelian 2 Q]

theorem symplectic_four_cubic_actor_strict
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
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
      m (by omega) hcard ξ S hVS e ρ hρ f ha hratio
    have hP : IsElementaryAbelian 2 (P V M g) := by
      let := h.Z_normal
      let := h.core_geometry.1
      let := h.quotient_direct_sum.1
      let := ZMod.algebra F 2
      obtain ⟨η,eP,heP⟩ := h.symplectic_four_core_natural_of_rank_le hproper hfit
        m hm hcard ξ hrank
      have hF : 3 < Nat.card F := by
        have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hm
        rw [hcard]
        omega
      exact h.P_elementary_of_symplectic_four_natural hproper hfit hF η eP heP
    have hoff := (h.offender_of_P_elementary_and_star_dimension hproper hfit hP
      e ρ hρ f ha (2*m) (star_card_le_symplectic_center m (by omega) hcard ξ S hVS)
      (h.actor_rank_ge_symplectic_four hfit m (by omega) hcard ξ)).1
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

namespace CFSG.Quasithin.ChapterE.DihedralCubic
open TwoConjugate
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem local_cubic_actor_strict_symplectic_four
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ J M) ≃* Sp F)
    (S : Sylow 2 (Sp F))
    (hVS : V.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (J M))) ≤
      (center S).map (S : Subgroup _).subtype) :
    letI := h.elementary
    let ρ := canonicalAction (normalizer (V : Set X)) V le_rfl
    let f := localActor h
    f.ker = (Z V g).subgroupOf (A V M g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range < 2 * rank f.range ∧
      actionRatio ρ f.range < 2 ∧ cubicRatio ρ < 2 := by
  let := h.elementary
  let := centralizer_normal (normalizer (V : Set X)) V le_rfl
  apply h.symplectic_four_cubic_actor_strict hproper hfit m hm hcard ξ S hVS
    (MulEquiv.refl V) _ (representation_injective _ V le_rfl _
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) (localActor h)
  intro a v
  exact representation_apply _ V le_rfl _ (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) _ _
end CFSG.Quasithin.ChapterE.DihedralCubic

namespace CFSG.Quasithin.ChapterE.DihedralCubic
open TwoConjugate Theory.SpecificGroups.SymplecticFour
variable {G D F : Type*} [Group G] [Finite G] [Group D] [Finite D]
  [Field F] [Finite F] [CharP F 2]
  {I U V : Subgroup G} {R : Sylow 2 I} {N : Subgroup I} {g : I}

/-- Strict E.2.15 on the literal ambient normalizer quotient. The original
source subgroup I only places its Sylow in U; it need not normalize V. -/
theorem ambient_cubic_actor_strict_symplectic_four [IsElementaryAbelian 2 V]
    (hVI : V ≤ I) (hn : U ≤ normalizer (V : Set G))
    (h : Hypotheses R (V.subgroupOf I) N g)
    (hRU : (R : Subgroup I).map I.subtype ≤ U)
    (hproper : V.subgroupOf I ≠ ⊤)
    (hfit : generalizedFitting I = pCore 2 I)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (I ⧸ J N) ≃* Sp F)
    (S : Sylow 2 (Sp F))
    (hVS : (V.subgroupOf I).map (ξ.toMonoidHom.comp (QuotientGroup.mk' (J N))) ≤
      (center S).map (S : Subgroup _).subtype)
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (V : Set G)).subgroupOf U) :
    let ρ := representation U V hn q hq hk
    let f := actorMap h hRU q
    f.ker = (Z (V.subgroupOf I) g).subgroupOf (A (V.subgroupOf I) N g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range < 2 * rank f.range ∧
      actionRatio ρ f.range < 2 ∧ cubicRatio ρ < 2 := by
  let e := subgroupOfEquivOfLe hVI
  let ρ := representation U V hn q hq hk
  let f := actorMap h hRU q
  apply h.symplectic_four_cubic_actor_strict hproper hfit m hm hcard ξ S hVS
    e ρ (representation_injective U V hn q hq hk) f
  intro a v
  apply Subtype.ext
  change ((ρ (q (actorIn h hRU a)) (Additive.ofMul (e v))).toMul : G) =
    ((a : I) : G) * ((v : I) : G) * ((a : I) : G)⁻¹
  rw [representation_apply]
  rfl
end CFSG.Quasithin.ChapterE.DihedralCubic
