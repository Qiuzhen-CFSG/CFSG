module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.SymplecticEquality.Strict
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.SymplecticBinary.Strict

/-!
# Strict original symplectic actor bounds at every field size

The nonbinary natural-module argument and the binary orbit-count argument
cover every positive field exponent. Both preserve the original actor,
source quotient marking and Sylow-center placement. The ambient consumer
uses the same conjugation representation and quotient map supplied by the
original two-conjugate configuration.

Source: the complete symplectic family of Aschbacher–Smith E.2.15,
printed p.228. No TI, degree, module-chart or covering premise is retained.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Theory.SpecificGroups.SymplecticFour
open scoped Matrix MatrixGroups IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}
  {D Q : Type*} [Group D] [Finite D] [Group Q] [Finite Q]
  [IsElementaryAbelian 2 Q]

theorem symplectic_four_cubic_actor_strict_of_positive_exponent
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 0 < m) (hcard : Nat.card F = 2^m)
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
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
  · exact h.symplectic_four_binary_cubic_actor_strict hproper hfit
      (by simpa using hcard) ξ S hVS e ρ hρ f ha
  · exact h.symplectic_four_cubic_actor_strict hproper hfit m hm2 hcard ξ S hVS e ρ hρ f ha
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses

namespace CFSG.Quasithin.ChapterE.DihedralCubic
open TwoConjugate
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem local_cubic_actor_strict_symplectic_four_of_positive_exponent
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 0 < m) (hcard : Nat.card F = 2^m)
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
  apply h.symplectic_four_cubic_actor_strict_of_positive_exponent hproper hfit m hm hcard ξ S hVS
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
theorem ambient_cubic_actor_strict_symplectic_four_of_positive_exponent [IsElementaryAbelian 2 V]
    (hVI : V ≤ I) (hn : U ≤ normalizer (V : Set G))
    (h : Hypotheses R (V.subgroupOf I) N g)
    (hRU : (R : Subgroup I).map I.subtype ≤ U)
    (hproper : V.subgroupOf I ≠ ⊤)
    (hfit : generalizedFitting I = pCore 2 I)
    (m : ℕ) (hm : 0 < m) (hcard : Nat.card F = 2^m)
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
  apply h.symplectic_four_cubic_actor_strict_of_positive_exponent hproper hfit m hm hcard ξ S hVS
    e ρ (representation_injective U V hn q hq hk) f
  intro a v
  apply Subtype.ext
  change ((ρ (q (actorIn h hRU a)) (Additive.ofMul (e v))).toMul : G) =
    ((a : I) : G) * ((v : I) : G) * ((a : I) : G)⁻¹
  rw [representation_apply]
  rfl
end CFSG.Quasithin.ChapterE.DihedralCubic
