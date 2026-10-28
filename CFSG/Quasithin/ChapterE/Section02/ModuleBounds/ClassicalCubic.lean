module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.PrimeActors
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.ActorDimension
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.InnerAction
public import Theory.SpecificGroups.Suzuki.TwoRank

/-!
# Cubic bounds for the original symplectic and Suzuki source families

The original star quotient has size at most 2^(2m) in the symplectic
family, by its prescribed Sylow-center placement, and at most 2^(2m+1)
in the Suzuki family, by the actual two-rank theorem. Primitive-prime
degree bounds on P/Z give the corresponding lower actor ranks. Exact
kernel counting then gives the cubic bound, strictly below two in the
Suzuki case. The final theorems use the literal Aut_X(V) action.

Source: Aschbacher–Smith E.2.13(2–4) and the Suzuki branch of E.2.15,
combined manuscript (1 March 2004), printed pp.224–228. The symplectic
placement is the actual center condition from E.2.4; no abstract degree
or ratio certificate is assumed.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X : Type*} [Group X] [Finite X]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

omit [Finite X] in
theorem star_card_le_symplectic_center
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (m : ℕ) (hm : 0 < m) (hcard : Nat.card F = 2 ^ m)
    (e : (X ⧸ J M) ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hVS : V.map (e.toMonoidHom.comp (QuotientGroup.mk' (J M))) ≤
      (center S).map (S : Subgroup _).subtype) :
    Nat.card (V.map (QuotientGroup.mk' (J M))) ≤ 2 ^ (2 * m) := by
  have hv : (V.map (QuotientGroup.mk' (J M))).map e.toMonoidHom ≤
      (center S).map (S : Subgroup _).subtype := by
    simpa only [Subgroup.map_map] using hVS
  have hc := Nat.card_le_card_of_injective (inclusion hv) (inclusion_injective hv)
  have hcenter : Nat.card ((center S).map
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)).subtype) =
      Nat.card (center S) := card_map_of_injective (S : Subgroup
        (Theory.SpecificGroups.SymplecticFour.Sp F)).subtype_injective
  rw [card_map_of_injective e.injective, hcenter,
    Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.card_sylow_center hcard hm S,
    hcard, ← pow_mul, mul_comm m 2] at hc
  exact hc

omit [Finite X] in
theorem star_card_le_suzuki (h : Hypotheses T V M g)
    (m : ℕ) (hm : 0 < m)
    (e : (X ⧸ J M) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    Nat.card (V.map (QuotientGroup.mk' (J M))) ≤ 2 ^ (2 * m + 1) := by
  let := h.elementary
  let q := QuotientGroup.mk' (J M)
  let E := (V.map q).map e.toMonoidHom
  let : IsElementaryAbelian 2 (V.map q) := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map e.toMonoidHom
  have hc := (primeRank_le_iff_elementary_card_le
    (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)).mp
      (BenderSuzuki.MatrixGroups.suzuki_two_rank m hm).le E inferInstance
  rw [card_map_of_injective e.injective] at hc
  exact hc

open Representation.BinaryOffender
variable {D Q : Type*} [Group D] [Finite D] [Group Q] [Finite Q]
  [IsElementaryAbelian 2 Q]

theorem symplectic_four_cubic_actor
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 0 < m) (hcard : Nat.card F = 2 ^ m)
    (ξ : (X ⧸ J M) ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hVS : V.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (J M))) ≤
      (center S).map (S : Subgroup _).subtype)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹) :
    f.ker = (Z V g).subgroupOf (A V M g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range ≤ 2 * rank f.range ∧ cubicRatio ρ ≤ 2 := by
  apply h.cubic_actor_of_star_dimension hproper hfit e ρ hρ f ha (2*m)
  · exact star_card_le_symplectic_center m hm hcard ξ S hVS
  · exact h.actor_rank_ge_symplectic_four hfit m hm hcard ξ

theorem suzuki_cubic_actor_strict
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 1 ≤ m)
    (ξ : (X ⧸ J M) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹) :
    f.ker = (Z V g).subgroupOf (A V M g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range < 2 * rank f.range ∧
      actionRatio ρ f.range < 2 ∧ cubicRatio ρ < 2 := by
  apply h.cubic_actor_of_strict_star_dimension hproper hfit e ρ hρ f ha (2*m+1)
  · exact h.star_card_le_suzuki m (by omega) ξ
  · have hd := h.actor_rank_ge_suzuki hfit m hm ξ
    omega
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses

namespace CFSG.Quasithin.ChapterE.DihedralCubic
open Subgroup TwoConjugate Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
variable {X : Type*} [Group X] [Finite X]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

/-- E.2.13(3) for the actual Aut_X(V) action in the symplectic family. -/
theorem canonical_cubicRatio_le_two_symplectic_four
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 0 < m) (hcard : Nat.card F = 2 ^ m)
    (ξ : (X ⧸ J M) ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hVS : V.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (J M))) ≤
      (center S).map (S : Subgroup _).subtype) :
    letI := h.elementary
    cubicRatio (canonicalAction (normalizer (V : Set X)) V le_rfl) ≤ 2 := by
  let := h.elementary
  let := centralizer_normal (normalizer (V : Set X)) V le_rfl
  have hr := h.symplectic_four_cubic_actor hproper hfit m hm hcard ξ S hVS
    (MulEquiv.refl V) (canonicalAction (normalizer (V : Set X)) V le_rfl)
    (representation_injective _ V le_rfl _ (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)) (localActor h)
    (fun a v => representation_apply _ V le_rfl _ (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) _ _)
  exact hr.2.2.2.2

/-- E.2.15's strict conclusion for the actual Aut_X(V) action in the Suzuki
family; the source TI condition is unnecessary for this particular case. -/
theorem canonical_cubicRatio_lt_two_suzuki
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 1 ≤ m)
    (ξ : (X ⧸ J M) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    letI := h.elementary
    cubicRatio (canonicalAction (normalizer (V : Set X)) V le_rfl) < 2 := by
  let := h.elementary
  let := centralizer_normal (normalizer (V : Set X)) V le_rfl
  have hr := h.suzuki_cubic_actor_strict hproper hfit m hm ξ (MulEquiv.refl V)
    (canonicalAction (normalizer (V : Set X)) V le_rfl)
    (representation_injective _ V le_rfl _ (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)) (localActor h)
    (fun a v => representation_apply _ V le_rfl _ (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) _ _)
  exact hr.2.2.2.2.2
end CFSG.Quasithin.ChapterE.DihedralCubic
