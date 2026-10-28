module
public import Theory.Representation.RankOne.QuadraticRecognition.SL2Actors
public import Theory.Representation.RankOne.QuadraticRecognition.SL2Sylow
public import Theory.SpecificGroups.SL2.OddFixedVectors
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# Element fixed spaces and odd-order actors in binary SL₂ modules

The displacement map identifies the cyclic fixed quotient with its image.
The faithful SL₂ field-degree estimate gives the individual-element bound.
Complementary Sylow fixed spaces force uniformity and quadratic Sylow
action; root coordinates then express the module as natural copies. A
nonidentity odd-order matrix fixes no nonzero vector in those copies.
The source omega-center is identified with the whole binary SL₂ Sylow,
including field order two. No irreducibility or generation premise is
added to the complementary-fixed-space theorem.

Source: DGS85, *Groups and Graphs*, (5.8)(c), (5.10)(a), (5.11),
pp.109–112, at prime two. CriticalSupporting applies the results to the
literal Z/(Z∩Z(L)) quotient used in the critical-pair argument.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition

/-- DGS (5.8)(c), with the actual displacement image and quotient. -/
theorem card_fixed_quotient_eq_displacement {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (a : G) :
    Nat.card (V ⧸ fixedSpace ρ (zpowers a)) =
      Nat.card (LinearMap.range (ρ a - LinearMap.id)) := by
  have hk : (ρ a - LinearMap.id).ker = fixedSpace ρ (zpowers a) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    exact sub_eq_zero
  rw [←hk]
  exact Nat.card_congr (LinearMap.quotKerEquivRange (ρ a - LinearMap.id)).toEquiv

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
local instance elementFixedSpacesAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- DGS (5.10)(a) at prime two. The estimate actually needs neither the
quadratic actor nor its order-at-least-three hypothesis. -/
theorem sl2_element_fixed_index (ρ : Representation (ZMod 2) SL(2,F) V)
    (hf : Function.Injective ρ) (S : Sylow 2 SL(2,F))
    {t : SL(2,F)} (ht : t ∈ S) (ht1 : t ≠ 1)
    {n : ℕ} (hF : Nat.card F = 2^n) :
    2^n ≤ Nat.card (V ⧸ fixedSpace ρ (zpowers t)) := by
  rw [←hF]
  exact sl2_actor_field_bound ρ hf S (zpowers t) (zpowers_le.mpr ht)
    (fun h => ht1 (by simpa only [h,mem_bot] using mem_zpowers t)) hF

omit [Finite F] [Finite V] in
/-- Nonidentity odd-order actors have zero fixed space on any number of
natural copies, with the same original field and matrix actors. -/
theorem odd_fixed_eq_bot_of_natural_copies
    (ρ : Representation (ZMod 2) SL(2,F) V)
    (hc : SL2SylowFixedRecognition.NaturalCoordinates ρ)
    (a : SL(2,F)) {m : ℕ} (hm : Odd m) (ha : a^m=1) (ha1 : a≠1) :
    fixedSpace ρ (zpowers a) = ⊥ := by
  obtain ⟨k,E,he⟩ := hc
  apply bot_unique
  intro v hv
  rw [Submodule.mem_bot]
  apply E.injective
  ext i j
  have hv' := (mem_fixedSpace_zpowers_iff ρ a v).mp hv
  have hh : Matrix.mulVec a.val (E v i) = E v i := by rw [←he,hv']
  have hz := Matrix.SL2.odd_power_fixed_eq_zero a m hm ha ha1 (E v i) hh
  simpa only [map_zero,Pi.zero_apply] using congrFun hz j

/-- DGS (5.11), SL₂ branch, from just the two complementary Sylow fixed
spaces. All positive binary field degrees, including field order two, work. -/
theorem sl2_odd_fixed_eq_bot_of_complement
    (ρ : Representation (ZMod 2) SL(2,F) V) (S T : Sylow 2 SL(2,F))
    (hc : IsCompl (fixedSpace ρ S) (fixedSpace ρ T))
    (a : SL(2,F)) {m : ℕ} (hm : Odd m) (ha : a^m=1) (ha1 : a≠1) :
    fixedSpace ρ (zpowers a) = ⊥ := by
  have h := SL2SylowFixedRecognition.fixedSpaceHypotheses_of_isCompl ρ S T hc
  exact odd_fixed_eq_bot_of_natural_copies ρ
    (sl2_natural_copies ρ S h.quadratic h.generated
      (SL2SylowFixedRecognition.fixed_eq_bot_of_isCompl ρ S T hc)) a hm ha ha1

omit [Finite V] in
/-- In binary SL₂ the source subgroup Ω₁(Z(S)) is the whole Sylow. -/
theorem sl2_omega_center_eq (S : Sylow 2 SL(2,F)) :
    omegaOneAmbient ((center S).map (S : Subgroup SL(2,F)).subtype) = S := by
  let : IsMulCommutative S := ⟨⟨fun x y =>
    (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S).symm.injective (by simp [mul_comm])⟩⟩
  have hC : (center S).map (S : Subgroup SL(2,F)).subtype = S := by
    rw [center_eq_top,←MonoidHom.range_eq_map,range_subtype]
  rw [hC]
  apply le_antisymm (omegaOneAmbient_le _)
  intro x hx
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl x hx
  exact congrArg Subtype.val
    (Matrix.SpecialLinearGroup.twoSubgroup_pow_two (S : Subgroup SL(2,F)) S.isPGroup' ⟨x,hx⟩)

/-- The literal omega-center formulation of DGS (5.11), with the prescribed
Sylow, conjugator and arbitrary odd-order element. -/
theorem sl2_source_odd_fixed_eq_bot
    (ρ : Representation (ZMod 2) SL(2,F) V) (S : Sylow 2 SL(2,F))
    (g : SL(2,F))
    (hc : IsCompl
      (fixedSpace ρ (omegaOneAmbient ((center S).map (S : Subgroup SL(2,F)).subtype)))
      (fixedSpace ρ ((omegaOneAmbient ((center S).map (S : Subgroup SL(2,F)).subtype)).map
        (MulAut.conj g).toMonoidHom)))
    (a : SL(2,F)) (hm : Odd (orderOf a)) (ha1 : a≠1) :
    fixedSpace ρ (zpowers a) = ⊥ := by
  rw [sl2_omega_center_eq] at hc
  exact sl2_odd_fixed_eq_bot_of_complement ρ S (g • S) hc a hm (pow_orderOf_eq_one a) ha1
end Representation.RankOne.QuadraticRecognition
