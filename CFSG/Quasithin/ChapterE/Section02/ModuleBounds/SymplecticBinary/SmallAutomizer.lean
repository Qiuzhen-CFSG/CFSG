module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.SymplecticBinary.Strict

/-!
# Small automizers exclude the binary symplectic pair

The literal actor embeds in a group of order at most four, so its rank is at
most two. The original Sp4(2) orbit theorem then makes P elementary. Its
fixed-codimension bound supplies a cubic actor of ratio at most one.

Source: Aschbacher--Smith E.2.17, printed pp.229--230, using E.2.15.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
open Theory.SpecificGroups.SymplecticFour
variable {X D Q : Type*} [Group X] [Finite X] [Group D] [Finite D]
  [Group Q] [Finite Q] [IsElementaryAbelian 2 Q]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem binary_symplectic_small_automizer_false
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (ξ : (X ⧸ J M) ≃* Sp (ZMod 2)) (S : Sylow 2 (Sp (ZMod 2)))
    (hVS : V.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (J M))) ≤
      (center S).map (S : Subgroup _).subtype)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹)
    (hD : Nat.card D ≤ 4) (hq : 1 < cubicRatio ρ) : False := by
  have hk := h.actor_kernel e ρ hρ f ha
  have he := h.actor_elementary hproper hfit f hk
  have hc := h.actor_cubic e ρ f ha
  have hr : rank f.range = Nat.log 2 ((Z V g).relIndex (A V M g)) := by
    change Nat.log 2 (Nat.card f.range) = _
    rw [← index_ker,hk]
    rfl
  have hrle : rank f.range ≤ 2 := by
    have hh := (Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective).trans hD
    rw [he.card_eq_two_pow_rank] at hh
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  have hP := h.P_elementary_of_symplectic_four_binary_rank_le hproper hfit
    (by simp : Nat.card (ZMod 2) = 2) ξ (hr ▸ hrle)
  have hb := h.actor_fixed_bound_of_P_elementary hP e ρ f ha 2
    (star_card_le_symplectic_center 1 (by decide) (by simp) ξ S hVS)
  have hd := h.actor_rank_ge_symplectic_four hfit 1 (by decide) (by simp) ξ
  have hle : cubicRatio ρ ≤ (1 : ℕ) := (cubicRatio_le_nat_iff ρ 1).mpr
    ⟨f.range,he,hc,by rw [one_mul,hr]; exact hb.trans (by simpa using hd)⟩
  exact (not_le_of_gt hq) (by simpa only [Nat.cast_one] using hle)
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
