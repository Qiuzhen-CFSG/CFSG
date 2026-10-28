module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.ZeroIntersection
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallAutomizer

/-!
# The star-image reduction in E.2.17

For the original two-conjugate configuration on a four-dimensional space,
the source actor-degree bound and an automizer of order at most four force
|VJ/J|=2 whenever the cubic ratio is greater than one. An elementary core
would give ratio at most one. This excludes both an actor of rank one and
trivial intersection Z. The exact identity |V|=|Z||A/Z||VJ/J| then gives the
claim. The original witness consumer discharges the actor-degree bound in
its dihedral, linear and Suzuki models.

Source: Aschbacher–Smith, E.2.17, first paragraph, printed p.229.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X D Q : Type*} [Group X] [Finite X] [Group D] [Finite D]
  [Group Q] [Finite Q] [IsElementaryAbelian 2 Q]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem star_card_two_of_small_automizer
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting X = pCore 2 X)
    (hV : Nat.card V = 16)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹)
    (hD : Nat.card D ≤ 4) (hq : 1 < cubicRatio ρ)
    (d : ℕ) (hstar : Nat.card (V.map (QuotientGroup.mk' (J M))) ≤ 2^d)
    (hd : d ≤ Nat.log 2 ((Z V g).relIndex (A V M g))) :
    Nat.card (V.map (QuotientGroup.mk' (J M))) = 2 := by
  have hk := h.actor_kernel e ρ hρ f ha
  have he := h.actor_elementary hproper hfit f hk
  have hc := h.actor_cubic e ρ f ha
  have hr : rank f.range = Nat.log 2 ((Z V g).relIndex (A V M g)) :=
    by
      change Nat.log 2 (Nat.card f.range) = _
      rw [← index_ker, hk]
      rfl
  have hnot : ¬ IsElementaryAbelian 2 (P V M g) := by
    intro hP
    have hb := h.actor_fixed_bound_of_P_elementary hP e ρ f ha d hstar
    have hle : cubicRatio ρ ≤ (1 : ℕ) := (cubicRatio_le_nat_iff ρ 1).mpr
      ⟨f.range, he, hc, by rw [one_mul, hr]; exact hb.trans hd⟩
    exact (not_le_of_gt hq) (by simpa only [Nat.cast_one] using hle)
  have hrle : rank f.range ≤ 2 := by
    have hh := (Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective).trans hD
    rw [he.card_eq_two_pow_rank] at hh
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  have hrne : rank f.range ≠ 1 := by
    intro hn
    apply hnot
    apply h.P_elementary_of_actor_index_two
    change ((Z V g).subgroupOf (A V M g)).index = 2
    rw [← hk, index_ker, he.card_eq_two_pow_rank, hn]
    decide
  have hr2 : rank f.range = 2 := by have := he.rank_pos; omega
  have hrc : Nat.card f.range = 4 := by rw [he.card_eq_two_pow_rank, hr2]; decide
  have hz : 2 ≤ Nat.card (Z V g) := by
    have hp : 0 < Nat.card (Z V g) := Nat.card_pos
    have hn : Nat.card (Z V g) ≠ 1 := by
      intro hc
      exact hnot (h.P_elementary_of_Z_eq_bot (Subgroup.card_eq_one.mp hc))
    omega
  have hs : 2 ≤ Nat.card (V.map (QuotientGroup.mk' (J M))) := by
    have hp : 0 < Nat.card (V.map (QuotientGroup.mk' (J M))) := Nat.card_pos
    have hn : Nat.card (V.map (QuotientGroup.mk' (J M))) ≠ 1 := by
      intro hc
      have hVJ : V ≤ J M := by
        simpa using (map_eq_bot_iff V).mp (Subgroup.card_eq_one.mp hc)
      exact h.V_not_le_twoCore hproper (h.le_twoCore_of_le_J V
        (by let := h.elementary; exact IsElementaryAbelian.isPGroup 2 V) hVJ)
    omega
  have hAc := f.ker.card_mul_index
  rw [index_ker, hk, Nat.card_congr (subgroupOfEquivOfLe
    (h.Z_le_B_inf_A.trans inf_le_right)).toEquiv, hrc] at hAc
  have hVc := h.card_V_eq_card_A_mul_star
  rw [hV, ← hAc] at hVc
  nlinarith
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
