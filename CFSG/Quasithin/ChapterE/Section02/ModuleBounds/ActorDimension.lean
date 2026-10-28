module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.Strict
import all CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.Strict

/-!
# Comparing the original cubic actor with the original star quotient

Exact kernel counting gives |V|=|Z| |A/Z| |VJ/J|. The central subgroup Z
is fixed, so an upper bound 2^d for |VJ/J| gives fixed codimension at most
rank(A/Z)+d. Comparing d with the actual actor rank then yields the cubic
bound at two, or its strict version. All quotient maps and coordinate
conjugation identities are literal.

The internal import reuses the fixed-subgroup cardinal argument of the
existing strict-dihedral proof; it exposes no private name in the API.
Source: Aschbacher–Smith E.2.13 proof equations (*)–(**), printed p.225.
The following source family modules discharge both numerical comparisons
from the concrete groups and the original source placement.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X D Q : Type*} [Group X] [Finite X] [Group D] [Finite D]
  [Group Q] [Finite Q] [IsElementaryAbelian 2 Q]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

omit [Finite X] in
theorem card_V_eq_card_A_mul_star (_h : Hypotheses T V M g) :
    Nat.card V = Nat.card (A V M g) * Nat.card (V.map (QuotientGroup.mk' (J M))) := by
  have hi := relIndex_ker V (QuotientGroup.mk' (J M))
  rw [QuotientGroup.ker_mk'] at hi
  have hb : (J M).subgroupOf V = (B V M).subgroupOf V := by ext x; simp [B]
  have hc := ((J M).subgroupOf V).card_mul_index
  have he : Nat.card ((J M).subgroupOf V) = Nat.card (B V M) := by
    rw [hb]
    exact Nat.card_congr (subgroupOfEquivOfLe (show B V M ≤ V from inf_le_right)).toEquiv
  rw [he, ← relIndex, hi] at hc
  have hAc : Nat.card (A V M g) = Nat.card (B V M) :=
    card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [← hc, hAc]

theorem actor_fixed_bound_add_star_dimension (h : Hypotheses T V M g)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (f : A V M g →* D) (hk : f.ker = (Z V g).subgroupOf (A V M g))
    (he : IsElementaryTwo f.range)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹)
    (d : ℕ) (hstar : Nat.card (V.map (QuotientGroup.mk' (J M))) ≤ 2 ^ d) :
    fixedCodim ρ f.range ≤ rank f.range + d := by
  apply actor_fixed_bound_of_fixed_subgroup e ρ f ha (Z V g) inf_le_left
    ((h.core_geometry.2.2.trans inf_le_right).trans (center_le_centralizer _))
  have hcA : Nat.card (A V M g) = Nat.card (Z V g) * Nat.card f.range := by
    have hc := f.ker.card_mul_index
    rw [index_ker, hk, Nat.card_congr (subgroupOfEquivOfLe
      (h.Z_le_B_inf_A.trans inf_le_right)).toEquiv] at hc
    exact hc.symm
  calc
    Nat.card V = (Nat.card (Z V g) * Nat.card f.range) *
        Nat.card (V.map (QuotientGroup.mk' (J M))) := by
      rw [h.card_V_eq_card_A_mul_star, hcA]
    _ ≤ (Nat.card (Z V g) * Nat.card f.range) * 2 ^ d :=
      Nat.mul_le_mul_left _ hstar
    _ = 2 ^ (rank f.range + d) * Nat.card (Z V g) := by
      rw [he.card_eq_two_pow_rank, pow_add]
      ring

theorem cubic_actor_of_star_dimension (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting X = pCore 2 X)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹)
    (d : ℕ) (hstar : Nat.card (V.map (QuotientGroup.mk' (J M))) ≤ 2 ^ d)
    (hd : d ≤ Nat.log 2 ((Z V g).relIndex (A V M g))) :
    f.ker = (Z V g).subgroupOf (A V M g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range ≤ 2 * rank f.range ∧ cubicRatio ρ ≤ 2 := by
  have hk := h.actor_kernel e ρ hρ f ha
  have he := h.actor_elementary hproper hfit f hk
  have hc := h.actor_cubic e ρ f ha
  have hr : rank f.range = Nat.log 2 ((Z V g).relIndex (A V M g)) := by
    change Nat.log 2 (Nat.card f.range) = _
    rw [← index_ker, hk]
    rfl
  have hb₀ := h.actor_fixed_bound_add_star_dimension e ρ f hk he ha d hstar
  have hb : fixedCodim ρ f.range ≤ 2 * rank f.range := by rw [← hr] at hd; omega
  exact ⟨hk,he,hc,hb,(cubicRatio_le_nat_iff ρ 2).mpr ⟨f.range,he,hc,hb⟩⟩
theorem cubic_actor_of_strict_star_dimension (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting X = pCore 2 X)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹)
    (d : ℕ) (hstar : Nat.card (V.map (QuotientGroup.mk' (J M))) ≤ 2 ^ d)
    (hd : d < Nat.log 2 ((Z V g).relIndex (A V M g))) :
    f.ker = (Z V g).subgroupOf (A V M g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range < 2 * rank f.range ∧
      actionRatio ρ f.range < 2 ∧ cubicRatio ρ < 2 := by
  have hk := h.actor_kernel e ρ hρ f ha
  have he := h.actor_elementary hproper hfit f hk
  have hc := h.actor_cubic e ρ f ha
  have hr : rank f.range = Nat.log 2 ((Z V g).relIndex (A V M g)) := by
    change Nat.log 2 (Nat.card f.range) = _
    rw [← index_ker, hk]
    rfl
  have hb₀ := h.actor_fixed_bound_add_star_dimension e ρ f hk he ha d hstar
  have hb : fixedCodim ρ f.range < 2 * rank f.range := by rw [← hr] at hd; omega
  have har : actionRatio ρ f.range < 2 := by
    have h0 : (rank f.range : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he.rank_pos)
    rw [actionRatio, ENNReal.div_lt_iff (Or.inl h0) (Or.inl (by simp))]
    exact_mod_cast hb
  exact ⟨hk,he,hc,hb,har,
    (iInf_le_of_le f.range (iInf_le_of_le ⟨he,hc⟩ le_rfl)).trans_lt har⟩
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
