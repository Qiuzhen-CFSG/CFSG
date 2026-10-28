module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.Contradiction
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.NineExtension.Automorphisms
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.FieldTheory.Finiteness

/-!
# Comparing the full overlap automizer with a marked wreath residual

For H₁ ≤ J ≤ H, a literal wreath quotient and the equality L₁ = O²(H₁)
identify L₁/O₂(L₁) with the elementary cubic base of order nine. The
J-automizer has order dividing 48. Its kernel contains L₁, so a factor
three in its image would force 27 to divide |H|. A Sylow two-subgroup
of H contained in H₁ makes the relative image index odd. The computed
order-eight H₁ image therefore equals the whole J-automizer.

This is the conditional automizer calculation used in Aschbacher–Smith
13.8.16(1), printed p.952. The source assembly must supply the wreath
quotient, residual marking, numerical hypothesis and Sylow containment.
The argument retains the actual section and both conjugation maps.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup

private noncomputable def nineCoordinates (V : Type*) [Group V] [Finite V]
    [IsElementaryAbelian 3 V] (hc : Nat.card V = 9) :
    V ≃* Multiplicative (Fin 2 → ZMod 3) := by
  have hpow : 3 ^ Module.finrank (ZMod 3) (Additive V) = 3 ^ 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive V)
    change Nat.card V = _ at h
    simpa only [Nat.card_zmod, hc, show (3 : ℕ) ^ 2 = 9 by decide] using h.symm
  have hdim : Module.finrank (ZMod 3) (Additive V) = 2 :=
    Nat.pow_right_injective (by decide : 1 < 3) hpow
  exact (Module.finBasisOfFinrankEq (ZMod 3) (Additive V) hdim).equivFun.toAddEquiv.toMultiplicativeRight

variable {G : Type*} [Group G] [Finite G]

/-- The marked section is the actual cubic base of the given wreath quotient. -/
noncomputable def markedCubicEquiv (L₁ H₁ : Subgroup G)
    (hres : L₁ = (pResidual 2 H₁).map H₁.subtype)
    (e : H₁ ⧸ pCore 2 H₁ ≃* WreathModel.W) :
    (L₁ ⧸ pCore 2 L₁) ≃* WreathModel.cubicBase :=
  (markedQuotientEquiv L₁ H₁ hres).symm.trans (ResidualAction.residualQuotientEquiv e)

/-- The full J-automizer equals the induced image of the marked wreath overgroup. -/
theorem automizer_range_eq (L₁ H₁ J H : Subgroup G)
    (hHJ : H₁ ≤ J) (hJH : J ≤ H)
    (hres : L₁ = (pResidual 2 H₁).map H₁.subtype)
    (e : H₁ ⧸ pCore 2 H₁ ≃* WreathModel.W)
    (h27 : ¬ 27 ∣ Nat.card H) (S : Sylow 2 H)
    (hS : (S : Subgroup H).map H.subtype ≤ H₁) :
    (automizerAction L₁ J).range =
      (quotientAction L₁ H₁ (normalizes_embedded_residual L₁ H₁ hres)).range := by
  classical
  let V := L₁ ⧸ pCore 2 L₁
  let c := markedCubicEquiv L₁ H₁ hres e
  let : IsElementaryAbelian 3 V := IsElementaryAbelian.of_surjective c.symm.toMonoidHom c.symm.surjective
  have hV : Nat.card V = 9 := markedQuotient_card L₁ H₁ hres e
  have hAut : Nat.card (MulAut V) = 48 :=
    Matrix.PSL3Four.ExtendedCentralizer.NineExtension.automorphism_card (nineCoordinates V hV)
  have hn := normalizes_embedded_residual L₁ H₁ hres
  let A := J ⊓ normalizer (L₁ : Set G)
  let α : A →* MulAut V := automizerAction L₁ J
  let β : H₁ →* MulAut V := quotientAction L₁ H₁ hn
  have hHA : H₁ ≤ A := le_inf hHJ hn
  have hAH : A ≤ H := inf_le_left.trans hJH
  have hL : L₁ ≤ H₁ := hres ▸ map_subtype_le _
  have hLA : L₁ ≤ A := hL.trans hHA
  have hle : β.range ≤ α.range :=
    quotientAction_range_mono L₁ H₁ A hHA inf_le_right
  have hsmall : Nat.card β.range = 8 := by
    rw [Nat.card_congr (markedActionEquivDihedral L₁ H₁ hres hn e).toEquiv]
    exact DihedralGroup.nat_card
  have hLker : L₁.subgroupOf A ≤ α.ker := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro y
    induction y using Quotient.inductionOn with
    | h y =>
      let l : L₁ := ⟨x.val, hx⟩
      change quotientAction L₁ A inf_le_right x (QuotientGroup.mk' (pCore 2 L₁) y) = _
      rw [quotientAction_mk]
      change QuotientGroup.mk' (pCore 2 L₁) (l * y * l⁻¹) = QuotientGroup.mk' (pCore 2 L₁) y
      rw [map_mul, map_mul, map_inv, mul_comm (QuotientGroup.mk' (pCore 2 L₁) l), mul_inv_cancel_right]
  have h9ker : 9 ∣ Nat.card α.ker := by
    have h9 : 9 ∣ Nat.card L₁ := hV ▸ (pCore 2 L₁).card_quotient_dvd_card
    have heq := Nat.card_congr (subgroupOfEquivOfLe hLA).toEquiv
    exact (h9.trans (heq ▸ card_dvd_of_le hLker))
  have hnot3 : ¬ 3 ∣ Nat.card α.range := by
    intro h3
    apply h27
    have hmul := Nat.mul_dvd_mul h9ker h3
    rw [show 9 * 3 = 27 from rfl, ← index_ker, α.ker.card_mul_index] at hmul
    exact hmul.trans (card_dvd_of_le hAH)
  have hdiv : Nat.card α.range ∣ 48 := hAut ▸ α.range.card_subgroup_dvd_card
  have hidx : ¬ 2 ∣ β.range.relIndex α.range := by
    let P := (S : Subgroup H).map H.subtype
    have hPH : P.relIndex H = (S : Subgroup H).index := by
      have hh := relIndex_map_map_of_injective (S : Subgroup H) (⊤ : Subgroup H) H.subtype_injective
      simpa only [← MonoidHom.range_eq_map, H.range_subtype, relIndex_top_right] using hh
    have hHAodd : ¬ 2 ∣ H₁.relIndex A := by
      intro hd
      apply S.not_dvd_index
      rw [← hPH]
      have hdHA : H₁.relIndex A ∣ H₁.relIndex H := by
        rw [← relIndex_subgroupOf (H := H₁) hAH]
        exact relIndex_dvd_index_of_le (fun _ hx => hHA hx)
      exact hd.trans (hdHA.trans (relIndex_dvd_of_le_left H hS))
    have hmap : (H₁.subgroupOf A).map α = β.range := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x.val, hx⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨inclusion hHA x, x.property, rfl⟩
    have hd : β.range.relIndex α.range ∣ H₁.relIndex A := by
      rw [← hmap, MonoidHom.range_eq_map, relIndex_map_map, top_sup_eq, relIndex_top_right]
      exact index_dvd_of_le le_sup_left
    exact fun h => hHAodd (h.trans hd)
  have hmul := (β.range.subgroupOf α.range).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hmul
  change Nat.card β.range * β.range.relIndex α.range = Nat.card α.range at hmul
  rw [hsmall] at hmul
  have hcard : Nat.card α.range = 8 := by
    have hm : Nat.card α.range ∈ (48 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
    have hds : (48 : ℕ).divisors = {1, 2, 3, 4, 6, 8, 12, 16, 24, 48} := by decide
    rw [hds] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h <;> omega
  exact (eq_of_le_of_card_ge hle (by omega)).symm

/-- The conventional J-automizer has the computed dihedral structure. -/
noncomputable def automizerEquivDihedral (L₁ H₁ J H : Subgroup G)
    (hHJ : H₁ ≤ J) (hJH : J ≤ H)
    (hres : L₁ = (pResidual 2 H₁).map H₁.subtype)
    (e : H₁ ⧸ pCore 2 H₁ ≃* WreathModel.W)
    (h27 : ¬ 27 ∣ Nat.card H) (S : Sylow 2 H)
    (hS : (S : Subgroup H).map H.subtype ≤ H₁) :
    (automizerAction L₁ J).range ≃* D8 :=
  (MulEquiv.subgroupCongr (automizer_range_eq L₁ H₁ J H hHJ hJH hres e h27 S hS)).trans
    (markedActionEquivDihedral L₁ H₁ hres (normalizes_embedded_residual L₁ H₁ hres) e)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup

end
