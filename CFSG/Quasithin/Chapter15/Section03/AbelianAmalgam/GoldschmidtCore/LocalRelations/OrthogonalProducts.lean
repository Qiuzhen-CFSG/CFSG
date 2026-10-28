module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalProducts.Transport
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic
public import Theory.SpecificGroups.OrthogonalFourBinary.TerminalLines.Lines

/-!
# Assembly of the terminal orthogonal line product

This adapter retains the actual Sylow subgroup, residual, centralizer,
normalizer, definite plane, central involutions and conjugation action.
For the chosen `s ∈ S − T_E`, the published conjugate geometry gives the
second singular four-subgroup and its common central involution. Coordinate
transport applies a universal finite line calculation to that pair, and
kernel lifting supplies the literal product `Y = Y_E Y_F O₂(Y)`.
Commutativity of the model two-residual then gives both the relative
normality of `Y_E` and its normalizer containment. The product also gives
`⟨Y_F,T⟩ = M` through ProductConsequences.

`terminal_relations` discharges both finite-model calculations using the
actual plane rotations and singular-line stabilizers. Its remaining inputs
are the genuine earlier source conclusions, including the permitted
15.3.7 action-image identity. The definite-plane hypotheses identify the
source choice of `S`; once `s` is chosen, only its membership in `T` is
needed in this geometric route. No common-core equality is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.2,
15.3.7, 15.3.66–67 and the construction before 15.3.68, printed
pp.1121–1122 and 1152–1154 (PDF pp.1138–1139 and 1169–1171).
-/

public section

open Subgroup OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalProducts
variable {G : Type*} [Group G] [Finite G]

/-- Assemble the source relations after the two universal coordinate calculations. -/
theorem terminal_relations_of_model_calculations
    (T : Sylow 2 G) (M Mc Y V R V₁ E : Subgroup G)
    (d : NaturalAction V M)
    (_hMnormalizer : M = normalizer (V : Set G))
    (hY : Y = residualY M Mc)
    (hR : R = centralizer (V : Set G))
    (hRT : R = (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hMproduct : (M : Set G) = (Y : Set G) * (T : Set G))
    (hV₁ : V₁ ≤ V) (_hV₁card : Nat.card V₁ = 4)
    (_hdefinite : ∀ v : V₁, v ≠ 1 → ¬ d.singular ⟨v, hV₁ v.property⟩)
    (hEV : E ≤ V) (hEcard : Nat.card E = 4)
    (hEsingular : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (hZcard : Nat.card (centralInvolutions T) = 2)
    (hZE : centralInvolutions T ≤ E)
    (himage : actionImage d Y = pResidual 2 IsometryGroup)
    (s : G) (hs : s ∈ planeStabilizer T V₁) (hsE : s ∉ lineT (T : Subgroup G) E)
    (hcomm : IsMulCommutative (pResidual 2 IsometryGroup))
    (hcalc : ∀ A B : Subgroup (Multiplicative Space),
      Nat.card A = 4 → Nat.card B = 4 →
      (∀ w ∈ A, form (Multiplicative.toAdd w) = 0) →
      (∀ w ∈ B, form (Multiplicative.toAdd w) = 0) →
      A ≠ B → (∃ w, w ≠ 1 ∧ w ∈ A ∧ w ∈ B) →
      (pResidual 2 IsometryGroup : Set IsometryGroup) =
        (lineResidual A : Set IsometryGroup) * (lineResidual B : Set IsometryGroup)) :
    (Y : Set G) = (lineY Y E : Set G) * (lineY Y (otherLine E s) : Set G) *
        (Stellmacher.twoCoreAmbient Y : Set G) ∧
      IsMulCommutative (actionImage d Y) ∧
      ((lineY Y E).subgroupOf (Y ⊔ lineT (T : Subgroup G) E)).Normal ∧
      Y ⊔ lineT (T : Subgroup G) E ≤ normalizer (lineY Y E : Set G) ∧
      lineY Y (otherLine E s) ⊔ (T : Subgroup G) = M := by
  have hYM : Y ≤ M := by
    rw [hY]
    exact Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  have hTM : (T : Subgroup G) ≤ M := by
    intro t ht
    rw [← SetLike.mem_coe, hMproduct]
    exact ⟨1, Y.one_mem, t, ht, one_mul t⟩
  have hn : (Y.subgroupOf M).Normal := by rw [hY]; exact residualY_normal M Mc
  have hMY := (normal_subgroupOf_iff_le_normalizer hYM).mp hn
  have hTY := hTM.trans hMY
  have hMjoin : M = Y ⊔ (T : Subgroup G) := by
    apply SetLike.coe_injective
    exact hMproduct.trans (coe_mul_of_right_le_normalizer_left _ _ hTY).symm
  have hCT : centralizer (V : Set G) ≤ (T : Subgroup G) :=
    hR.symm.le.trans (hRT.le.trans inf_le_left)
  have hC : IsPGroup 2 (centralizer (V : Set G)) :=
    T.isPGroup'.of_injective (inclusion hCT) (inclusion_injective hCT)
  have hsT : s ∈ T := hs.1
  have hsM := hTM hsT
  have hFV := otherLine_le_module V M E d hEV s hsM
  have hFcard : Nat.card (otherLine E s) = 4 :=
    (card_map_of_injective (MulAut.conj s⁻¹).injective).trans hEcard
  have hFsingular := otherLine_totally_singular V M E d hEV hEsingular s hsM
  have hEF : E ≠ otherLine E s := (otherLine_ne (T : Subgroup G) E s hsT hsE).symm
  have hZF := centralInvolutions_le_otherLine T E hZE s hsT
  have hZne : centralInvolutions T ≠ ⊥ :=
    (one_lt_card_iff_ne_bot (centralInvolutions T)).mp (by rw [hZcard]; decide)
  obtain ⟨z, hz'⟩ := ne_bot_iff_exists_ne_one.mp hZne
  have hz : (z : G) ≠ 1 := fun h => hz' (Subtype.ext h)
  have hcoord := hcalc (coordinateLine d E) (coordinateLine d (otherLine E s))
    ((coordinateLine_card d E hEV).trans hEcard)
    ((coordinateLine_card d (otherLine E s) hFV).trans hFcard)
    (coordinateLine_singular d E hEV hEsingular)
    (coordinateLine_singular d (otherLine E s) hFV hFsingular)
    (fun he => hEF (coordinateLine_injective d E (otherLine E s) hEV hFV he))
    (coordinateLine_common_vector d E (otherLine E s) hEV z (hZE z.property) (hZF z.property) hz)
  have hprod := line_product_of_coordinate_product d Y E (otherLine E s) hYM hC hEV hFV
    himage hcoord
  have hcommY : IsMulCommutative (actionImage d Y) := himage ▸ hcomm
  have hc := actionImage_commutative_commutator d Y hYM
  exact ⟨hprod, hcommY,
    lineY_normal_in_local_product Y (T : Subgroup G) V E hEV hTY hc,
    lineY_normalized_by_local_product Y (T : Subgroup G) V E hEV hTY hc,
    generate_localGroup_from_line_product T M Y E hTM hYM hMY hMjoin s hsT hprod⟩

/-- The terminal line product, image commutativity, relative normality, and
Sylow generation, with the finite orthogonal calculations fully discharged. -/
theorem terminal_relations
    (T : Sylow 2 G) (M Mc Y V R V₁ E : Subgroup G)
    (d : NaturalAction V M)
    (_hMnormalizer : M = normalizer (V : Set G))
    (hY : Y = residualY M Mc)
    (hR : R = centralizer (V : Set G))
    (hRT : R = (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hMproduct : (M : Set G) = (Y : Set G) * (T : Set G))
    (hV₁ : V₁ ≤ V) (_hV₁card : Nat.card V₁ = 4)
    (_hdefinite : ∀ v : V₁, v ≠ 1 → ¬ d.singular ⟨v, hV₁ v.property⟩)
    (hEV : E ≤ V) (hEcard : Nat.card E = 4)
    (hEsingular : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (hZcard : Nat.card (centralInvolutions T) = 2)
    (hZE : centralInvolutions T ≤ E)
    (himage : actionImage d Y = pResidual 2 IsometryGroup)
    (s : G) (hs : s ∈ planeStabilizer T V₁) (hsE : s ∉ lineT (T : Subgroup G) E) :
    (Y : Set G) = (lineY Y E : Set G) * (lineY Y (otherLine E s) : Set G) *
        (Stellmacher.twoCoreAmbient Y : Set G) ∧
      IsMulCommutative (actionImage d Y) ∧
      ((lineY Y E).subgroupOf (Y ⊔ lineT (T : Subgroup G) E)).Normal ∧
      Y ⊔ lineT (T : Subgroup G) E ≤ normalizer (lineY Y E : Set G) ∧
      lineY Y (otherLine E s) ⊔ (T : Subgroup G) = M := by
  exact terminal_relations_of_model_calculations T M Mc Y V R V₁ E d
    _hMnormalizer hY hR hRT hMproduct hV₁ _hV₁card _hdefinite hEV hEcard
    hEsingular hZcard hZE himage s hs hsE residual_commutative residual_line_product

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalProducts
