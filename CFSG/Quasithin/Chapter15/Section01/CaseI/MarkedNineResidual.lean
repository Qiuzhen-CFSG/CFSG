module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedNine
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedQuotient
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ResidualIntersection
public import Theory.GroupTheory.PResidual.OrderSix

/-!
# The residual intersection for the elementary-nine marking

Use the actual vector and stabilizer selected by the Nine source row.
The marked centralizer quotient has order six, hence its two-residual has
order three. The literal Sylow intersection and generation already proved
for this same marking then give original 15.1.18(2). No new vector, quotient
model, or prime-order hypothesis is selected in this step.

Source: Aschbacher--Smith 15.1.16(b)--18(2), printed p.1092.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Keep all marking data together with its literal quotient residual of order three. -/
theorem chosen_nine_marked_residual
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (h9 : SourceCases.Nine (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict)) :
    ∃ Z1 : Subgroup G, Z1 ≤ thompsonFixed T V ∧ Z1 ≠ ⊥ ∧
      M = (M ⊓ centralizer (Z1 : Set G)) ⊔ (T : Subgroup G) ∧
      (∃ P : Sylow 2 ↥(M ⊓ centralizer (Z1 : Set G)),
        (P : Subgroup ↥(M ⊓ centralizer (Z1 : Set G))).map
          (M ⊓ centralizer (Z1 : Set G)).subtype =
            (T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ∧
      (letI := caseI_module_centralizer_normal (Z1 := Z1) hn;
        Nat.card (pResidual 2 (↥(M ⊓ centralizer (Z1 : Set G)) ⧸
          (M ⊓ centralizer (V : Set G)).subgroupOf
            (M ⊓ centralizer (Z1 : Set G)))) = 3) := by
  obtain ⟨v, K, hv, hfixed, hK, hgen, hc, hSyl⟩ := chosen_nine_marked_image T hTM hn h9
  obtain ⟨hZ, hne, hM, hS⟩ :=
    marked_zpowers_and_sylow_of_image_stabilizer T hTM hn v hv hfixed K hK hgen hSyl
  refine ⟨zpowers (v.toMul : G), hZ, hne, hM, hS, ?_⟩
  let := caseI_module_centralizer_normal (Z1 := zpowers (v.toMul : G)) hn
  apply card_twoResidual_of_card_six
  exact (marked_quotient_card M V hn v K hK (zpowers_le.mpr v.toMul.property)).trans hc

/-- Apply the actual Nine marking to the literal residual identity in
original 15.1.18(2), discharging its marked Sylow and prime quotient inputs. -/
theorem chosen_nine_residual_intersection
    (T : Sylow 2 G) {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (h9 : SourceCases.Nine (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict))
    (hNMc : M ⊓ centralizer (V : Set G) ≤ Mc)
    (hTMc : (T : Subgroup G) ≤ Mc) (hMnot : ¬ M ≤ Mc) :
    ∃ Z1 : Subgroup G, Z1 ≤ thompsonFixed T V ∧ Z1 ≠ ⊥ ∧
      M = (M ⊓ centralizer (Z1 : Set G)) ⊔ (T : Subgroup G) ∧
      (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
          (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
        (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
          (M ⊓ centralizer (V : Set G)).subtype := by
  obtain ⟨Z1, hZ, hne, hM, hSyl, hres⟩ := chosen_nine_marked_residual T hTM hn h9
  refine ⟨Z1, hZ, hne, hM,
    caseI_residual_intersection T M Mc V Z1 hn (hZ.trans inf_le_left)
      hNMc hTMc hMnot hM hSyl ?_⟩
  let := caseI_module_centralizer_normal (Z1 := Z1) hn
  rw [hres]
  decide
end CFSG.Quasithin.Chapter15.Section01
