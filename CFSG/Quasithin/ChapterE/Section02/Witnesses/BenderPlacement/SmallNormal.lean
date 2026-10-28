module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallSectionBounds
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallResidualSpan
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallSectionSource

/-!
# Normalized quaternion core in the solvable E.2.17 branch

The marked quaternion core lies in the global two-core and in the residual
span. The literal section action on that span has order sixteen; its order
sixty-four alternative is excluded by the source extraspecial residual
centralization. Consequently the span has order thirty-two and equals the
marked core, which is therefore normal in the ambient solvable group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.2.17, printed pp.229--230. The subsequent Thompson argument remains an
assembly responsibility.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]
  {S : Sylow 2 H} {W U : Subgroup H} [IsElementaryAbelian 2 W] {n : ℕ}
theorem OriginalWitness.small_normal_core_of_solvable
    {κ : GroupClass} (hH : IsSQTK κ H)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : Group.IsSolvable H)
    (w : OriginalWitness S (ChapterB.minimalParabolicMax S hP) W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ (ChapterB.minimalParabolicMax S hP).pCoreIn 2)
    (hout : ¬ W ≤ ChapterB.minimalParabolicCore S hP)
    (hfit : generalizedFitting H = pCore 2 H) (hW : Nat.card W = 16)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (W : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U W hU q hq hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax S hP)).map
      (ChapterB.minimalParabolicMax S hP).subtype ≤ centralizer (W : Set H)) :
    let P := w.pair.subgroup.pCoreIn 2
    P.Normal ∧ P ≤ (S : Subgroup H) ∧ Nonempty (QuaternionCentralProductData P) ∧
      U = P ⊔ (U ⊓ centralizer (W : Set H)) ∧
      P ⊓ centralizer (W : Set H) = P ⊓ W ∧
      ⁅U ⊓ centralizer (W : Set H),P⁆ ≤ P ⊓ W := by
  let P := w.pair.subgroup.pCoreIn 2
  let Z := (center P).map P.subtype
  let B := P ⊓ W
  let L := conjugateSpanBy B ⊤
  have hn := ChapterE.minimalParabolic_normalizer_le S hP W
    (IsElementaryAbelian.isPGroup 2 W) hSW hout
  have hsmall := w.small_quaternion_core hWS hSW hcore hn hfit hW
    hSU hU q hq hk hD hratio
  obtain ⟨d⟩ := hsmall.1
  have hplacement := w.small_core_placement_of_solvable hH hP hs hWS hSW hcore hout
    hfit hW hSU hU q hq hk hD hratio
  have hmove := w.small_span_residual_of_solvable hH hP hs hWS hSW hcore hout hfit hW
    hSU hU q hq hk hD hratio
  rw [←hplacement.2] at hmove
  change P ≤ L ∧ L = pCore 2 H ⊓ pResidual 2 H ∧ ⁅L,pResidual 2 H⁆ = L at hmove
  let : L.Normal := hmove.2.1.symm ▸ inferInstance
  obtain ⟨hZn,hZL,ha,hB,hsz,hd⟩ := w.small_section_bounds_of_solvable hH hP hs
    hWS hSW hcore hout hfit hW hSU hU q hq hk hD hratio hres
  let := hZn
  obtain ⟨_,hZcentral,hO,hE⟩ := w.small_span_section_of_solvable hH hP hs
    hWS hSW hcore hout hfit hW hSU hU q hq hk hD hratio hres
  let : IsElementaryAbelian 2 (L.map (QuotientGroup.mk' Z)) := hE
  let : IsElementaryAbelian 2 (L ⧸ Z.subgroupOf L) :=
    DihedralCubic.section_elementary_of_image L Z
  have hKV := ChapterB.minimalParabolic_residual_commutator_of_normalized_two_actor
    S hP W hWS hSW (fun hh => hout (hh.trans (ChapterB.minimalParabolicTwoCore_le_core S hP)))
  obtain ⟨e⟩ := hsmall.2.2.2.1
  have hI : Nat.card (w.pair.subgroup ⧸ pCore 2 w.pair.subgroup) = 6 := by
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  have h3 : 3 ∣ Nat.card H := by
    have hh := (pCore 2 w.pair.subgroup).index_dvd_card
    change Nat.card (w.pair.subgroup ⧸ pCore 2 w.pair.subgroup) ∣ Nat.card w.pair.subgroup at hh
    rw [hI] at hh
    exact ((by decide : 3 ∣ 6).trans hh).trans w.pair.subgroup.card_subgroup_dvd_card
  have he : ¬ (ChapterB.minimalParabolicMax S hP).pCoreIn 2 ≤ pCore 2 H := by
    intro hle
    exact hout (hcore.trans (hle.trans (ChapterB.minimalParabolicTwoCore_le_core S hP)))
  have hm := SolvableMinimalParabolic.source_cubic_models hH S hP hs (Or.inl he) h3
  have h16 := DihedralCubic.source_small_section_card S hP hs W B L Z hZL
    inf_le_right rfl hKV hmove.2.2.symm hO ha hd hsz hres hm
  have hZcard : Nat.card Z = 2 := by
    rw [card_map_of_injective P.subtype_injective]
    exact d.center_card
  have hZLcard : Nat.card (Z.subgroupOf L) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZL).toEquiv).trans hZcard
  have hLcard : Nat.card L = 32 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf L)
    rw [h16,hZLcard] at hh
    exact hh
  have hPL : P = L := eq_of_le_of_card_ge hmove.1 (by rw [hLcard,d.card])
  have hPn : P.Normal := hPL.symm ▸ inferInstance
  let := hPn
  exact ⟨hPn,hplacement.1.trans (pCore_isPGroup.le_sylow_of_normal S),⟨d⟩,
    hsmall.2.1,hsmall.2.2.1,hsmall.2.2.2.2 le_normalizer_of_normal⟩
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
