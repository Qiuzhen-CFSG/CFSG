module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallSpanSection
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallCoreSpan

/-!
# Cardinal bounds for the E.2.17 section

For a solvable small automizer witness, the marked quaternion core has order
`32`, its center has order `2`, and the marked elementary subgroup has order
`8`.  Passing to the central section therefore gives the literal order-two
module image, an order-four marked image, and the lower section bound used by
the E.2.17 alternatives.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.2.17 (printed pp. 228--229).
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
private theorem card_map_mul_card_inf {H : Type*} [Group H] [Finite H]
    (X Z : Subgroup H) [Z.Normal] :
    Nat.card (X.map (QuotientGroup.mk' Z)) * Nat.card (X ⊓ Z : Subgroup H) = Nat.card X := by
  have hc : Nat.card (Z.subgroupOf X) = Nat.card (X ⊓ Z : Subgroup H) := by
    rw [←card_map_of_injective X.subtype_injective,subgroupOf_map_subtype,inf_comm]
  rw [←relIndex_ker X (QuotientGroup.mk' Z),QuotientGroup.ker_mk',←hc,mul_comm]
  exact (Z.subgroupOf X).card_mul_index

private theorem nat_card_subgroup_mono {H : Type*} [Group H] [Finite H]
    {A B : Subgroup H} (h : A ≤ B) : Nat.card A ≤ Nat.card B := by
  apply Nat.card_le_card_of_injective
    (f := fun x : A => (⟨(x : H), h x.property⟩ : B))
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : B => (z : H)) hxy

namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
open TwoConjugate
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]
  {S : Sylow 2 H} {N W U : Subgroup H} [IsElementaryAbelian 2 W] {n : ℕ}
theorem OriginalWitness.small_seed_card (w : OriginalWitness S N W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ N.pCoreIn 2) (hn : normalizer (W : Set H) ≤ N)
    (hfit : generalizedFitting H = pCore 2 H) (hW : Nat.card W = 16)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (W : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U W hU q hq hk)) :
    Nat.card (w.pair.subgroup.pCoreIn 2 ⊓ W : Subgroup H) = 8 := by
  let h := w.pair.hypotheses hWS hSW hcore hn
  let hSU' := w.pair.sylow_eq.le.trans (inf_le_left.trans hSU)
  let e := subgroupOfEquivOfLe w.pair.le
  let ρ := DihedralCubic.representation U W hU q hq hk
  let f := DihedralCubic.actorMap h hSU' q
  have hp := w.pair.proper_of_quotient_card_ne_one hn w.model.card_ne_one
  have hf := w.pair.fitting hSW hfit
  have ha : ∀ (a : A (W.subgroupOf w.pair.subgroup) (N.subgroupOf w.pair.subgroup) w.pair.conjugator)
      (v : W.subgroupOf w.pair.subgroup),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : w.pair.subgroup) =
        (a : w.pair.subgroup) * v * (a : w.pair.subgroup)⁻¹ := by
    intro a v
    apply Subtype.ext
    change ((ρ (q (DihedralCubic.actorIn h hSU' a)) (Additive.ofMul (e v))).toMul : H) =
      ((a : w.pair.subgroup) : H) * ((v : w.pair.subgroup) : H) *
        ((a : w.pair.subgroup) : H)⁻¹
    rw [DihedralCubic.representation_apply]
    rfl
  have hρ := DihedralCubic.representation_injective U W hU q hq hk
  have hcard := w.model.star_card_two h hp hf ((Nat.card_congr e.toEquiv).trans hW)
    e ρ hρ f ha hD hratio
  have hc := h.small_automizer_core_orders hp hf hcard
    ((Nat.card_congr e.toEquiv).trans hW) e ρ hρ f ha hD hratio
  have hB : (B (W.subgroupOf w.pair.subgroup) (N.subgroupOf w.pair.subgroup)).map
      w.pair.subgroup.subtype = w.pair.subgroup.pCoreIn 2 ⊓ W := by
    rw [h.B_eq_twoCore_inf,map_inf _ _ _ w.pair.subgroup.subtype_injective,
      map_subgroupOf_eq_of_le w.pair.le]
    rfl
  rw [←hB,card_map_of_injective w.pair.subgroup.subtype_injective]
  exact hc.2.1

/-- The solvable small-core placement already fixes the literal module image
order.  This projection is kept separate because the residual Frattini
inverter only needs the order-two image, before the central section is formed. -/
theorem OriginalWitness.small_module_image_card_of_solvable
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
    (hratio : 1 < cubicRatio (DihedralCubic.representation U W hU q hq hk)) :
    Nat.card (W.map (QuotientGroup.mk' (pCore 2 H))) = 2 := by
  have hn := ChapterE.minimalParabolic_normalizer_le S hP W
    (IsElementaryAbelian.isPGroup 2 W) hSW hout
  have hplacement := w.small_core_placement_of_solvable hH hP hs hWS hSW hcore hout
    hfit hW hSU hU q hq hk hD hratio
  have hBcard := w.small_seed_card hWS hSW hcore hn hfit hW hSU hU q hq hk hD hratio
  have hh := card_map_mul_card_inf W (pCore 2 H)
  rw [inf_comm,←hplacement.2,hBcard,hW] at hh
  omega

theorem OriginalWitness.small_section_bounds_of_solvable
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
    let Z := (center P).map P.subtype
    let B := P ⊓ W
    let L := conjugateSpanBy B ⊤
    ∃ hZn : Z.Normal, letI := hZn
      Z ≤ L ∧ Nat.card (W.map (QuotientGroup.mk' (pCore 2 H))) = 2 ∧
      Nat.card (B.map (QuotientGroup.mk' Z)) = 4 ∧
      16 ≤ Nat.card (L ⧸ Z.subgroupOf L) ∧
      Nat.card ((⁅L,W⁆).map (QuotientGroup.mk' Z)) ≤ 4 := by
  let P := w.pair.subgroup.pCoreIn 2
  let Z := (center P).map P.subtype
  let B := P ⊓ W
  let L := conjugateSpanBy B ⊤
  have hcenter := w.small_center_of_solvable hH hP hs hWS hSW hcore hout hfit hW
    hSU hU q hq hk hD hratio hres
  obtain ⟨hZn,hcentral,hcomm,hE⟩ := w.small_span_section_of_solvable hH hP hs hWS hSW
    hcore hout hfit hW hSU hU q hq hk hD hratio hres
  let := hZn
  have hn := ChapterE.minimalParabolic_normalizer_le S hP W
    (IsElementaryAbelian.isPGroup 2 W) hSW hout
  have hplacement := w.small_core_placement_of_solvable hH hP hs hWS hSW hcore hout
    hfit hW hSU hU q hq hk hD hratio
  have hPL := w.small_core_le_span hWS hSW hcore hn hfit hW hSU hU q hq hk hD hratio
  have hBcard := w.small_seed_card hWS hSW hcore hn hfit hW hSU hU q hq hk hD hratio
  have hsmall := w.small_quaternion_core hWS hSW hcore hn hfit hW hSU hU q hq hk hD hratio
  obtain ⟨d⟩ := hsmall.1
  have hZP : Z ≤ P := map_subtype_le _
  have hZB : Z ≤ B := le_inf hZP (hcenter.2.le.trans inf_le_left)
  have hZcard : Nat.card Z = 2 := by
    rw [card_map_of_injective P.subtype_injective]
    exact d.center_card
  have hBmap : Nat.card (B.map (QuotientGroup.mk' Z)) = 4 := by
    have hh := card_map_mul_card_inf B Z
    rw [inf_eq_right.mpr hZB,hZcard,hBcard] at hh
    omega
  have hPmap : Nat.card (P.map (QuotientGroup.mk' Z)) = 16 := by
    have hh := card_map_mul_card_inf P Z
    rw [inf_eq_right.mpr hZP,hZcard,d.card] at hh
    omega
  have hWmap : Nat.card (W.map (QuotientGroup.mk' (pCore 2 H))) = 2 := by
    have hh := card_map_mul_card_inf W (pCore 2 H)
    rw [inf_comm,←hplacement.2,hBcard,hW] at hh
    omega
  have hsize : 16 ≤ Nat.card (L ⧸ Z.subgroupOf L) := by
    have he : Nat.card (L ⧸ Z.subgroupOf L) = Nat.card (L.map (QuotientGroup.mk' Z)) := by
      calc
        Nat.card (L ⧸ Z.subgroupOf L) = Z.relIndex L := by
          exact (index_eq_card (Z.subgroupOf L)).symm
        _ = Nat.card (L.map (QuotientGroup.mk' Z)) := by
          simpa only [QuotientGroup.ker_mk'] using
            (relIndex_ker L (QuotientGroup.mk' Z))
    rw [he,←hPmap]
    exact nat_card_subgroup_mono (map_mono hPL)
  have hLQ : L ≤ pCore 2 H :=
    conjugateSpanBy_le (inf_le_left.trans hplacement.1) le_normalizer_of_normal
  have hLV : ⁅L,W⁆ ≤ B := by
    rw [show B = pCore 2 H ⊓ W from hplacement.2]
    refine le_inf ((commutator_mono hLQ le_rfl).trans (commutator_le_left _ _)) ?_
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      (hLQ.trans ((pCore_isPGroup.le_sylow_of_normal S).trans hSW))
  exact ⟨hZn,hZP.trans hPL,hWmap,hBmap,hsize,
    (nat_card_subgroup_mono (map_mono hLV)).trans_eq hBmap⟩

end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
