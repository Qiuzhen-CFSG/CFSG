module
public import Stellmacher.SectionNine.NineNinePenultimateStabilizerExclusion
public import Stellmacher.SectionNine.NineEightWTransfer
public import Stellmacher.SectionNine.NineFivePreviousCommutation

public import Stellmacher.SectionNine.NineFivePenultimateResidualGeneration
/-!
# The final support commutator bound in (9.9)

The preceding module's intersection with the penultimate core has commutator
with the supplied canonical support contained in the first-step center. The
support and its source (1) centralizer bound remain the actual supplied data.

First the preceding module cannot centralize the terminal center. It already
centralizes the preterminal center; together these span the penultimate plane.
The ambient residual commutator bound and residual transitivity would then
put the module in the terminal stabilizer, contrary to the proved exclusion.
Consequently the terminal center lies outside the abelian initial neighborhood.
The required commutator lies both in that neighborhood and in the join of the
first and terminal center lines, so it lies in the first line alone.

Source: the final commutator assertion of Stellmacher (9.9), printed p.57/PDF
p.47 of `refs/files/stellmacher-n-group.pdf`. The argument does not assume the
remaining index-two normalizer conclusion.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_final_support_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card (VAt ctx.Γ previous ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤ Nat.card (VAt ctx.Γ previous))
    (support : Subgroup G)
    (hsupport : support ≤ VAt ctx.Γ ctx.criticalPath.a')
    (hcontrol : ⁅support, GAt ctx.Γ ctx.criticalPath.a' ⊓
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)⁆ ≤
        ZAt ctx.Γ ctx.criticalPath.firstStep ⊔ ZAt ctx.Γ ctx.criticalPath.a') :
    ⁅VAt ctx.Γ previous ⊓ QAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩),support⁆ ≤
        ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let B := VAt Γ previous
  let R := ZAt Γ cp.firstStep
  let Z := ZAt Γ cp.a'
  let W := GeneratedNeighborhoodV Γ cp.a
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let I := B ⊓ QAt Γ penultimate
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hpreAdj := Γ.adjacent_symm (nine_five_previous_adjacent_penultimate
    ctx.toLocalContext hshort preterminal
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩)
  have hterminalAdj := nine_five_penultimate_adjacent ctx.toLocalContext
  have hpreOrbit := nine_five_penultimate_neighbor_orbit ctx.toLocalContext preterminal hpreAdj
  obtain ⟨alignment,halign,_⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpenOrbit : IsConjugateVertex Γ cp.a penultimate := ⟨alignment,halign⟩
  have hBpre : B≤GAt Γ preterminal := by
    have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    have hlong : 4 < cp.length := by
      obtain ⟨n,hn⟩ := hodd
      change 3 < cp.length at hb
      omega
    exact (nine_eight_v_le_generated_neighborhood Γ hprevious).trans
      (nine_eight_neighborhood_le_preterminal ctx.toLocalContext hlong cp.a
        ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)))
  have hBnot : ¬ B ≤ GAt Γ cp.a' :=
    nine_nine_previous_not_le_terminal_stabilizer_of_large_intersection
      ctx hb hcore previous hprevious hne hlarge
  have hnoncomm : ⁅B,Z⁆ ≠ ⊥ := by
    intro hzero
    have hBpreCenter := hBpre.trans
      (nine_eight_first_orbit_center_centralizes ctx.toLocalContext preterminal hpreOrbit)
    have hpreNe : preterminal≠cp.a' := nine_five_previous_ne_terminal ctx.toLocalContext
      hshort preterminal ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩
    have hsplit := (nine_three_center_split ctx hshort hpenOrbit hpreAdj hterminalAdj hpreNe).1
    have hBcenter : B≤Subgroup.centralizer (ZAt Γ penultimate : Set G) := by
      apply Subgroup.le_centralizer_iff.mp
      rw [hsplit]
      exact sup_le (Subgroup.le_centralizer_iff.mpr hBpreCenter)
        (Subgroup.le_centralizer_iff.mpr
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero))
    have hcomm := (Subgroup.commutator_mono hBcenter le_rfl).trans
      (nine_eight_initial_orbit_centralizer_commutator ctx penultimate hpenOrbit)
    exact hBnot (nine_eight_stabilizer_transfer_of_commutator ctx.sectionSeven Γ
      penultimate preterminal cp.a' ((mem_neighborhood_iff_adjacent Γ).mpr hpreAdj)
      ((mem_neighborhood_iff_adjacent Γ).mpr hterminalAdj) B hBpre hcomm)
  have hcoreTerminal : QAt Γ penultimate≤GAt Γ cp.a' :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core penultimate cp.a'
      ((mem_neighborhood_iff_adjacent Γ).mpr hterminalAdj) default).2.2
  have hBW : B ≤ W := nine_eight_v_le_generated_neighborhood Γ hprevious
  have hWab : IsMulCommutative W := nine_eight_neighborhood_abelian ctx.toLocalContext
    (by change 4 < cp.length
        have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
        change Odd cp.length at hodd
        obtain ⟨k,hk⟩ := hodd
        change 3 < cp.length at hb
        omega) cp.a
  have hZnotW : ¬ Z ≤ W := by
    intro hZW
    exact hnoncomm (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hBW.trans ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hWab).trans
        (Subgroup.centralizer_le hZW))))
  have hZaB : ZAt Γ cp.a ≤ B := nine_seven_neighbor_center_le_module Γ
    (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hprevious))
  have hBZa : B ≤ Subgroup.centralizer (ZAt Γ cp.a : Set G) :=
    hBW.trans ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hWab).trans
      (Subgroup.centralizer_le (hZaB.trans hBW)))
  have hbound : ⁅I,support⁆ ≤ R ⊔ Z := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl (le_inf (inf_le_right.trans hcoreTerminal)
      (inf_le_left.trans hBZa))).trans hcontrol
  have hQaGa : QAt Γ cp.firstStep ≤ GAt Γ cp.a :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.firstStep cp.a
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)) default).2.2
  have hsupportGa : support ≤ GAt Γ cp.a := hsupport.trans (hcore.trans hQaGa)
  have hnormal : support ≤ Subgroup.normalizer (W : Set G) :=
    hsupportGa.trans (nine_seven_stabilizer_normalizes_neighborhood Γ cp.a)
  have hcommW : ⁅I,support⁆ ≤ W :=
    (Subgroup.commutator_mono (inf_le_left.trans hBW) le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hnormal)
  have hRZa : R ≤ ZAt Γ cp.a :=
    ((nine_seven_center_join ctx cp.a ⟨1, Γ.act_one _⟩).2 cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).2
  have hRW : R ≤ W := hRZa.trans (hZaB.trans hBW)
  have hfour := (lemma_nine_three_ambient ctx hshort cp.a ⟨1, Γ.act_one _⟩).2
  have hRcard := nine_next_center_order_of_initial_four ctx.toLocalContext hfour
  obtain ⟨mover, _, hmover⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hZcard := (nine_next_center_and_commutator_of_initial_four ctx.toLocalContext hfour
    cp.a' ⟨mover, hmover⟩).1
  obtain ⟨actor, _, _, hactorComm, hquot⟩ := nine_nine_initial_transvection ctx hshort hcore
  rw [hactorComm] at hquot
  have hRQ : QuotientCardEq (R ⊔ Z) R 2 := by
    change Nat.card (R ⊔ Z : Subgroup G) = 2 * Nat.card Z at hquot
    change Nat.card R = 2 at hRcard
    change Nat.card Z = 2 at hZcard
    change Nat.card (R ⊔ Z : Subgroup G) = 2 * Nat.card R
    omega
  have hcommR : ⁅I,support⁆ ≤ R := by
    by_contra hnot
    obtain ⟨element, helement, houtside⟩ := Set.not_subset.mp hnot
    have hjoinW := nine_five_index_two_span_of_element R (R ⊔ Z) W
      le_sup_left hRQ hRW element (hbound helement) houtside (hcommW helement)
    exact hZnotW (le_sup_right.trans hjoinW)
  exact hcommR

end Stellmacher.SectionNine
