module
public import Stellmacher.SectionNine.NineNineTerminalStabilizerExclusion
public import Stellmacher.SectionNine.NineNineNeighborStabilizerGeometry
public import Stellmacher.SectionNine.NineNineTerminalInputs
public import Stellmacher.SectionNine.NineSevenCentralizerCore
public import Stellmacher.SectionNine.NineFiveConjugatorAlgebra
public import Stellmacher.SectionNine.NineFivePenultimateJoinAction

/-!
# The penultimate-stabilizer exclusion in (9.9)

With the proved rank-one support and an intersection index of at least four,
`V_{a-1}` cannot lie in the penultimate stabilizer. Its already-proved escape
from the terminal stabilizer, together with the cubic local action at the
penultimate vertex, would give a terminal-stabilizer intersection of index at
most two and a nontrivial commutator with the terminal center.

The initial neighborhood is abelian, so that terminal center cannot lie in it.
The support commutator of the intersection lies both in the neighborhood and
in the join of the first and terminal center lines. Thus it lies in the first
line alone. The maximal-commutator identification puts the entire intersection
in `V_{a-1} ∩ V_1`, contradicting the index-four bound. The consequent escape
from the preterminal core is the immediate adjacent-core containment.

These are the exclusions before the second use of (9.8) in Stellmacher (9.9),
printed p.56/PDF p.46 of `refs/files/stellmacher-n-group.pdf`. The reversed
terminal-core containment and the transported (9.7) index bound remain explicit
inputs; neither unfinished numbered theorem is used.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_previous_not_le_penultimate_stabilizer
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
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤ Nat.card (VAt ctx.Γ previous)) :
    ¬ VAt ctx.Γ previous ≤ GAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  intro hcontained
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let B := VAt Γ previous
  let R := ZAt Γ cp.firstStep
  let Z := ZAt Γ cp.a'
  let W := GeneratedNeighborhoodV Γ cp.a
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let I := B ⊓ GAt Γ cp.a'
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  obtain ⟨support, hsupport, hcomm, hcontrol⟩ :=
    nine_nine_support_of_terminal_core ctx hshort hcore
  have hmax := nine_nine_maximal_eq_intersection ctx hb support (hsupport.trans hcore)
    hcomm previous hprevious hne
  let data : NineNineSupportData ctx.toLocalContext hb := {
    terminal_core := hcore
    support := support
    support_le := hsupport
    support_commutator := hcomm
    centralizer_commutator := hcontrol
    previous := previous
    previous_neighbor := hprevious
    previous_ne := hne
    maximal_eq := hmax
    large_index := hlarge }
  have hBpre : B ≤ GAt Γ preterminal :=
    nine_nine_previous_le_preterminal_stabilizer ctx.toLocalContext hb data
  have hBnot : ¬ B ≤ GAt Γ cp.a' :=
    nine_nine_previous_not_le_terminal_stabilizer_of_large_intersection
      ctx hb hcore previous hprevious hne hlarge
  obtain ⟨aligner, hpenultimate, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpenOrbit : IsConjugateVertex Γ cp.a penultimate := ⟨aligner, hpenultimate⟩
  have hpreAdj : Γ.adjacent penultimate preterminal := Γ.adjacent_symm
    (nine_five_previous_adjacent_penultimate ctx.toLocalContext hshort preterminal
      ⟨⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩, rfl, rfl⟩)
  have hterminalAdj : Γ.adjacent penultimate cp.a' :=
    nine_five_penultimate_adjacent ctx.toLocalContext
  obtain ⟨hIcard, hnoncomm⟩ := nine_nine_neighbor_stabilizer_geometry ctx hshort
    hpenOrbit hpreAdj hterminalAdj B (le_inf hcontained hBpre) hBnot
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
    exact (Subgroup.commutator_mono le_rfl (le_inf inf_le_right
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
  have hImax := (le_nineNineCommutatorBound_iff B support R I
    (nine_nine_previous_normalizes_first_center ctx.toLocalContext hb previous hprevious)).mpr
      ⟨inf_le_left, hcommR⟩
  rw [hmax] at hImax
  have hImaxCard := Subgroup.card_le_of_le hImax
  have hpositive : 0 < Nat.card
    (VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) := Nat.card_pos
  change Nat.card (VAt ctx.Γ previous) ≤ 2 * Nat.card I at hIcard
  change Nat.card I ≤ Nat.card
    (VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) at hImaxCard
  omega

public theorem nine_nine_previous_not_le_preterminal_core
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
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤ Nat.card (VAt ctx.Γ previous)) :
    ¬ VAt ctx.Γ previous ≤ QAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  intro hcontained
  apply nine_nine_previous_not_le_penultimate_stabilizer
    ctx hb hcore previous hprevious hne hlarge
  have hadj := nine_five_previous_adjacent_penultimate ctx.toLocalContext (by change 1 < ctx.criticalPath.length; omega)
    (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
    ⟨⟨ctx.criticalPath.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩, rfl, rfl⟩
  exact hcontained.trans (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj) default).2.2)

end Stellmacher.SectionNine
