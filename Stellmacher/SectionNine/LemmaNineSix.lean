module

public import Stellmacher.SectionNine.LemmaNineFour
public import Stellmacher.SectionNine.NineSixLengthThree
public import Stellmacher.SectionNine.NineSixTerminalCoreExclusion
public import Stellmacher.SectionNine.NineSixNineFourGeometry
public import Stellmacher.SectionNine.NineSixNonzeroCommutator
public import Stellmacher.SectionNine.NineSixZeroCommutatorCoatom

/-!
# Stellmacher (9.6): the index-two neighboring-module intersection

For a commuting critical path of length greater than one, if the first
stabilizer modulo its two-core is SL₂(2), its neighbor-center module
intersects the module at offset three with index two. The ambient theorem
retains both the ambient and graph groups, and the original public theorem
is its unchanged canonical-context specialization.

The length-three case is handled by the proved residual-intersection
argument. For a longer path, failure of index two gives module order sixteen.
Terminal containment in the first core contradicts the independently proved
predecessor classification supplied with actual (9.8). Otherwise a terminal
actor outside that core supplies all original hypotheses for (9.4), with a
backward neighbor whose intersection is the initial center. If the backward
and preterminal modules commute, the coatom producer and (9.4) force an
impossibly large subgroup into that order-four intersection. If they do not,
(9.4) places their commutator in the first module, and the center-core
transfer and two-center span contradict criticality.

Source: Stellmacher (9.6), printed p.53 / PDF p.43 of
`refs/files/stellmacher-n-group.pdf`. The shorter terminal-core reduction
uses the independent source (9.9)(3) predecessor classification; its import
closure does not contain (9.6) or the numbered (9.9) theorem. Every original
(9.4) premise is produced from the retained path and module data.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem lemma_nine_six_ambient
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2 := by
  classical
  by_contra hnot
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 3 ≤ cp.length := by obtain ⟨index,hindex,_⟩ := hpath;dsimp [cp];omega
  by_cases hthree : cp.length=3
  · exact hnot (nine_six_index_two_of_length_three ctx hthree third hpath hquot)
  have hlong : 3 < cp.length := by omega
  have hfourLong : 4 < cp.length := by
    obtain ⟨k,hk⟩ := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    omega
  have hnotCore : ¬ VAt Γ cp.a' ≤ QAt Γ cp.firstStep :=
    fun hcore => nine_six_terminal_core_exclusion ctx hlong third hpath hquot hnot hcore
  obtain ⟨t,ht,houtside⟩ := Set.not_subset.mp hnotCore
  obtain ⟨x,hx,hdistance,htpair,hprevious,hpreviousNe,hinter,hgen,hdisplacement⟩ :=
    nine_six_nine_four_geometry ctx third hpath hquot hnot t ht houtside
  let previous := Γ.act x third
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let R := ⁅VAt Γ previous,VAt Γ preterminal⁆
  have hbackInter : VAt Γ previous ⊓ VAt Γ cp.firstStep=ZAt Γ cp.a := by
    rw [inf_comm]
    exact hinter
  let second := cp.path ⟨2,by omega⟩
  have hsecond : IsCriticalPathOffset Γ cp 2 second := ⟨⟨2,by omega⟩,rfl,rfl⟩
  have hfour := (lemma_nine_three_ambient ctx hb cp.a ⟨1,Γ.act_one _⟩).2
  have hbound := nine_six_first_module_card_le ctx.toLocalContext hb hfour hquot
  have hcard : Nat.card (VAt Γ cp.firstStep)=16 :=
    nine_six_order_sixteen_of_not_index_two ctx.toLocalContext
      second third hsecond hpath hfour hbound hnot
  obtain ⟨align,halign⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
  change Γ.act (align:G) cp.firstStep=previous at halign
  have hpreviousCard : Nat.card (VAt Γ previous)=16 := by
    change Nat.card (v Γ previous)=16
    rw [← halign,v_act,Subgroup.card_map_of_injective (MulAut.conj (align:G)⁻¹).injective]
    exact hcard
  have hterminalFirst : VAt Γ cp.a' ≤ GAt Γ cp.firstStep :=
    (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2
  have hRbigFirst : ⁅VAt Γ cp.firstStep,VAt Γ cp.a'⁆ ≤ VAt Γ cp.firstStep :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hterminalFirst.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  by_cases hzero : R=⊥
  · obtain ⟨K,hKback,hKcard,hKcomm⟩ := nine_six_zero_commutator_coatom ctx hlong
      hquot hcard previous hprevious hpreviousNe hzero
    have hKactor : ⁅K,Subgroup.zpowers t⁆ ≤ VAt Γ cp.firstStep :=
      (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr ht)).trans
        (hKcomm.trans hRbigFirst)
    have hKfirst := lemma_nine_four_ambient ctx hb third hdistance t htpair x hx K hKback hKactor hgen hdisplacement
    have hKcenter : K ≤ ZAt Γ cp.a := (le_inf hKback hKfirst).trans_eq hbackInter
    have hsmall := Subgroup.card_le_of_le hKcenter
    change Nat.card (VAt Γ previous) ≤ 2*Nat.card K at hKcard
    change Nat.card (ZAt Γ cp.a)=4 at hfour
    rw [hpreviousCard] at hKcard
    rw [hfour] at hsmall
    omega
  have hpreCore : VAt Γ preterminal ≤ QAt Γ cp.a := by
    rw [VAt,v,Γ.vAt_def]
    apply sSup_le
    rintro center ⟨vertex,hvertex,rfl⟩
    have hstep := nine_eight_adjacent_distance_le Γ (target := cp.a)
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hvertex))
    have hpath := path_distance_le Γ cp 0 (cp.length-2) (Nat.zero_le _) (Nat.sub_le _ _)
    change Γ.distance (cp.path 0) preterminal ≤ cp.length-2-0 at hpath
    rw [cp.path_start,Nat.sub_zero,Γ.distance_symm cp.a preterminal] at hpath
    exact critical_minimality Γ cp (by omega)
  have hprePrevious : VAt Γ preterminal ≤ GAt Γ previous := hpreCore.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a previous
      hprevious default).2.2)
  have hRback : R ≤ VAt Γ previous := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hprePrevious.trans (stabilizer_le_normalizer_v Γ previous))
  have hbackPreterminal : VAt Γ previous ≤ GAt Γ preterminal :=
    (nine_eight_v_le_generated_neighborhood Γ hprevious).trans
      (nine_eight_neighborhood_le_preterminal ctx.toLocalContext hfourLong cp.a
        ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)))
  have hRpreterminal : R ≤ VAt Γ preterminal := by
    rw [show R=⁅VAt Γ previous,VAt Γ preterminal⁆ from rfl,Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hbackPreterminal.trans (stabilizer_le_normalizer_v Γ preterminal))
  have hRcentral : R ≤ Subgroup.centralizer (VAt Γ cp.a' : Set G) :=
    hRpreterminal.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (nine_nine_terminal_modules_commute ctx.toLocalContext hlong))
  have hRactor : ⁅R,Subgroup.zpowers t⁆ ≤ VAt Γ cp.firstStep :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hRcentral.trans (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr ht)))).le.trans bot_le
  have hRfirst := lemma_nine_four_ambient ctx hb third hdistance t htpair x hx R hRback hRactor hgen hdisplacement
  exact nine_six_nonzero_backward_commutator_impossible ctx hlong hquot hcard
    previous hprevious hpreviousNe hbackInter hRfirst hzero



/-- **Stellmacher (9.6).** The specified neighboring-module intersection has index two. -/
public theorem lemma_nine_six
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hb : 1 < ctx.criticalPath.length)
    (aPlus3 : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 aPlus3)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ aPlus3) 2 :=
  lemma_nine_six_ambient ctx.toAmbientContext hb aPlus3 hpath hquot


end Stellmacher.SectionNine
