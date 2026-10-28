module

public import Stellmacher.SectionNine.NineSixCenterCoreTransfer
public import Stellmacher.SectionNine.NineNineTerminalInputs
public import Stellmacher.SectionNine.NineThreeCenterSplitting
public import Stellmacher.SectionNine.NineSevenLongDistanceSetup

/-!
# The nonzero backward commutator contradiction in (9.6)

In the order-sixteen SL₂(2) branch at critical distance greater than three,
let a distinct initial neighbor have module intersection equal to the initial
center. If its nontrivial commutator with the preterminal module lies in the
first module, the original critical pair is contradicted. The containment
in the first module is explicitly retained for its separate (9.4) consumer.

Short distances put the preterminal module in the initial core. The given
intersection bounds the commutator by the initial center, so the center-core
transfer puts the preterminal module in the backward vertex's core. Its
nontrivial commutator is therefore the order-two backward center. The
neighborhood bound puts the backward module in the preterminal stabilizer;
the commutator then lies in the preterminal module and centralizes the
terminal module. The first-step center also centralizes that module, while
these two lines generate the initial center, contradicting the nontrivial
critical commutator.

Source: Stellmacher (9.6), printed p.53 / PDF p.43 of
`refs/files/stellmacher-n-group.pdf`, the final nonzero-R₀ paragraph. The
proved neighborhood and module-commutation bounds work for every b>3, so
this proof does not rely on the source's additional phrase “i.e. b>5”.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_six_nonzero_backward_commutator_impossible
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=16)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep)
    (hinter : VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep=
      ZAt ctx.Γ ctx.criticalPath.a)
    (hcomm : ⁅VAt ctx.Γ previous,VAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)⁆ ≤
        VAt ctx.Γ ctx.criticalPath.firstStep)
    (hnontrivial : ⁅VAt ctx.Γ previous,VAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)⁆ ≠ ⊥) : False := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let actors := VAt Γ preterminal
  let backward := VAt Γ previous
  let R := ⁅backward,actors⁆
  have hshort : 1 < cp.length := by change 3 < cp.length at hb;omega
  have hlong : 4 < cp.length := by
    obtain ⟨k,hk⟩ := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    change 3 < cp.length at hb
    omega
  have hactorsQa : actors ≤ QAt Γ cp.a := by
    rw [show actors=VAt Γ preterminal from rfl,VAt,v,Γ.vAt_def]
    apply sSup_le
    rintro center ⟨vertex,hvertex,rfl⟩
    have hstep := nine_eight_adjacent_distance_le Γ (target := cp.a)
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hvertex))
    have hpath := path_distance_le Γ cp 0 (cp.length-2) (Nat.zero_le _) (Nat.sub_le _ _)
    change Γ.distance (cp.path 0) preterminal ≤ cp.length-2-0 at hpath
    rw [cp.path_start,Nat.sub_zero,Γ.distance_symm cp.a preterminal] at hpath
    exact critical_minimality Γ cp (by omega)
  have hactorsGprevious : actors ≤ GAt Γ previous := hactorsQa.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a previous
      hprevious default).2.2)
  have hRback : R ≤ backward := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hactorsGprevious.trans (stabilizer_le_normalizer_v Γ previous))
  have hRZa : R ≤ ZAt Γ cp.a := (le_inf hRback hcomm).trans_eq hinter
  have hactorsQprevious : actors ≤ QAt Γ previous :=
    nine_six_center_commutator_forces_neighbor_core ctx hshort hquot hcard
      previous hprevious actors hactorsQa hRZa
  have hfour := (lemma_nine_three_ambient ctx hshort cp.a ⟨1,Γ.act_one _⟩).2
  obtain ⟨mover,hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
  have hpreviousData := nine_next_center_and_commutator_of_initial_four ctx.toLocalContext
    hfour previous ⟨mover,hmover⟩
  have hRline : R ≤ ZAt Γ previous :=
    (Subgroup.commutator_mono le_rfl hactorsQprevious).trans_eq hpreviousData.2
  have hpreviousCard : Nat.card (ZAt Γ previous)=2 := hpreviousData.1
  have hR : R=ZAt Γ previous := Subgroup.eq_of_le_of_card_ge hRline (by
    rw [hpreviousCard]
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hnontrivial)
  have hbackPreterminal : backward ≤ GAt Γ preterminal :=
    (nine_eight_v_le_generated_neighborhood Γ hprevious).trans
      (nine_eight_neighborhood_le_preterminal ctx.toLocalContext hlong cp.a
        ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)))
  have hRpreterminal : R ≤ actors := by
    rw [show R=⁅backward,actors⁆ from rfl,Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hbackPreterminal.trans (stabilizer_le_normalizer_v Γ preterminal))
  have hpreviousCentral : ZAt Γ previous ≤ Subgroup.centralizer (VAt Γ cp.a' : Set G) :=
    hR.ge.trans (hRpreterminal.trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (nine_nine_terminal_modules_commute ctx.toLocalContext hb)))
  have hfirstCentral : ZAt Γ cp.firstStep ≤
      Subgroup.centralizer (VAt Γ cp.a' : Set G) := by
    change z Γ cp.firstStep ≤ _
    rw [(lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center.2]
    exact (omegaOneCenter_le_centerAmbient _).trans ((centerAmbient_le_centralizer _).trans
      (Subgroup.centralizer_le
        (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2))
  have hsplit := (nine_three_center_split ctx hshort (left := previous)
    ⟨1,Γ.act_one _⟩ ((mem_neighborhood_iff_adjacent Γ).mp hprevious) cp.firstStep_adj hne).1
  have hcentral : ZAt Γ cp.a ≤ Subgroup.centralizer (VAt Γ cp.a' : Set G) := by
    rw [hsplit]
    exact sup_le hpreviousCentral hfirstCentral
  exact nine_seven_terminal_initial_commutator_ne_bot ctx
    (by rw [Subgroup.commutator_comm];exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral)

end Stellmacher.SectionNine
