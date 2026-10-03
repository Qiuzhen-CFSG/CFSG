module
public import Stellmacher.SectionNine.NineNinePenultimateStabilizerExclusion
public import Stellmacher.SectionNine.NineEightNearbyCoreContainment

/-!
# The two center exclusions at the preterminal vertex in (9.9)

The proved escape of the preceding module from the preterminal core implies
that the preterminal center cannot lie in it: the two vertices are at distance
less than the critical length, so the nearby version of (9.8) would give core
containment. This first result retains the ambient (9.8) bound explicitly.

Conversely, the preceding center cannot lie in the preterminal module. The
latter commutes with the terminal module. Since the initial center splits
as the preceding center and the first-step line, and that line lies in the
selected support, such containment would centralize the support and contradict
its nontrivial initial-center commutator. This second exclusion needs neither
(9.8) nor the index-four hypothesis.

Source: Stellmacher (9.9), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`, following the penultimate-stabilizer
exclusion and preceding the extraction at the preterminal vertex.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_preterminal_center_not_le_previous_module
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (bound : ∀ shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B,
      ZAt shifted.Γ shifted.criticalPath.a' ≤
        VAt shifted.Γ shifted.criticalPath.firstStep → shifted.criticalPath.length ≤ 3)
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card (VAt ctx.Γ previous ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤ Nat.card (VAt ctx.Γ previous)) :
    ¬ ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤ VAt ctx.Γ previous := by
  intro hcontain
  apply nine_nine_previous_not_le_preterminal_core ctx hb hcore previous hprevious hne hlarge
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let preterminal := cp.path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hd0 : Γ.distance cp.a preterminal ≤ cp.length - 2 := by
    have hpath := path_distance_le Γ cp 0 (cp.length - 2) (by omega) (Nat.sub_le _ _)
    change Γ.distance (cp.path 0) preterminal ≤ cp.length - 2 - 0 at hpath
    simpa only [cp.path_start, Nat.sub_zero] using hpath
  have hd1 := nine_eight_adjacent_distance_le Γ
    (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hprevious))
    (target := preterminal)
  change Γ.distance previous preterminal ≤ Γ.distance cp.a preterminal + 1 at hd1
  have hd : Γ.distance previous preterminal < cp.length := by
    change 3 < cp.length at hb
    omega
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
  let _ : IsElementaryAbelian 2 (VAt Γ previous) := by
    change IsElementaryAbelian 2 (v Γ previous)
    rw [← hactor, v_act]
    let _ : IsElementaryAbelian 2 (v Γ cp.firstStep) :=
      ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case
        (by change 3 < cp.length at hb; omega)).1
    exact IsElementaryAbelian.map (MulAut.conj (actor : G)⁻¹).toMonoidHom
  exact nine_eight_nearby_core_of_center_containment bound ctx hb
    previous preterminal hd inferInstance hcontain

public theorem nine_nine_previous_center_not_le_preterminal_module
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep) :
    ¬ ZAt ctx.Γ previous ≤ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  intro hcontained
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let terminal := VAt Γ cp.a'
  let first := ZAt Γ cp.firstStep
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  obtain ⟨support, hsupport, _, _, hfirstSupport, hcomm, _⟩ :=
    nine_nine_support_data_with_line_of_terminal_core ctx hshort hcore
  have hpreviousComm : ⁅ZAt Γ previous, support⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hcontained hsupport).trans_eq
      (nine_nine_terminal_modules_commute ctx.toLocalContext hb)
  let _ : IsElementaryAbelian 2 terminal :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hshort).2.2.1
  have hfirstComm : ⁅first,support⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((hfirstSupport.trans hsupport).trans
        ((Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
          (Subgroup.centralizer_le hsupport)))
  have hsplit := (nine_three_center_split ctx hshort (left := previous)
    ⟨1, Γ.act_one _⟩ ((mem_neighborhood_iff_adjacent Γ).mp hprevious)
    cp.firstStep_adj hne).1
  have hzero : ⁅ZAt Γ cp.a,support⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    rw [hsplit]
    exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hpreviousComm)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hfirstComm)
  have hfour := (lemma_nine_three_ambient ctx hshort cp.a ⟨1, Γ.act_one _⟩).2
  have htwo := nine_next_center_order_of_initial_four ctx.toLocalContext hfour
  rw [Subgroup.commutator_comm] at hzero
  rw [hcomm] at hzero
  have hbot : first = ⊥ := hzero
  change Nat.card first = 2 at htwo
  rw [hbot, Subgroup.card_bot] at htwo
  omega

end Stellmacher.SectionNine
