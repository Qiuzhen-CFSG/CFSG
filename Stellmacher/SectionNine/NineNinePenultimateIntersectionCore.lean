module
public import Stellmacher.SectionNine.NineNinePreterminalCenters
public import Stellmacher.SectionNine.NineNineTerminalInputs
public import Stellmacher.SectionNine.NineFivePreviousCommutation
public import Stellmacher.SectionNine.NineThreeOrbitEdgeCoreCentralizer
public import Stellmacher.SectionEight.EightFourSourceNineCommutingCore

/-!
# The penultimate stabilizer intersection lies in the core

The preceding module's intersection with the penultimate stabilizer lies in
that vertex's two-core. The intersection-index conclusion is not assumed.
It suffices that the preterminal center is excluded from the preceding module,
as already proved from the explicit distance-bound and large-index inputs.

The intersection normalizes the penultimate centerplane and its preterminal
line. Their index two bounds the commutator by that line. Critical minimality
also puts the plane in the initial core, hence in the preceding stabilizer,
so the same commutator lies in the preceding module. The excluded line of
order two forces it to vanish. The proved centralizer theorem for two-groups
at an initial-orbit vertex then places the intersection in the two-core.

Source: Stellmacher (9.9), printed pp.56--57/PDF pp.46--47 of
`refs/files/stellmacher-n-group.pdf`, the core containment in the last sentence
on p.56. This is independent of the later normalizer index computation.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_penultimate_intersection_le_core
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
    VAt ctx.Γ previous ⊓ GAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤
      QAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let B := VAt Γ previous
  let I := B ⊓ GAt Γ penultimate
  let plane := ZAt Γ penultimate
  let line := ZAt Γ preterminal
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  obtain ⟨alignment,halign,_⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpenOrbit : IsConjugateVertex Γ cp.a penultimate := ⟨alignment,halign⟩
  have hpreAdj := Γ.adjacent_symm (nine_five_previous_adjacent_penultimate
    ctx.toLocalContext hshort preterminal
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩)
  have hpreOrbit := nine_five_penultimate_neighbor_orbit ctx.toLocalContext preterminal hpreAdj
  have hplaneCard := (lemma_nine_three_ambient ctx hshort penultimate hpenOrbit).2
  have hlineCard := (nine_next_center_commutator_and_kernel ctx hshort preterminal hpreOrbit).1
  change Nat.card line=2 at hlineCard
  change Nat.card plane=4 at hplaneCard
  have hlinePlane : line ≤ plane :=
    ((nine_seven_center_join ctx penultimate hpenOrbit).2 preterminal
      ((mem_neighborhood_iff_adjacent Γ).mpr hpreAdj)).2
  have hindex : line.relIndex plane=2 := by
    have hcount := (line.subgroupOf plane).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hlinePlane).toEquiv] at hcount
    change line.relIndex plane * Nat.card line=Nat.card plane at hcount
    rw [hlineCard,hplaneCard] at hcount
    omega
  have hIB : I≤B := inf_le_left
  have hIG : I≤GAt Γ penultimate := inf_le_right
  have hBpre : B≤GAt Γ preterminal := by
    have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    have hlong : 4 < cp.length := by
      obtain ⟨n,hn⟩ := hodd
      change 3 < cp.length at hb
      omega
    exact (nine_eight_v_le_generated_neighborhood Γ hprevious).trans
      (nine_eight_neighborhood_le_preterminal ctx.toLocalContext hlong cp.a
        ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)))
  have hcommLine : ⁅plane,I⁆ ≤ line := SectionEight.commutator_le_of_normalizing_index_two
    plane line I hindex (hIG.trans (stabilizer_le_normalizer_z Γ penultimate))
      ((hIB.trans hBpre).trans (stabilizer_le_normalizer_z Γ preterminal))
  have hplaneQa : plane≤QAt Γ cp.a := by
    apply critical_minimality Γ cp
    rw [Γ.distance_symm]
    have hd := path_distance_le Γ cp 0 (cp.length-1) (by omega) (Nat.sub_le _ _)
    have hstrict : cp.length-1<cp.length := by omega
    have hd' : Γ.distance cp.a penultimate≤cp.length-1 := by
      change Γ.distance (cp.path 0) penultimate≤cp.length-1-0 at hd
      simpa only [cp.path_start,Nat.sub_zero] using hd
    exact hd'.trans_lt hstrict
  have hQaPrevious : QAt Γ cp.a≤GAt Γ previous :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a previous hprevious default).2.2
  have hcommB : ⁅plane,I⁆ ≤ B := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hIB le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((hplaneQa.trans hQaPrevious).trans (stabilizer_le_normalizer_v Γ previous)))
  have hlineNot : ¬ line≤B := nine_nine_preterminal_center_not_le_previous_module
    bound ctx hb hcore previous hprevious hne hlarge
  have hcommZero : ⁅plane,I⁆=⊥ := by
    by_contra hnonzero
    have hcard := (Subgroup.one_lt_card_iff_ne_bot _).mpr hnonzero
    have heq : ⁅plane,I⁆=line := Subgroup.eq_of_le_of_card_ge hcommLine (by omega)
    exact hlineNot (heq ▸ hcommB)
  have htwo : IsPGroup 2 B := by
    obtain ⟨mover,hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
    change IsPGroup 2 (v Γ previous)
    rw [← hmover,v_act]
    let _ := ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
    exact (IsElementaryAbelian.isPGroup 2 (v Γ cp.firstStep)).map _
  apply nine_three_orbit_pgroup_centralizer ctx.toLocalContext penultimate hpenOrbit
    I (htwo.to_le hIB) hIG
  rw [Subgroup.commutator_comm] at hcommZero
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommZero

end Stellmacher.SectionNine
