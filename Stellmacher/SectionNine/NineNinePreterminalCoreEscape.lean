module
public import Stellmacher.SectionNine.NineNinePreterminalCenters

/-!
# Escape of the preterminal module from the preceding core in (9.9)

The preterminal V-module cannot be contained in the core at the preceding
neighbor. Such containment would put its commutator with the preceding module
in the preceding center line. The preceding module fixes the preterminal
vertex, so the same commutator lies in the preterminal module. The proved
center noncontainment and the line's order two force that commutator to vanish.
The full module-centralizer bound would then put the preceding module into the
preterminal core, contradicting the earlier stabilizer exclusion.

This supplies the last core escape before the actual (7.8) extraction in
Stellmacher (9.9), printed p.56/PDF p.46 of `refs/files/stellmacher-n-group.pdf`.
It retains the reversed terminal-core containment and the intersection-index
lower bound explicitly and uses no unfinished numbered theorem.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_preterminal_module_not_le_previous_core
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
    ¬ VAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤ QAt ctx.Γ previous := by
  intro hcontained
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let preterminal := cp.path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let B := VAt Γ previous
  let V := VAt Γ preterminal
  let Z := ZAt Γ previous
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  obtain ⟨support, hsupport, hcomm, hcontrol⟩ :=
    nine_nine_support_of_terminal_core ctx hshort hcore
  let data : NineNineSupportData ctx.toLocalContext hb := {
    terminal_core := hcore
    support := support
    support_le := hsupport
    support_commutator := hcomm
    centralizer_commutator := hcontrol
    previous := previous
    previous_neighbor := hprevious
    previous_ne := hne
    maximal_eq := nine_nine_maximal_eq_intersection ctx hb support (hsupport.trans hcore)
      hcomm previous hprevious hne
    large_index := hlarge }
  have hBpre : B ≤ GAt Γ preterminal :=
    nine_nine_previous_le_preterminal_stabilizer ctx.toLocalContext hb data
  have hBnot : ¬ B ≤ QAt Γ preterminal :=
    nine_nine_previous_not_le_preterminal_core ctx hb hcore previous hprevious hne hlarge
  obtain ⟨mover, hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
  have hpreviousOrbit : IsConjugateVertex Γ cp.firstStep previous := ⟨mover, hmover⟩
  have hdata := nine_next_center_commutator_and_kernel ctx hshort previous hpreviousOrbit
  have hcommZ : ⁅B,V⁆ ≤ Z :=
    (Subgroup.commutator_mono le_rfl hcontained).trans_eq hdata.2.1
  have hcommV : ⁅B,V⁆ ≤ V := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hBpre.trans (stabilizer_le_normalizer_v Γ preterminal))
  have hnoncontain : ¬ Z ≤ V :=
    nine_nine_previous_center_not_le_preterminal_module ctx hb hcore previous hprevious hne
  have hcommZero : ⁅B,V⁆ = ⊥ := by
    by_contra hnot
    have hcard := (Subgroup.one_lt_card_iff_ne_bot _).mpr hnot
    have hcardZ := hdata.1
    have heq : ⁅B,V⁆ = Z := Subgroup.eq_of_le_of_card_ge hcommZ (by
      change Nat.card Z = 2 at hcardZ
      omega)
    exact hnoncontain (heq ▸ hcommV)
  have hpreOrbit : IsConjugateVertex Γ cp.firstStep preterminal :=
    nine_five_penultimate_neighbor_orbit ctx.toLocalContext preterminal
      (Γ.adjacent_symm (nine_five_previous_adjacent_penultimate ctx.toLocalContext hshort
        preterminal ⟨⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩, rfl, rfl⟩))
  exact hBnot ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommZero).trans
    (nine_three_module_centralizer_core_at_vertex ctx preterminal hpreOrbit))

end Stellmacher.SectionNine
