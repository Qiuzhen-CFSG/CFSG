module
public import Stellmacher.SectionNine.NineNinePreterminalExtraction
public import Stellmacher.SectionEight.EightFourSourceNineCommutingCore

/-!
# A preterminal neighbor center centralizes the preceding-module coatom

Every center at a preterminal neighbor lies in the initial core by critical
minimality, and hence stabilizes the preceding vertex. The preceding module
also fixes the preterminal vertex. Its intersection with the neighbor
stabilizer therefore normalizes both the neighbor's center plane and the
preterminal line, of respective orders four and two. Their commutator lies
in that line, and also in the preceding module by the first containment.
If the line is not contained in the module, this commutator is trivial.

These are the containment and coatom-centralization inputs to the actual
transvection selected after (7.8) in Stellmacher (9.9), printed p.56/PDF p.46
of `refs/files/stellmacher-n-group.pdf`. The center noncontainment is an
explicit input furnished by the nearby (9.8) transport.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_preterminal_neighbor_centralizes_coatom
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ Neighborhood ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩))
    (hnot : ¬ ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤ VAt ctx.Γ previous) :
    ZAt ctx.Γ neighbor ≤ GAt ctx.Γ previous ∧
      ⁅ZAt ctx.Γ neighbor, VAt ctx.Γ previous ⊓ GAt ctx.Γ neighbor⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let preterminal := cp.path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let V := VAt Γ previous
  let I := V ⊓ GAt Γ neighbor
  let Z := ZAt Γ preterminal
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hlong : 4 < cp.length := by
    have hh := nine_ten_length_ge_five ctx.toLocalContext hb
    change 5 ≤ cp.length at hh
    omega
  have hpreAdj := nine_five_previous_adjacent_penultimate ctx.toLocalContext hshort preterminal
    ⟨⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩, rfl, rfl⟩
  obtain ⟨alignment, halign, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  obtain ⟨mover, hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    preterminal ((mem_neighborhood_iff_adjacent Γ).mpr hpreAdj) hneighbor
  change Γ.act (mover:G) penultimate = neighbor at hmover
  have hneighborOrbit : IsConjugateVertex Γ cp.a neighbor :=
    ⟨alignment * (mover:G), by rw [Γ.act_mul,halign]; exact hmover⟩
  have hpreOrbit : IsConjugateVertex Γ cp.firstStep preterminal :=
    nine_five_penultimate_neighbor_orbit ctx.toLocalContext preterminal (Γ.adjacent_symm hpreAdj)
  have hfour := (lemma_nine_three_ambient ctx hshort neighbor hneighborOrbit).2
  have htwo := (nine_next_center_commutator_and_kernel ctx hshort preterminal hpreOrbit).1
  have hreverse : preterminal ∈ Neighborhood Γ neighbor := (mem_neighborhood_iff_adjacent Γ).mpr
    (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor))
  have hline : Z ≤ ZAt Γ neighbor := ((nine_seven_center_join ctx neighbor hneighborOrbit).2
    preterminal hreverse).2
  have hindex : Z.relIndex (ZAt Γ neighbor) = 2 := by
    have hmul := (Z.subgroupOf (ZAt Γ neighbor)).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hline).toEquiv, hfour] at hmul
    change Nat.card Z = 2 at htwo
    rw [htwo] at hmul
    change Z.relIndex (ZAt Γ neighbor) * 2 = 4 at hmul
    omega
  have hVpre : V ≤ GAt Γ preterminal :=
    (nine_eight_v_le_generated_neighborhood Γ hprevious).trans
      (nine_eight_neighborhood_le_preterminal ctx.toLocalContext hlong cp.a
        ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)))
  have hcommLine : ⁅ZAt Γ neighbor,I⁆ ≤ Z :=
    Stellmacher.SectionEight.commutator_le_of_normalizing_index_two _ _ _ hindex
      (inf_le_right.trans (stabilizer_le_normalizer_z Γ neighbor))
      ((inf_le_left.trans hVpre).trans (stabilizer_le_normalizer_z Γ preterminal))
  have hZQa : ZAt Γ neighbor ≤ QAt Γ cp.a := by
    have hpath := path_distance_le Γ cp 0 (cp.length - 2) (by omega) (Nat.sub_le _ _)
    change Γ.distance (cp.path 0) preterminal ≤ cp.length - 2 - 0 at hpath
    rw [cp.path_start, Nat.sub_zero] at hpath
    have hstep := nine_eight_adjacent_distance_le Γ
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)) (target := cp.a)
    rw [Γ.distance_symm preterminal cp.a] at hstep
    apply critical_minimality Γ cp
    omega
  have hQaPrev : QAt Γ cp.a ≤ GAt Γ previous :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a previous hprevious default).2.2
  have hZprev : ZAt Γ neighbor ≤ GAt Γ previous := hZQa.trans hQaPrev
  refine ⟨hZprev, ?_⟩
  have hcommV : ⁅ZAt Γ neighbor,I⁆ ≤ V := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hZprev.trans (stabilizer_le_normalizer_v Γ previous)))
  by_contra hnonzero
  change ⁅ZAt Γ neighbor,I⁆ ≠ ⊥ at hnonzero
  have hpositive := (Subgroup.one_lt_card_iff_ne_bot _).mpr hnonzero
  have heq : ⁅ZAt Γ neighbor,I⁆ = Z := Subgroup.eq_of_le_of_card_ge hcommLine (by
    change Nat.card Z = 2 at htwo
    omega)
  change ¬ Z ≤ V at hnot
  exact hnot (heq ▸ hcommV)

end Stellmacher.SectionNine
