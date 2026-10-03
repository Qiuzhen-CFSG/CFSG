module
public import Stellmacher.SectionNine.NineNinePreterminalCoreEscape
public import Stellmacher.SectionNine.NineEightInitialExtraction

/-!
# The actual preterminal extraction in (9.9)

The preceding module lies in the core at offset b-3 by critical minimality,
but escapes the core at offset b-2 by the earlier stabilizer exclusion. It is
elementary abelian, so its Frattini subgroup is trivial. The proved prescribed-
actor portion of (7.8) and its geometric conversion produce a genuine neighbor
of the preterminal vertex whose stabilizer intersects the module with index
two. The same witnesses retain generation of the preterminal stabilizer by
the new edge and the original module.

The extracted center acts nontrivially on the module: otherwise that generation
would force the whole preterminal stabilizer to normalize the neighboring
center, contradicting the edge normality obstruction. All selected groups and
the coatom come from the same geometric witness.

Source: Stellmacher (9.9), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`, the application of (7.8) before assertion
(3). The reversed core containment and intersection-index lower bound remain
explicit inputs from (9.8) and (9.7).
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_preterminal_extracted_neighbor
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
    let preterminal := ctx.criticalPath.path ⟨ctx.criticalPath.length - 2,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    ∃ neighbor : ctx.Γ.Vertex,
      neighbor ∈ Neighborhood ctx.Γ preterminal ∧
      QuotientCardEq (VAt ctx.Γ previous)
        (VAt ctx.Γ previous ⊓ GAt ctx.Γ neighbor) 2 ∧
      (GAt ctx.Γ preterminal ⊓ GAt ctx.Γ neighbor) ⊔ VAt ctx.Γ previous =
        GAt ctx.Γ preterminal ∧
      ⁅ZAt ctx.Γ neighbor, VAt ctx.Γ previous⁆ ≠ ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let preterminal := cp.path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let seed := cp.path ⟨cp.length - 3, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let V := VAt Γ previous
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hlong : 4 < cp.length := by
    have hh := nine_ten_length_ge_five ctx.toLocalContext hb
    change 5 ≤ cp.length at hh
    omega
  have hseed : seed ∈ Neighborhood Γ preterminal := by
    apply (mem_neighborhood_iff_adjacent Γ).mpr
    apply Γ.adjacent_symm
    have hedge := cp.path_adj ⟨cp.length - 3, by omega⟩
    convert hedge using 1 <;> apply congrArg cp.path <;> apply Fin.ext <;> simp
    omega
  have hVseed : V ≤ QAt Γ seed := by
    change v Γ previous ≤ q Γ seed
    rw [v, Γ.vAt_def]
    apply sSup_le
    rintro Z ⟨neighbor, hneighbor, rfl⟩
    have hpath := path_distance_le Γ cp 0 (cp.length - 3) (by omega) (Nat.sub_le _ _)
    change Γ.distance (cp.path 0) seed ≤ cp.length - 3 - 0 at hpath
    rw [cp.path_start, Nat.sub_zero] at hpath
    have hprev := nine_eight_adjacent_distance_le Γ
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hprevious)) (target := seed)
    change Γ.distance previous seed ≤ Γ.distance cp.a seed + 1 at hprev
    have hneighborDist := nine_eight_adjacent_distance_le Γ
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)) (target := seed)
    exact critical_minimality Γ cp (by omega)
  have hVnot : ¬ V ≤ QAt Γ preterminal :=
    nine_nine_previous_not_le_preterminal_core ctx hb hcore previous hprevious hne hlarge
  obtain ⟨mover, hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
  let _ : IsElementaryAbelian 2 V := by
    change IsElementaryAbelian 2 (v Γ previous)
    rw [← hmover, v_act]
    let _ : IsElementaryAbelian 2 (v Γ cp.firstStep) :=
      ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
    exact IsElementaryAbelian.map (MulAut.conj (mover : G)⁻¹).toMonoidHom
  let _ : Fact (IsPGroup 2 V) := ⟨IsElementaryAbelian.isPGroup 2 V⟩
  have hPhi : frattiniAmbient V ≤ QAt Γ preterminal := by
    rw [frattiniAmbient, frattini_eq_bot_of_isElementaryAbelian (R := V) (p := 2),
      Subgroup.map_bot]
    exact bot_le
  obtain ⟨actor, hactorV, hactorNot⟩ := SetLike.not_le_iff_exists.mp hVnot
  obtain ⟨conjugator, A0, E, hEP, _, h0V, hgen, hcard, hconjE, _, h0core,
      hedge, hmodel, _, hby, _, hactor0⟩ :=
    sevenEight_quotient_configuration_with_actor ctx.sectionSeven Γ preterminal seed hseed
      V hVseed hVnot hPhi actor hactorV hactorNot
  obtain ⟨data⟩ := nine_three_geometric_extraction ctx.sectionSeven Γ preterminal seed hseed
    V E A0 hVseed hPhi actor hactorV hactor0 conjugator hconjE hEP hgen h0V hcard
      h0core hedge hmodel hby
  let neighbor := Γ.act data.x⁻¹ seed
  have hedgeGen := nine_ten_geometric_edge_generation ctx.sectionSeven Γ preterminal seed V E A0 actor data
  refine ⟨neighbor, data.neighbor, ?_, hedgeGen, ?_⟩
  · change Nat.card V = 2 * Nat.card (V ⊓ GAt Γ neighbor : Subgroup G)
    rw [← data.coatom_eq]
    exact data.coatom_card
  · intro hcomm
    apply neighbor_center_not_normalized ctx.sectionSeven Γ preterminal neighbor data.neighbor
    change GAt Γ preterminal ≤ Subgroup.normalizer (ZAt Γ neighbor : Set G)
    rw [← hedgeGen]
    rw [Subgroup.commutator_comm] at hcomm
    exact sup_le (inf_le_right.trans (stabilizer_le_normalizer_z Γ neighbor))
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (Subgroup.centralizer_le_normalizer _))

end Stellmacher.SectionNine
