module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalLonger.NormalizedGeometry
public import Theory.GroupTheory.IndexTwoIntersectionLine

/-!
# All mixed-center relations for the two cubic extractions

Retargeting the first extraction to the second neighbor preserves its
actual conjugator and group. Local fixed-subgroup extraction and the cubic
rank-one estimate prove both center-intersection identities. Restricting
the two geometric coatoms gives both outer indices; a second application
of the rank-one estimate gives the two inner indices. The mixed commutator
lies in all four centers and is centralized by both extracted groups.

These are the full local relations through Stellmacher (9.3)(4), Journal
of Algebra 190 (1997), p.49. No ambient normalizer, centralizer, P-star or
subnormality premise is introduced.
-/
namespace Stellmacher.SectionNine.LocalLonger
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u


/-- The first geometric extraction satisfies its center relations again at
the second extracted neighbor, with the original witnesses retained. -/
public theorem first_relations_at_second_neighbor
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : FirstConfigurationData ctx)
    (second : SecondConfigurationData ctx first) :
    let m := ctx.Γ.act first.extraction.x⁻¹ first.l
    let n := ctx.Γ.act second.extraction.x⁻¹ second.l
    ZAt ctx.Γ m ⊓ QAt ctx.Γ n = ZAt ctx.Γ m ⊓ ZAt ctx.Γ first.l ∧
      Nat.card (ZAt ctx.Γ m ⊓ GAt ctx.Γ n : Subgroup G) ≤
        2 * Nat.card (ZAt ctx.Γ m ⊓ QAt ctx.Γ n : Subgroup G) ∧
      ¬ ZAt ctx.Γ m ≤ GAt ctx.Γ n := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  let n := Γ.act second.extraction.x⁻¹ second.l
  let V := VAt Γ cp.firstStep
  have hbLocal : 1 < cp.length := hb
  have hn : n ∈ neighborhood Γ cp.firstStep := second.extraction.neighbor
  have ha : cp.a ∈ neighborhood Γ cp.firstStep :=
    (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  have hnorbit : IsConjugateVertex Γ cp.a n := by
    obtain ⟨g, hg⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
      cp.firstStep ha hn
    exact ⟨g, hg⟩
  have hZnV : ZAt Γ n ≤ V := by
    change z Γ n ≤ v Γ cp.firstStep
    rw [v, Γ.vAt_def]
    exact le_sSup ⟨n, hn, rfl⟩
  have hZmV : ZAt Γ m ≤ VAt Γ cp.a' := by
    change z Γ m ≤ v Γ cp.a'
    rw [v, Γ.vAt_def]
    exact le_sSup ⟨m, first.extraction.neighbor, rfl⟩
  have hZnnot : ¬ ZAt Γ n ≤ GAt Γ m :=
    (second_center_relations ctx e hb hlarge first second).2.2
  obtain ⟨actor, haZn, haNot⟩ := Set.not_subset.mp hZnnot
  let data : NineThreeGeometricData Γ cp.a' first.l V first.E first.A0 actor :=
    { first.extraction with actor_outside := haNot }
  have hnback : cp.firstStep ∈ neighborhood Γ n :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hn))
  have hquad : ⁅⁅ZAt Γ n, ZAt Γ m ⊓ GAt Γ n⁆, ZAt Γ m ⊓ GAt Γ n⁆ = ⊥ := by
    have hlong := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb
    have hYV : ZAt Γ m ⊓ GAt Γ n ≤ VAt Γ cp.a' := inf_le_left.trans hZmV
    exact bot_unique ((Subgroup.commutator_mono
      (Subgroup.commutator_mono hZnV hYV) hYV).trans_eq hlong.2.2)
  obtain ⟨W, hWm, hWn, hWl, hbound, _, _⟩ :=
    geometric_small_fixed_subgroup ctx n cp.a' first.l hnorbit
      V first.E first.A0 actor haZn hZnV data hquad
  have hl : first.l ∈ neighborhood Γ cp.a' := by
    rw [first.penultimate]
    exact (nine_three_initial_extraction_inputs ctx hb).1
  have hVQ : V ≤ QAt Γ first.l := by
    rw [first.penultimate]
    exact (nine_three_initial_extraction_inputs ctx hb).2.1
  have hZlQn : ZAt Γ first.l ≤ QAt Γ n := by
    apply critical_minimality Γ cp
    rw [Γ.distance_symm, first.penultimate]
    have hnadj : Γ.adjacent n cp.firstStep :=
      Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hn)
    have hd := neighbor_path_distance_le Γ cp n 1 (cp.length - 1)
      (by omega) (by omega) (by simpa [cp.path_first] using hnadj)
    exact lt_of_le_of_lt hd (by omega)
  have hZnC : ZAt Γ n ≤ Subgroup.centralizer (QAt Γ n : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core n cp.firstStep hnback).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hcardL : Nat.card (ZAt Γ first.l) = Nat.card (ZAt Γ cp.a) := by
    obtain ⟨g, hg, _⟩ := lemma_seven_five_endpoint_alignment
      ctx.sectionSeven Γ cp ctx.commutator_eq
    have hgl : Γ.act g cp.a = first.l := hg.trans first.penultimate.symm
    rw [← hgl]
    change Nat.card (z Γ (Γ.act g cp.a)) = _
    rw [z_act]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hlargeL : 4 < Nat.card (ZAt Γ first.l) := by rw [hcardL]; exact hlarge
  exact geometric_center_intersections ctx e n cp.a' first.l
    ⟨1, Γ.act_one _⟩ hl V first.E first.A0 hVQ actor (hZnV haZn) haZn hZnC
    hZlQn hlargeL data W hWm hWn hWl hbound



private theorem center_core_bounds
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B) (Γ : CosetGraphContext G T A B)
    (d l : Γ.Vertex) (hl : l ∈ neighborhood Γ d) :
    ZAt Γ d ≤ QAt Γ d ∧ ZAt Γ d ≤ Subgroup.centralizer (QAt Γ d : Set G) := by
  have hZ := ((lemma_seven_three h Γ).center_core d l hl).trans
    (omegaOneCenter_le_centerAmbient _)
  exact ⟨hZ.trans (Subgroup.map_subtype_le _), hZ.trans (centerAmbient_le_centralizer _)⟩

private theorem extraction_centralizes_common_centers
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B) (Γ : CosetGraphContext G T A B)
    (d l : Γ.Vertex) (hl : l ∈ neighborhood Γ d)
    (V E A0 : Subgroup G) (actor : G) (hVQ : V ≤ QAt Γ l)
    (data : NineThreeGeometricData Γ d l V E A0 actor)
    (R : Subgroup G) (hRl : R ≤ ZAt Γ l)
    (hRm : R ≤ ZAt Γ (Γ.act data.x⁻¹ l)) :
    E ≤ Subgroup.centralizer (R : Set G) := by
  have hlback : d ∈ neighborhood Γ l :=
    (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hl))
  have hmback : d ∈ neighborhood Γ (Γ.act data.x⁻¹ l) :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
  have hCl := (center_core_bounds h Γ l d hlback).2
  have hCm := (center_core_bounds h Γ _ d hmback).2
  rw [data.generated]
  exact sup_le (hVQ.trans ((Subgroup.le_centralizer_iff.mp hCl).trans
      (Subgroup.centralizer_le hRl)))
    (data.conjugate_core_le.trans ((Subgroup.le_centralizer_iff.mp hCm).trans
      (Subgroup.centralizer_le hRm)))

public theorem pair_center_commutator
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : FirstConfigurationData ctx)
    (second : SecondConfigurationData ctx first) :
    let m := ctx.Γ.act first.extraction.x⁻¹ first.l
    let n := ctx.Γ.act second.extraction.x⁻¹ second.l
    let R := ⁅ZAt ctx.Γ n ⊓ GAt ctx.Γ m, ZAt ctx.Γ m ⊓ GAt ctx.Γ n⁆
    R ≤ ZAt ctx.Γ n ⊓ ZAt ctx.Γ second.l ⊓ ZAt ctx.Γ m ⊓ ZAt ctx.Γ first.l ∧
      first.E ⊔ second.E ≤ Subgroup.centralizer (R : Set G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  let n := Γ.act second.extraction.x⁻¹ second.l
  let R := ⁅ZAt Γ n ⊓ GAt Γ m, ZAt Γ m ⊓ GAt Γ n⁆
  have hRn : R ≤ ZAt Γ n :=
    (Subgroup.commutator_mono inf_le_left (le_refl _)).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (inf_le_right.trans (stabilizer_le_normalizer_z Γ n)))
  have hRm : R ≤ ZAt Γ m :=
    (Subgroup.commutator_mono (le_refl _) inf_le_left).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (inf_le_right.trans (stabilizer_le_normalizer_z Γ m)))
  have hmback : cp.a' ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp first.extraction.neighbor))
  have hnback : cp.firstStep ∈ neighborhood Γ n :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp second.extraction.neighbor))
  have hRQm := hRm.trans (center_core_bounds ctx.sectionSeven Γ m cp.a' hmback).1
  have hRQn := hRn.trans (center_core_bounds ctx.sectionSeven Γ n cp.firstStep hnback).1
  have hRsecond : R ≤ ZAt Γ second.l := by
    have hh := le_inf hRn hRQm
    rw [(second_center_relations ctx e hb hlarge first second).1] at hh
    exact hh.trans inf_le_right
  have hRfirst : R ≤ ZAt Γ first.l := by
    have hh := le_inf hRm hRQn
    rw [(first_relations_at_second_neighbor ctx e hb hlarge first second).1] at hh
    exact hh.trans inf_le_right
  refine ⟨le_inf (le_inf (le_inf hRn hRsecond) hRm) hRfirst, sup_le ?_ ?_⟩
  · have hl : first.l ∈ neighborhood Γ cp.a' := by
      rw [first.penultimate]
      exact (nine_three_initial_extraction_inputs ctx hb).1
    have hVQ : VAt Γ cp.firstStep ≤ QAt Γ first.l := by
      rw [first.penultimate]
      exact (nine_three_initial_extraction_inputs ctx hb).2.1
    exact extraction_centralizes_common_centers ctx.sectionSeven Γ cp.a' first.l hl
      _ first.E first.A0 first.actor hVQ first.extraction R hRfirst hRm
  · have hl : second.l ∈ neighborhood Γ cp.firstStep := by
      obtain ⟨hsecond,he⟩ := second.second
      rw [he]
      exact (nine_three_second_extraction_inputs ctx hb).1
    have hVQ : VAt Γ cp.a' ≤ QAt Γ second.l := by
      obtain ⟨hsecond,he⟩ := second.second
      rw [he]
      exact (nine_three_second_extraction_inputs ctx hb).2.1
    exact extraction_centralizes_common_centers ctx.sectionSeven Γ cp.firstStep second.l hl
      _ second.E second.A0 second.actor hVQ second.extraction R hRsecond hRn


private theorem card_intersection_of_index_two
    {G : Type u} [Group G] [Finite G] (V K Z : Subgroup G)
    (hZV : Z ≤ V) (hVcard : Nat.card V = 2 * Nat.card (V ⊓ K : Subgroup G))
    (hnot : ¬ Z ≤ K) : Nat.card Z = 2 * Nat.card (Z ⊓ K : Subgroup G) := by
  have hcard := ((V ⊓ K).subgroupOf V).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show V ⊓ K ≤ V from inf_le_left)).toEquiv] at hcard
  change (V ⊓ K).relIndex V * Nat.card (V ⊓ K : Subgroup G) = Nat.card V at hcard
  have hi : K.relIndex V = 2 := by
    rw [Subgroup.inf_relIndex_left] at hcard
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hcard.trans hVcard)
  have hni : ¬ Z.subgroupOf V ≤ K.subgroupOf V := by
    intro hle
    exact hnot fun z hz => hle (show (⟨z,hZV hz⟩ : V) ∈ Z.subgroupOf V from hz)
  have hZindex := Subgroup.subgroupOf_index_eq_two (K.subgroupOf V) (Z.subgroupOf V) hi hni
  change (K.subgroupOf V).relIndex (Z.subgroupOf V) = 2 at hZindex
  rw [Subgroup.relIndex_subgroupOf hZV] at hZindex
  have hZcard := ((Z ⊓ K).subgroupOf Z).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show Z ⊓ K ≤ Z from inf_le_left)).toEquiv] at hZcard
  change (Z ⊓ K).relIndex Z * Nat.card (Z ⊓ K : Subgroup G) = Nat.card Z at hZcard
  rw [Subgroup.inf_relIndex_left,hZindex] at hZcard
  exact hZcard.symm

public theorem mutual_outer_indices
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : FirstConfigurationData ctx)
    (second : SecondConfigurationData ctx first) :
    let m := ctx.Γ.act first.extraction.x⁻¹ first.l
    let n := ctx.Γ.act second.extraction.x⁻¹ second.l
    Nat.card (ZAt ctx.Γ n) = 2 * Nat.card (ZAt ctx.Γ n ⊓ GAt ctx.Γ m : Subgroup G) ∧
      Nat.card (ZAt ctx.Γ m) = 2 * Nat.card (ZAt ctx.Γ m ⊓ GAt ctx.Γ n : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  let n := Γ.act second.extraction.x⁻¹ second.l
  have hZnV : ZAt Γ n ≤ VAt Γ cp.firstStep := by
    change z Γ n ≤ v Γ cp.firstStep
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨n,second.extraction.neighbor,rfl⟩
  have hZmV : ZAt Γ m ≤ VAt Γ cp.a' := by
    change z Γ m ≤ v Γ cp.a'
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨m,first.extraction.neighbor,rfl⟩
  have hVfirst : Nat.card (VAt Γ cp.firstStep) =
      2 * Nat.card (VAt Γ cp.firstStep ⊓ GAt Γ m : Subgroup G) := by
    rw [← first.extraction.coatom_eq]
    exact first.extraction.coatom_card
  have hVend : Nat.card (VAt Γ cp.a') =
      2 * Nat.card (VAt Γ cp.a' ⊓ GAt Γ n : Subgroup G) := by
    rw [← second.extraction.coatom_eq]
    exact second.extraction.coatom_card
  have hnnot : ¬ ZAt Γ n ≤ GAt Γ m :=
    (second_center_relations ctx e hb hlarge first second).2.2
  have hmnot : ¬ ZAt Γ m ≤ GAt Γ n := fun hle =>
    second.extraction.actor_outside (hle second.actor_first_center)
  exact ⟨card_intersection_of_index_two _ _ _ hZnV hVfirst hnnot,
    card_intersection_of_index_two _ _ _ hZmV hVend hmnot⟩



public theorem geometric_center_index_four
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (d l : ctx.Γ.Vertex)
    (hd : IsConjugateVertex ctx.Γ ctx.criticalPath.a' d)
    (hl : l ∈ neighborhood ctx.Γ d)
    (V E A0 : Subgroup G) (hVQ : V ≤ QAt ctx.Γ l)
    (actor : G) (data : NineThreeGeometricData ctx.Γ d l V E A0 actor)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ l))
    (Y : Subgroup G)
    (hIY : ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ ZAt ctx.Γ l ≤ Y)
    (_hYm : Y ≤ ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l))
    (hdouble : Nat.card (ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l)) = 2 * Nat.card Y)
    (hbound : Nat.card Y ≤ 2 * Nat.card ↥(ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ ZAt ctx.Γ l)) :
    Nat.card Y = 2 * Nat.card ↥(ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ ZAt ctx.Γ l) ∧
      Nat.card (ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l)) =
        4 * Nat.card ↥(ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ ZAt ctx.Γ l) := by
  let Γ := ctx.Γ
  let m := Γ.act data.x⁻¹ l
  let I := ZAt Γ m ⊓ ZAt Γ l
  have hmlcard : Nat.card (ZAt Γ m) = Nat.card (ZAt Γ l) := by
    change Nat.card (z Γ (Γ.act data.x⁻¹ l)) = _
    rw [z_act,inv_inv]
    exact Subgroup.card_map_of_injective (MulAut.conj data.x).injective
  have hne : I ≠ Y := by
    intro he
    have hindex : QuotientCardEq (ZAt Γ l) (ZAt Γ l ⊓ ZAt Γ m) 2 := by
      change Nat.card (ZAt Γ l) = 2 * Nat.card ↥(ZAt Γ l ⊓ ZAt Γ m)
      rw [← hmlcard,inf_comm]
      exact hdouble.trans (congrArg (fun U : Subgroup G => 2 * Nat.card U) he.symm)
    have hgen := geometric_extraction_core_edge_generation ctx.sectionSeven Γ d l
      V E A0 actor hVQ data
    have hnine := LocalCubic.nine_two ctx e d l m hd hl data.neighbor hindex hgen
    exact (ne_of_gt hlarge) hnine
  have hlt : Nat.card I < Nat.card Y := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le hIY)
    intro he
    exact hne (Subgroup.eq_of_le_of_card_ge hIY he.ge)
  obtain ⟨n,hn⟩ := Subgroup.card_dvd_of_le hIY
  have hpos : 0 < Nat.card I := Nat.card_pos
  have hn2 : 2 ≤ n := by nlinarith
  have hlow : 2 * Nat.card I ≤ Nat.card Y := by nlinarith
  have hY : Nat.card Y = 2 * Nat.card I := le_antisymm hbound hlow
  refine ⟨hY,?_⟩
  calc
    Nat.card (ZAt Γ m) = 2 * Nat.card Y := hdouble
    _ = 2 * (2 * Nat.card I) := by rw [hY]
    _ = 4 * Nat.card I := by omega


public theorem four_center_indices
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : FirstConfigurationData ctx)
    (second : SecondConfigurationData ctx first) :
    let m := ctx.Γ.act first.extraction.x⁻¹ first.l
    let n := ctx.Γ.act second.extraction.x⁻¹ second.l
    Nat.card (ZAt ctx.Γ m) = 2 * Nat.card (ZAt ctx.Γ m ⊓ GAt ctx.Γ n : Subgroup G) ∧
      Nat.card (ZAt ctx.Γ m ⊓ GAt ctx.Γ n : Subgroup G) =
        2 * Nat.card (ZAt ctx.Γ m ⊓ ZAt ctx.Γ first.l : Subgroup G) ∧
      Nat.card (ZAt ctx.Γ n) = 2 * Nat.card (ZAt ctx.Γ n ⊓ GAt ctx.Γ m : Subgroup G) ∧
      Nat.card (ZAt ctx.Γ n ⊓ GAt ctx.Γ m : Subgroup G) =
        2 * Nat.card (ZAt ctx.Γ n ⊓ ZAt ctx.Γ second.l : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  let n := Γ.act second.extraction.x⁻¹ second.l
  have houter := mutual_outer_indices ctx e hb hlarge first second
  have hfirst := first_relations_at_second_neighbor ctx e hb hlarge first second
  have hsecond := second_center_relations ctx e hb hlarge first second
  have hcore (v : Γ.Vertex) : QAt Γ v ≤ GAt Γ v := by
    change q Γ v ≤ stabilizer Γ v
    rw [q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hI1Y : ZAt Γ m ⊓ ZAt Γ first.l ≤ ZAt Γ m ⊓ GAt Γ n := by
    rw [← hfirst.1]
    exact inf_le_inf_left _ (hcore n)
  have hI2Y : ZAt Γ n ⊓ ZAt Γ second.l ≤ ZAt Γ n ⊓ GAt Γ m := by
    rw [← hsecond.1]
    exact inf_le_inf_left _ (hcore m)
  have hl : first.l ∈ neighborhood Γ cp.a' := by
    rw [first.penultimate]
    exact (nine_three_initial_extraction_inputs ctx hb).1
  have hVfirst : VAt Γ cp.firstStep ≤ QAt Γ first.l := by
    rw [first.penultimate]
    exact (nine_three_initial_extraction_inputs ctx hb).2.1
  have hlargeL : 4 < Nat.card (ZAt Γ first.l) := by
    obtain ⟨g,hg,_⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven Γ cp ctx.commutator_eq
    have he : Γ.act g cp.a = first.l := hg.trans first.penultimate.symm
    rw [← he]
    change 4 < Nat.card (z Γ (Γ.act g cp.a))
    rw [z_act,Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hlarge
  have hbound1 : Nat.card (ZAt Γ m ⊓ GAt Γ n : Subgroup G) ≤
      2 * Nat.card (ZAt Γ m ⊓ ZAt Γ first.l : Subgroup G) := by
    rw [← hfirst.1]
    exact hfirst.2.1
  have hi1 := geometric_center_index_four ctx e cp.a' first.l
    ⟨1,Γ.act_one _⟩ hl (VAt Γ cp.firstStep) first.E first.A0 hVfirst first.actor
    first.extraction hlargeL (ZAt Γ m ⊓ GAt Γ n) hI1Y inf_le_left houter.2 hbound1
  obtain ⟨_,hd,hr,_,hcardR,_⟩ := second_center_inputs ctx hb first second
  have hVend : VAt Γ cp.a' ≤ QAt Γ second.l := by
    obtain ⟨_,he⟩ := second.second
    rw [he]
    exact (nine_three_second_extraction_inputs ctx hb).2.1
  have hlargeR : 4 < Nat.card (ZAt Γ second.l) := by rw [hcardR]; exact hlarge
  have hbound2 : Nat.card (ZAt Γ n ⊓ GAt Γ m : Subgroup G) ≤
      2 * Nat.card (ZAt Γ n ⊓ ZAt Γ second.l : Subgroup G) := by
    rw [← hsecond.1]
    exact hsecond.2.1
  have hi2 := geometric_center_index_four ctx e cp.firstStep second.l hd hr
    (VAt Γ cp.a') second.E second.A0 hVend second.actor second.extraction hlargeR
    (ZAt Γ n ⊓ GAt Γ m) hI2Y inf_le_left houter.1 hbound2
  exact ⟨houter.2,hi1.1,houter.1,hi2.1⟩

end Stellmacher.SectionNine.LocalLonger
