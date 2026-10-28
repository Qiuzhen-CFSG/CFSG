module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalLonger.SecondConfiguration

/-!
# Repeating the cubic extraction at the second neighbor

The actual second extraction has the same small fixed subgroup and center
intersection properties as the first. Endpoint alignment and reverse-path
critical minimality supply its geometric inputs. The local fixed-subgroup
argument supplies the two-core containment without an ambient centralizer
hypothesis; the literal S₃ quotient supplies the local rank-one estimate.

This is the repeated argument in Stellmacher (9.3), Journal of Algebra
190 (1997), p.49, immediately after relation (3). Both chosen extractions
are retained and no global Hypothesis Two is used.
-/

namespace Stellmacher.SectionNine.LocalLonger
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem second_center_inputs
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length)
    (first : FirstConfigurationData ctx)
    (second : SecondConfigurationData ctx first) :
    let Γ := ctx.Γ
    let cp := ctx.criticalPath
    let m := Γ.act first.extraction.x⁻¹ first.l
    let l := second.l
    IsConjugateVertex Γ cp.a m ∧
      IsConjugateVertex Γ cp.a' cp.firstStep ∧
      l ∈ Neighborhood Γ cp.firstStep ∧
      ZAt Γ l ≤ QAt Γ m ∧
      Nat.card (ZAt Γ l) = Nat.card (ZAt Γ cp.a) ∧
      ZAt Γ m ≤ Subgroup.centralizer (QAt Γ m : Set G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  let l := second.l
  change IsConjugateVertex Γ cp.a m ∧ _
  have hbLocal : 1 < cp.length := hb
  obtain ⟨g, hga, hgnext⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hgm : Γ.act (g * first.extraction.x⁻¹) cp.a = m := by
    rw [Γ.act_mul, hga, ← first.penultimate]
  have hback : Γ.act g⁻¹ cp.a' = cp.firstStep := by
    rw [← hgnext, ← Γ.act_mul, mul_inv_cancel, Γ.act_one]
  have hl : l ∈ Neighborhood Γ cp.firstStep := by
    obtain ⟨bound, heq⟩ := second.second
    change second.l ∈ Neighborhood Γ cp.firstStep
    rw [heq]
    exact (nine_three_second_extraction_inputs ctx hb).1
  have hm : m ∈ neighborhood Γ cp.a' := first.extraction.neighbor
  have hZlQm : ZAt Γ l ≤ QAt Γ m := by
    apply critical_minimality Γ cp
    rw [Γ.distance_symm]
    have hmadj : Γ.adjacent m cp.a' :=
      Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hm)
    have hd := neighbor_reverse_path_distance_le Γ cp m 2 cp.length
      (by omega) le_rfl (by simpa [cp.path_end] using hmadj)
    obtain ⟨bound, heq⟩ := second.second
    change Γ.distance m second.l < cp.length
    rw [heq]
    exact lt_of_le_of_lt hd (by omega)
  have haNeighbor : cp.a ∈ neighborhood Γ cp.firstStep :=
    (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    cp.firstStep haNeighbor hl
  have hcard : Nat.card (ZAt Γ l) = Nat.card (ZAt Γ cp.a) := by
    change Nat.card (z Γ l) = Nat.card (z Γ cp.a)
    rw [← hactor, z_act, Subgroup.card_map_of_injective (MulAut.conj (actor : G)⁻¹).injective]
  have htermNeighbor : cp.a' ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hm))
  have hcentral : ZAt Γ m ≤ Subgroup.centralizer (QAt Γ m : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core m cp.a' htermNeighbor).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  exact ⟨⟨g * first.extraction.x⁻¹, hgm⟩, ⟨g⁻¹, hback⟩,
    hl, hZlQm, hcard, hcentral⟩

public theorem second_small_fixed_subgroup
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length)
    (first : FirstConfigurationData ctx)
    (second : SecondConfigurationData ctx first) :
    let m := ctx.Γ.act first.extraction.x⁻¹ first.l
    let n := ctx.Γ.act second.extraction.x⁻¹ second.l
    ∃ W : Subgroup G, W ≤ ZAt ctx.Γ n ∧ W ≤ QAt ctx.Γ m ∧
      W ≤ ZAt ctx.Γ second.l ∧
      Nat.card (ZAt ctx.Γ n ⊓ GAt ctx.Γ m : Subgroup G) ≤ 2 * Nat.card W ∧
      second.E ≤ Subgroup.centralizer (W : Set G) ∧
      ¬ ZAt ctx.Γ m ⊓ Subgroup.centralizer (W : Set G) ≤ GAt ctx.Γ n := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  let n := Γ.act second.extraction.x⁻¹ second.l
  let Y := ZAt Γ n ⊓ GAt Γ m
  have hmorbit : IsConjugateVertex Γ cp.a m := by
    obtain ⟨g,hg,_⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven Γ cp ctx.commutator_eq
    refine ⟨g * first.extraction.x⁻¹, ?_⟩
    rw [Γ.act_mul,hg,← first.penultimate]
  have hZmV : ZAt Γ m ≤ VAt Γ cp.a' := by
    change z Γ m ≤ v Γ cp.a'
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨m,first.extraction.neighbor,rfl⟩
  have hZnV : ZAt Γ n ≤ VAt Γ cp.firstStep := by
    change z Γ n ≤ v Γ cp.firstStep
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨n,second.extraction.neighbor,rfl⟩
  have hYV : Y ≤ VAt Γ cp.firstStep := inf_le_left.trans hZnV
  have hquad : ⁅⁅ZAt Γ m,Y⁆,Y⁆ = ⊥ := by
    have hq := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb
    exact bot_unique ((Subgroup.commutator_mono
      (Subgroup.commutator_mono hZmV hYV) hYV).trans_eq hq.2.1)
  exact geometric_small_fixed_subgroup ctx m cp.firstStep second.l
    hmorbit (VAt Γ cp.a') second.E second.A0 second.actor second.actor_first_center hZmV
    second.extraction hquad

public theorem second_center_relations
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
    ZAt ctx.Γ n ⊓ QAt ctx.Γ m = ZAt ctx.Γ n ⊓ ZAt ctx.Γ second.l ∧
      Nat.card (ZAt ctx.Γ n ⊓ GAt ctx.Γ m : Subgroup G) ≤
        2 * Nat.card (ZAt ctx.Γ n ⊓ QAt ctx.Γ m : Subgroup G) ∧
      ¬ ZAt ctx.Γ n ≤ GAt ctx.Γ m := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  obtain ⟨hmorbit,hd,hl,hZlQ,hcard,hZmC⟩ := second_center_inputs ctx hb first second
  have hVQ : VAt Γ cp.a' ≤ QAt Γ second.l := by
    obtain ⟨hsecond,hsecondEq⟩ := second.second
    rw [hsecondEq]
    exact (nine_three_second_extraction_inputs ctx hb).2.1
  have hZmV : ZAt Γ m ≤ VAt Γ cp.a' := by
    change z Γ m ≤ v Γ cp.a'
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨m,first.extraction.neighbor,rfl⟩
  have hlargeL : 4 < Nat.card (ZAt Γ second.l) := by rw [hcard]; exact hlarge
  obtain ⟨W,hWn,hWm,hWl,hbound,hEC,hescape⟩ :=
    second_small_fixed_subgroup ctx hb first second
  exact geometric_center_intersections ctx e m cp.firstStep second.l hd hl
    (VAt Γ cp.a') second.E second.A0 hVQ second.actor (hZmV second.actor_first_center)
    second.actor_first_center hZmC hZlQ hlargeL second.extraction W hWn hWm hWl hbound

end Stellmacher.SectionNine.LocalLonger
