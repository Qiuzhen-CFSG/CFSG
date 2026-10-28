module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalRankOne
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalLonger.SmallFixedSubgroup
public import Stellmacher.SectionNine.NineThreeGeometricCenterIntersections

/-!
# First center intersections in the cubic longer-distance argument

The geometric proof of Stellmacher (9.3)(2) uses ambient hypotheses only
through the center-order conclusion (9.2). Here the actual S₃ quotient
supplies that conclusion by the local fixed-index argument. Combining it
with the local small-fixed-subgroup extraction produces the first full
configuration, with its two literal center intersections and noncontainments.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.3)(2), p.49.
-/

namespace Stellmacher.SectionNine.LocalLonger
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
private theorem double_card_le_of_lt
    {G : Type u} [Group G] [Finite G] (K L : Subgroup G)
    (hle : K ≤ L) (hne : K ≠ L) : 2 * Nat.card K ≤ Nat.card L := by
  have hlt : Nat.card K < Nat.card L := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le hle)
    intro he
    exact hne (Subgroup.eq_of_le_of_card_ge hle he.ge)
  obtain ⟨n,hn⟩ := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hn2 : 2 ≤ n := by nlinarith
  nlinarith

public theorem geometric_center_intersections
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (u0 d l : ctx.Γ.Vertex)
    (hd : IsConjugateVertex ctx.Γ ctx.criticalPath.a' d)
    (hl : l ∈ neighborhood ctx.Γ d)
    (V E A0 : Subgroup G) (hVQ : V ≤ QAt ctx.Γ l)
    (actor : G) (haV : actor ∈ V) (haZ : actor ∈ ZAt ctx.Γ u0)
    (hZu : ZAt ctx.Γ u0 ≤ Subgroup.centralizer (QAt ctx.Γ u0 : Set G))
    (hZlQ : ZAt ctx.Γ l ≤ QAt ctx.Γ u0)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ l))
    (data : NineThreeGeometricData ctx.Γ d l V E A0 actor)
    (W : Subgroup G)
    (hWm : W ≤ ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l))
    (hWa : W ≤ QAt ctx.Γ u0)
    (hWl : W ≤ ZAt ctx.Γ l)
    (hbound : Nat.card ↥(ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ GAt ctx.Γ u0) ≤
      2 * Nat.card W) :
    let m := ctx.Γ.act data.x⁻¹ l
    ZAt ctx.Γ m ⊓ QAt ctx.Γ u0 = ZAt ctx.Γ m ⊓ ZAt ctx.Γ l ∧
      Nat.card ↥(ZAt ctx.Γ m ⊓ GAt ctx.Γ u0) ≤
        2 * Nat.card ↥(ZAt ctx.Γ m ⊓ QAt ctx.Γ u0) ∧
      ¬ ZAt ctx.Γ m ≤ GAt ctx.Γ u0 := by
  let Γ := ctx.Γ
  let m := Γ.act data.x⁻¹ l
  let Y := ZAt Γ m ⊓ GAt Γ u0
  let F := ZAt Γ m ⊓ QAt Γ u0
  let I := ZAt Γ m ⊓ ZAt Γ l
  have hQaGa : QAt Γ u0 ≤ GAt Γ u0 := by
    change q Γ u0 ≤ stabilizer Γ u0
    rw [q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hIF : I ≤ F := inf_le_inf_left _ hZlQ
  have hFY : F ≤ Y := inf_le_inf_left _ hQaGa
  have hWI : W ≤ I := le_inf hWm hWl
  have hYbound : Nat.card Y ≤ 2 * Nat.card I :=
    hbound.trans (Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le hWI))
  have hmrev : d ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
  have hZm : ZAt Γ m ≤ Subgroup.centralizer (QAt Γ m : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core m d hmrev).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hF_eq : F = I := by
    by_contra hne
    have hFbig := double_card_le_of_lt I F hIF (Ne.symm hne)
    have hFYeq : F = Y := Subgroup.eq_of_le_of_card_ge hFY (hYbound.trans hFbig)
    have hYQa : Y ≤ QAt Γ u0 := hFYeq ▸ (inf_le_right : F ≤ QAt Γ u0)
    have haY : actor ∈ Subgroup.centralizer (Y : Set G) :=
      Subgroup.centralizer_le hYQa (hZu haZ)
    have hAxY : V.conjBy data.x ≤ Subgroup.centralizer (Y : Set G) :=
      data.conjugate_core_le.trans ((Subgroup.le_centralizer_iff.mp hZm).trans
        (Subgroup.centralizer_le inf_le_left))
    have hEY : E ≤ Subgroup.centralizer (Y : Set G) := by
      rw [data.actor_generated actor haV data.actor_outside]
      exact sup_le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr haY)) hAxY
    have hYI : Y ≤ I := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      have hxE : data.x ∈ E := Subgroup.map_subtype_le _ data.residual_mem
      have hcomm := Subgroup.mem_centralizer_iff.mp (hEY hxE) z hz
      have hback : data.x⁻¹ * z * data.x = z := by
        rw [mul_assoc, hcomm]
        simp
      have hzConj : z ∈ (ZAt Γ l).conjBy data.x := by
        have hzM := hz.1
        change z ∈ CosetGraphContext.z Γ (Γ.act data.x⁻¹ l) at hzM
        rw [z_act,inv_inv] at hzM
        exact hzM
      have hzBack : data.x⁻¹ * z * data.x ∈ ZAt Γ l := by
        obtain ⟨t,ht,he⟩ := hzConj
        rw [← he]
        simpa [mul_assoc] using ht
      rwa [hback] at hzBack
    exact hne (le_antisymm (hFY.trans hYI) hIF)
  have hcardBound : Nat.card Y ≤ 2 * Nat.card F :=
    hbound.trans (Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le (le_inf hWm hWa)))
  have hmQa : ¬ ZAt Γ m ≤ QAt Γ u0 :=
    nine_three_geometric_extracted_center_not_le_core ctx.sectionSeven Γ u0 d l
      V E A0 actor haV haZ hZu data
  have hmGa : ¬ ZAt Γ m ≤ GAt Γ u0 := by
    intro hcontained
    have hYeq : Y = ZAt Γ m := inf_eq_left.mpr hcontained
    have hIne : I ≠ ZAt Γ m := by
      intro he
      exact hmQa (he ▸ (inf_le_right.trans hZlQ : I ≤ QAt Γ u0))
    have hlower := double_card_le_of_lt I (ZAt Γ m) inf_le_left hIne
    have hindexm : Nat.card (ZAt Γ m) = 2 * Nat.card I :=
      le_antisymm (hYeq ▸ hYbound) hlower
    have hmlcard : Nat.card (ZAt Γ m) = Nat.card (ZAt Γ l) := by
      change Nat.card (z Γ (Γ.act data.x⁻¹ l)) = _
      rw [z_act,inv_inv]
      exact Subgroup.card_map_of_injective (MulAut.conj data.x).injective
    have hindex : QuotientCardEq (ZAt Γ l) (ZAt Γ l ⊓ ZAt Γ m) 2 := by
      change Nat.card (ZAt Γ l) = 2 * Nat.card ↥(ZAt Γ l ⊓ ZAt Γ m)
      rw [← hmlcard, inf_comm]
      exact hindexm
    have hgenQ := geometric_extraction_core_edge_generation ctx.sectionSeven Γ d l
      V E A0 actor hVQ data
    have hnine := LocalCubic.nine_two ctx e d l m hd hl
      data.neighbor hindex hgenQ
    exact (ne_of_gt hlarge) hnine
  exact ⟨hF_eq,hcardBound,hmGa⟩

public theorem first_center_intersections
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (l : ctx.Γ.Vertex)
    (hl : l = ctx.criticalPath.path ⟨ctx.criticalPath.length-1, by omega⟩)
    (E A0 : Subgroup G) (actor : G)
    (haV : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (haZ : actor ∈ ZAt ctx.Γ ctx.criticalPath.a)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.a' l
      (VAt ctx.Γ ctx.criticalPath.firstStep) E A0 actor)
    (W : Subgroup G)
    (hWm : W ≤ ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l))
    (hWa : W ≤ QAt ctx.Γ ctx.criticalPath.a)
    (hWl : W ≤ ZAt ctx.Γ l)
    (hbound : Nat.card ↥(ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓
      GAt ctx.Γ ctx.criticalPath.a) ≤ 2 * Nat.card W) :
    let m := ctx.Γ.act data.x⁻¹ l
    ZAt ctx.Γ m ⊓ QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ m ⊓ ZAt ctx.Γ l ∧
      Nat.card ↥(ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a) ≤
        2 * Nat.card ↥(ZAt ctx.Γ m ⊓ QAt ctx.Γ ctx.criticalPath.a) ∧
      ¬ ZAt ctx.Γ m ≤ GAt ctx.Γ ctx.criticalPath.a ∧
      ¬ VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act data.x⁻¹ l
  have hlNeigh : l ∈ neighborhood Γ cp.a' := by
    rw [hl]
    exact (nine_three_initial_extraction_inputs ctx hb).1
  have hVQl : VAt Γ cp.firstStep ≤ QAt Γ l := by
    rw [hl]
    exact (nine_three_initial_extraction_inputs ctx hb).2.1
  have hlQa : ZAt Γ l ≤ QAt Γ cp.a := by
    apply critical_minimality Γ cp
    have hd := path_distance_le Γ cp 0 (cp.length-1) (by omega) (by omega)
    have hd' : Γ.distance cp.a l ≤ cp.length-1 := by
      have hs : cp.path ⟨0,by omega⟩ = cp.a := cp.path_start
      have he : l = cp.path ⟨cp.length-1,by omega⟩ := hl
      simpa only [Nat.sub_zero,hs,← he] using hd
    rw [Γ.distance_symm]
    exact lt_of_le_of_lt hd' (by have := cp.length_pos; omega)
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hZa : ZAt Γ cp.a ≤ Subgroup.centralizer (QAt Γ cp.a : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep hfirst).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hlaCard : Nat.card (ZAt Γ l) = Nat.card (ZAt Γ cp.a) := by
    obtain ⟨g,hg,_⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven Γ cp ctx.commutator_eq
    have he : Γ.act g cp.a = l := hg.trans hl.symm
    rw [← he]
    change Nat.card (z Γ (Γ.act g cp.a)) = _
    rw [z_act]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hlargeL : 4 < Nat.card (ZAt Γ l) := hlaCard.symm ▸ hlarge
  obtain ⟨hF_eq,hcardBound,hmGa⟩ := geometric_center_intersections ctx e
    cp.a cp.a' l ⟨1,Γ.act_one _⟩ hlNeigh (VAt Γ cp.firstStep) E A0 hVQl
    actor haV haZ hZa hlQa hlargeL data W hWm hWa hWl hbound
  refine ⟨hF_eq,hcardBound,hmGa,?_⟩
  intro hVcore
  apply hmGa
  have hZmV : ZAt Γ m ≤ VAt Γ cp.a' := by
    rw [VAt,v,Γ.vAt_def]
    exact le_sSup ⟨m,data.neighbor,rfl⟩
  exact hZmV.trans (hVcore.trans ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2.trans
    (cp.S_le_edge_stabilizers.trans inf_le_left)))

/-- The full first cubic extraction, including the literal center intersections. -/
public structure FirstConfigurationData
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) extends InitialExtractionData ctx where
  center_intersection :
    ZAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l) ⊓ QAt ctx.Γ ctx.criticalPath.a =
      ZAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l) ⊓ ZAt ctx.Γ l
  center_index : Nat.card
      (ZAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l) ⊓ GAt ctx.Γ ctx.criticalPath.a : Subgroup G) ≤
    2 * Nat.card
      (ZAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l) ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G)
  center_not_le : ¬ ZAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l) ≤ GAt ctx.Γ ctx.criticalPath.a
  terminal_module_not_le : ¬ VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep

/-- Cubic local data produce the first configuration of (9.3)(2). -/
public theorem exists_first_configuration
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a)) :
    Nonempty (FirstConfigurationData ctx) := by
  obtain ⟨d⟩ := exists_initial_extraction ctx hb
  have haV := (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1 d.actor_initial
  obtain ⟨hinter,hindex,hnot,hVend⟩ := first_center_intersections ctx e hb hlarge
    d.l d.penultimate d.E d.A0 d.actor haV d.actor_initial d.extraction
    d.W d.W_new_center d.W_initial_core d.W_old_center d.W_index
  exact ⟨{ toInitialExtractionData := d
           center_intersection := hinter
           center_index := hindex
           center_not_le := hnot
           terminal_module_not_le := hVend }⟩

end Stellmacher.SectionNine.LocalLonger
