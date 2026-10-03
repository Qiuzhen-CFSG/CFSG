module

public import Stellmacher.SectionNine.CubicCoreIntersection
public import Stellmacher.SectionNine.GeneratedContext

/-!
# Shifted intersections in Stellmacher (9.7)

The cubic quotient action transports ordered pairs of distinct neighbors.
The index-two intersection of the initial order-eight module therefore
transports to every two-edge path whose middle vertex is in the initial
orbit: the intersection is exactly the middle order-four center.

At an order-eight module vertex, distinct neighbors have distinct order-four
centers. A separate finite-order calculation identifies the intersection of
two such centers once a common order-two subgroup is known. The seven-edge
specialization proves the actual intersection at offsets three and five,
including the required nonbacktracking and middle-orbit arguments.

These are upstream intersection facts, not a proof that the actual critical
commutator has order two or lies in either center, and not an exclusion of
distance seven. Source: Stellmacher, printed p.53 / PDF p.43, (9.7), in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

variable {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}

private theorem action_injective (Γ : CosetGraphContext G S P1 P2) (actor : G) :
    Function.Injective (Γ.act actor) := by
  intro left right heq
  have hinv := congrArg (Γ.act actor⁻¹) heq
  simpa only [← Γ.act_mul, mul_inv_cancel, Γ.act_one] using hinv

public theorem nine_seven_neighbor_center_le_module
    (Γ : CosetGraphContext G S P1 P2) {middle neighbor : Γ.Vertex}
    (hadj : Γ.adjacent middle neighbor) : ZAt Γ neighbor ≤ VAt Γ middle := by
  change z Γ neighbor ≤ v Γ middle
  rw [v, Γ.vAt_def]
  exact le_sSup ⟨neighbor, (mem_neighborhood_iff_adjacent Γ).mpr hadj, rfl⟩

public theorem nine_seven_two_arc_transport
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2)
    {left middle right targetLeft targetMiddle targetRight : Γ.Vertex}
    (hleft : Γ.adjacent middle left) (hright : Γ.adjacent middle right)
    (hdistinct : left ≠ right)
    (htargetLeft : Γ.adjacent targetMiddle targetLeft)
    (htargetRight : Γ.adjacent targetMiddle targetRight)
    (htargetDistinct : targetLeft ≠ targetRight)
    (horbit : IsConjugateVertex Γ middle targetMiddle)
    (hmodel : QuotientIsModel (GAt Γ targetMiddle) (QAt Γ targetMiddle) SL2Two) :
    ∃ actor : G, Γ.act actor left = targetLeft ∧
      Γ.act actor middle = targetMiddle ∧ Γ.act actor right = targetRight := by
  obtain ⟨first, hfirst⟩ := horbit
  have hfirstLeft := adjacent_act Γ first hleft
  rw [hfirst] at hfirstLeft
  obtain ⟨second, hsecond⟩ := (lemma_seven_one h7 Γ).local_transitivity targetMiddle
    ((mem_neighborhood_iff_adjacent Γ).mpr hfirstLeft)
    ((mem_neighborhood_iff_adjacent Γ).mpr htargetLeft)
  have hsecondFix : Γ.act (second : G) targetMiddle = targetMiddle :=
    (Set.ext_iff.mp (Γ.stabilizer_def targetMiddle) (second : G)).mp second.property
  let combined := first * (second : G)
  have hprefixMiddle : Γ.act combined middle = targetMiddle := by
    rw [Γ.act_mul, hfirst, hsecondFix]
  have hprefixLeft : Γ.act combined left = targetLeft := by
    rw [Γ.act_mul]
    exact hsecond
  have hprefixRight := adjacent_act Γ combined hright
  rw [hprefixMiddle] at hprefixRight
  have hprefixDistinct : Γ.act combined right ≠ targetLeft := by
    intro heq
    exact hdistinct ((action_injective Γ combined) (hprefixLeft.trans heq.symm))
  have htrans := (cubic_local_action_of_sl2Two_quotient Γ h7 targetMiddle hmodel).punctured_transitivity targetLeft htargetLeft
      (GAt Γ targetMiddle ⊓ GAt Γ targetLeft) le_rfl
      (edge_stabilizer_outside_core h7 Γ htargetLeft hmodel)
  obtain ⟨third, hthird⟩ := htrans
    ⟨(mem_neighborhood_iff_adjacent Γ).mpr hprefixRight, hprefixDistinct⟩
    ⟨(mem_neighborhood_iff_adjacent Γ).mpr htargetRight, htargetDistinct.symm⟩
  have hthirdMiddle : Γ.act (third : G) targetMiddle = targetMiddle :=
    (Set.ext_iff.mp (Γ.stabilizer_def targetMiddle) (third : G)).mp third.property.1
  have hthirdLeft : Γ.act (third : G) targetLeft = targetLeft :=
    (Set.ext_iff.mp (Γ.stabilizer_def targetLeft) (third : G)).mp third.property.2
  refine ⟨combined * (third : G), ?_, ?_, ?_⟩
  · rw [Γ.act_mul, hprefixLeft, hthirdLeft]
  · rw [Γ.act_mul, hprefixMiddle, hthirdMiddle]
  · rw [Γ.act_mul]
    exact hthird

public theorem nine_seven_shifted_module_intersection
    (ctx : SectionNineLocalContext G S P1 P2)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2)
    (hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2^3)
    (hstartData : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two ∧
        Nat.card (ZAt ctx.Γ vertex) = 4)
    {left middle right : ctx.Γ.Vertex}
    (hmiddle : IsConjugateVertex ctx.Γ ctx.criticalPath.a middle)
    (hleft : ctx.Γ.adjacent middle left) (hright : ctx.Γ.adjacent middle right)
    (hdistinct : left ≠ right) :
    VAt ctx.Γ left ⊓ VAt ctx.Γ right = ZAt ctx.Γ middle := by
  obtain ⟨index, hindexVal, rfl⟩ := hpath
  have hlength : 3 ≤ ctx.criticalPath.length := by omega
  let second := ctx.criticalPath.path ⟨2, by omega⟩
  have hfirstAdj : ctx.Γ.adjacent second ctx.criticalPath.firstStep := by
    have hedge := ctx.criticalPath.path_adj ⟨1, by omega⟩
    change ctx.Γ.adjacent (ctx.criticalPath.path ⟨1, by omega⟩) second at hedge
    rw [ctx.criticalPath.path_first] at hedge
    exact ctx.Γ.adjacent_symm hedge
  have hthirdAdj : ctx.Γ.adjacent second (ctx.criticalPath.path index) := by
    have hedge := ctx.criticalPath.path_adj ⟨2, by omega⟩
    have heq : (⟨2, by omega⟩ : Fin ctx.criticalPath.length).succ = index :=
      Fin.ext hindexVal.symm
    rwa [heq] at hedge
  obtain ⟨secondMover, hsecondMover⟩ :=
    (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity ctx.criticalPath.firstStep
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr
        (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj))
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hfirstAdj))
  have hsecondOrbit : IsConjugateVertex ctx.Γ ctx.criticalPath.a second :=
    ⟨secondMover, hsecondMover⟩
  have hsecondCard := (hstartData second hsecondOrbit).2
  have hcommonCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ (ctx.criticalPath.path index) : Subgroup G) = 4 := by
    change Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2 * _ at hindex
    rw [hfirstCard] at hindex
    omega
  have hfirstDistinct : ctx.criticalPath.firstStep ≠ ctx.criticalPath.path index := by
    intro heq
    rw [← heq, inf_idem, hfirstCard] at hcommonCard
    norm_num at hcommonCard
  have hcommon : VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ (ctx.criticalPath.path index) = ZAt ctx.Γ second := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
      (le_inf (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirstAdj))
        (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hthirdAdj)))
    exact hcommonCard.le.trans hsecondCard.ge
  obtain ⟨middleMover, hmiddleMover⟩ := hmiddle
  have horbit : IsConjugateVertex ctx.Γ second middle := by
    refine ⟨(secondMover : G)⁻¹ * middleMover, ?_⟩
    have hinverse : ctx.Γ.act (secondMover : G)⁻¹ second = ctx.criticalPath.a := by
      rw [← hsecondMover, ← ctx.Γ.act_mul, mul_inv_cancel, ctx.Γ.act_one]
    rw [ctx.Γ.act_mul, hinverse, hmiddleMover]
  obtain ⟨actor, hactorLeft, hactorMiddle, hactorRight⟩ :=
    nine_seven_two_arc_transport ctx.sectionSeven ctx.Γ hfirstAdj hthirdAdj
      hfirstDistinct hleft hright hdistinct horbit
      (hstartData middle ⟨middleMover, hmiddleMover⟩).1
  have hmap := congrArg
    (fun subgroup : Subgroup G => subgroup.map (MulAut.conj actor⁻¹).toMonoidHom) hcommon
  rw [Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective] at hmap
  change (v ctx.Γ ctx.criticalPath.firstStep).map _ ⊓
    (v ctx.Γ (ctx.criticalPath.path index)).map _ = (z ctx.Γ second).map _ at hmap
  rw [← v_act, ← v_act, ← z_act, hactorLeft, hactorRight, hactorMiddle] at hmap
  exact hmap

public theorem nine_seven_neighbor_centers_distinct
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2)
    {left middle right : Γ.Vertex}
    (hmodel : QuotientIsModel (GAt Γ middle) (QAt Γ middle) SL2Two)
    (hmoduleCard : Nat.card (VAt Γ middle) = 8)
    (hcenterCard : Nat.card (ZAt Γ left) = 4)
    (hleft : Γ.adjacent middle left) (hright : Γ.adjacent middle right)
    (hdistinct : left ≠ right) : ZAt Γ left ≠ ZAt Γ right := by
  intro hequal
  have hall (neighbor : Γ.Vertex) (hneighbor : Γ.adjacent middle neighbor) :
      ZAt Γ neighbor = ZAt Γ left := by
    by_cases heq : left = neighbor
    · rw [← heq]
    obtain ⟨actor, hactorLeft, _, hactorRight⟩ := nine_seven_two_arc_transport
      h7 Γ hleft hright hdistinct hleft hneighbor heq ⟨1, Γ.act_one middle⟩ hmodel
    have hmap := congrArg
      (fun subgroup : Subgroup G => subgroup.map (MulAut.conj actor⁻¹).toMonoidHom) hequal
    change (z Γ left).map _ = (z Γ right).map _ at hmap
    rw [← z_act, ← z_act, hactorLeft, hactorRight] at hmap
    exact hmap.symm
  have hmodule : VAt Γ middle = ZAt Γ left := by
    apply le_antisymm
    · change v Γ middle ≤ ZAt Γ left
      rw [v, Γ.vAt_def]
      apply sSup_le
      rintro subgroup ⟨neighbor, hneighbor, rfl⟩
      exact (hall neighbor ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)).le
    · exact nine_seven_neighbor_center_le_module Γ hleft
  rw [hmodule, hcenterCard] at hmoduleCard
  omega

public theorem nine_seven_distinct_planes_inf_eq_line
    {left right line : Subgroup G}
    (hleftCard : Nat.card left = 4) (hrightCard : Nat.card right = 4)
    (hdistinct : left ≠ right) (hlineCard : Nat.card line = 2)
    (hline : line ≤ left ⊓ right) : left ⊓ right = line := by
  have hproper : left ⊓ right ≠ left := by
    intro heq
    exact hdistinct (Subgroup.eq_of_le_of_card_ge
      (heq.ge.trans inf_le_right) (hrightCard.le.trans hleftCard.ge))
  have hcardlt : Nat.card (left ⊓ right : Subgroup G) < Nat.card left := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_left)
    intro heq
    exact hproper (Subgroup.eq_of_le_of_card_ge inf_le_left heq.ge)
  obtain ⟨factor, hfactor⟩ := Subgroup.card_dvd_of_le
    (show left ⊓ right ≤ left from inf_le_left)
  have hfactorTwo : 2 ≤ factor := by nlinarith
  have hbound : Nat.card (left ⊓ right : Subgroup G) ≤ 2 := by
    rw [hleftCard] at hfactor
    nlinarith
  exact (Subgroup.eq_of_le_of_card_ge hline (hbound.trans hlineCard.ge)).symm

public theorem nine_seven_length_seven_middle_intersection
    (ctx : SectionNineLocalContext G S P1 P2)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2)
    (hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2^3)
    (hstartData : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two ∧
        Nat.card (ZAt ctx.Γ vertex) = 4)
    (hseven : ctx.criticalPath.length = 7) :
    VAt ctx.Γ (ctx.criticalPath.path ⟨3, by omega⟩) ⊓
      VAt ctx.Γ (ctx.criticalPath.path ⟨5, by omega⟩) =
        ZAt ctx.Γ (ctx.criticalPath.path ⟨4, by omega⟩) := by
  let vertices : Fin 8 → ctx.Γ.Vertex := fun index =>
    ctx.criticalPath.path ⟨index.val, by omega⟩
  have hadj (index : Fin 7) : ctx.Γ.adjacent
      (vertices index.castSucc) (vertices index.succ) :=
    ctx.criticalPath.path_adj ⟨index.val, by omega⟩
  have hstart : vertices 0 = ctx.criticalPath.a := ctx.criticalPath.path_start
  have hend : vertices 7 = ctx.criticalPath.a' := by
    convert ctx.criticalPath.path_end using 1
    exact congrArg ctx.criticalPath.path (Fin.ext hseven.symm)
  have hdistinct : vertices 3 ≠ vertices 5 := by
    intro heq
    let shortened : Fin 6 → ctx.Γ.Vertex :=
      ![vertices 0, vertices 1, vertices 2, vertices 3, vertices 6, vertices 7]
    have hwalk : ∀ index : Fin 5, ctx.Γ.adjacent
        (shortened index.castSucc) (shortened index.succ) := by
      intro index
      fin_cases index
      · exact hadj 0
      · exact hadj 1
      · exact hadj 2
      · change ctx.Γ.adjacent (vertices 3) (vertices 6)
        rw [heq]
        exact hadj 5
      · exact hadj 6
    have hdist := ctx.Γ.distance_le_of_path 5 shortened hwalk
    change ctx.Γ.distance (vertices 0) (vertices 7) ≤ 5 at hdist
    rw [hstart, hend, ctx.criticalPath.endpoint_distance, hseven] at hdist
    omega
  obtain ⟨firstMover, hfirstMover⟩ :=
    (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity (vertices 1)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm (hadj 0)))
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj 1))
  obtain ⟨secondMover, hsecondMover⟩ :=
    (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity (vertices 3)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm (hadj 2)))
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj 3))
  change ctx.Γ.act (firstMover : G) (vertices 0) = vertices 2 at hfirstMover
  change ctx.Γ.act (secondMover : G) (vertices 2) = vertices 4 at hsecondMover
  have horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.a (vertices 4) := by
    refine ⟨(firstMover : G) * (secondMover : G), ?_⟩
    rw [ctx.Γ.act_mul, ← hstart, hfirstMover, hsecondMover]
  exact nine_seven_shifted_module_intersection ctx third hpath hindex hfirstCard
    hstartData horbit (ctx.Γ.adjacent_symm (hadj 3)) (hadj 4) hdistinct

end Stellmacher.SectionNine
