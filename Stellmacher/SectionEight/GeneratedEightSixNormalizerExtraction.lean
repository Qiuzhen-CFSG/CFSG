module

public import Stellmacher.SectionEight.GeneratedEightSixBaseSetup
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricExtraction
public import Theory.Frattini.PGroupMap

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

@[expose] public noncomputable def eightSixCommutatorCost
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (actor : G) : ℕ :=
  (ZAt graph path.firstStep).relIndex
    (⁅VAt graph path.firstStep, Subgroup.zpowers actor⁆ ⊔ ZAt graph path.firstStep)

public theorem eight_six_minimal_actor_configuration
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2)
    (next initial : graph.Vertex)
    (hadj : initial ∈ Later.Neighborhood graph next)
    (A : Subgroup G) (hA : A ≤ QAt graph initial)
    (hnot : ¬ A ≤ QAt graph next)
    (hphi : SectionsFiveToSeven.frattiniAmbient A ≤ QAt graph next)
    (cost : G → ℕ) :
    ∃ actor : G, ∃ E A0 : Subgroup G,
      actor ∈ A ∧ actor ∉ QAt graph next ∧
      (∀ other : G, other ∈ A → other ∉ QAt graph next →
        cost actor ≤ cost other) ∧
      E ⊔ (GAt graph initial ⊓ GAt graph next) = GAt graph next ∧
      Nonempty (QuotientDihedralProduct E (QAt graph next) A0) ∧
      Nonempty (SectionNine.NineThreeGeometricData graph next initial A E A0 actor) := by
  classical
  have hexists : ∃ value : ℕ, ∃ actor : G,
      actor ∈ A ∧ actor ∉ QAt graph next ∧ cost actor = value := by
    obtain ⟨actor, hactor, houtside⟩ := SetLike.not_le_iff_exists.mp hnot
    exact ⟨cost actor, actor, hactor, houtside, rfl⟩
  obtain ⟨actor, hactor, houtside, hcost⟩ := Nat.find_spec hexists
  obtain ⟨conjugator, A0, E, hEP, _, h0A, hgen, hcard, hyE, _, h0core,
      hedge, hmodel, _, hby, _, ha0⟩ :=
    sevenEight_quotient_configuration_with_actor hyp graph next initial hadj
      A hA hnot hphi actor hactor houtside
  refine ⟨actor, E, A0, hactor, houtside, ?_, hedge, hmodel, ?_⟩
  · intro other hother hotherOutside
    rw [hcost]
    exact Nat.find_min' hexists ⟨other, hother, hotherOutside, rfl⟩
  · exact SectionNine.nine_three_geometric_extraction hyp graph next initial hadj
      A E A0 hA hphi actor hactor ha0 conjugator hyE hEP hgen h0A hcard
      h0core hedge hmodel hby

public theorem eight_six_neighborhood_closure_le_core
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : 1 < path.length) (vertex : graph.Vertex) :
    VAt graph vertex ≤ QAt graph vertex := by
  change graph.vAt vertex ≤ QAt graph vertex
  rw [graph.vAt_def]
  refine sSup_le fun center hcenter => ?_
  obtain ⟨neighbor, hneighbor, rfl⟩ := hcenter
  apply SevenSix.critical_minimality graph path
  have hadj := (SevenSix.mem_neighborhood_iff_adjacent graph).mp hneighbor
  have hdist := (SevenSix.adjacent_iff_distance_eq_one graph).mp
    (graph.adjacent_symm hadj)
  omega

public theorem generated_eight_six_extraction_inputs
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hQ : Q = twoCoreIn L)
    (equation : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D :
        Subgroup (P1 ⊔ P2 : Subgroup H)) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a :
        Subgroup (P1 ⊔ P2 : Subgroup H))) :
    let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
    ¬ A ≤ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      SectionsFiveToSeven.frattiniAmbient A ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
  have hAQ : A ≤ Q := by
    rw [equation.core_generation]
    exact le_sup_left.trans le_sup_left
  have htwoQ : IsPGroup 2 Q := by
    rw [hQ]
    exact (pCore_isPGroup (p := 2)).map _
  let : Fact (IsPGroup 2 Q) := ⟨htwoQ⟩
  let : Fact (IsPGroup 2 A) := ⟨htwoQ.to_le hAQ⟩
  have hADcore : A ≤ QAt ctx.Γ previous :=
    inf_le_left.trans (eight_six_neighborhood_closure_le_core
      ctx.Γ ctx.criticalPath (by omega) previous)
  have hDnext : D ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
    rw [hD]
    exact inf_le_right
  constructor
  · intro hnext
    have hAD : A ≤ D := by rw [hD]; exact le_inf hADcore hnext
    have hpositive : 0 < Nat.card A := Nat.card_pos
    change 4 * Nat.card (A ⊓ D : Subgroup (P1 ⊔ P2 : Subgroup H)) ≤ Nat.card A
      at hlarge
    rw [inf_eq_left.mpr hAD] at hlarge
    omega
  · apply le_trans ?_ (equation.core_frattini_le.trans hDnext)
    change (frattini A).map A.subtype ≤ (frattini Q).map Q.subtype
    have hmap := frattini_map_le_of_isPGroup (p := 2) (Subgroup.inclusion hAQ)
    calc
      (frattini A).map A.subtype =
          ((frattini A).map (Subgroup.inclusion hAQ)).map Q.subtype := by
        rw [Subgroup.map_map]
        rfl
      _ ≤ (frattini Q).map Q.subtype := Subgroup.map_mono hmap

public theorem generated_eight_six_minimal_actor_configuration
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hQ : Q = twoCoreIn L)
    (equation : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D :
        Subgroup (P1 ⊔ P2 : Subgroup H)) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a :
        Subgroup (P1 ⊔ P2 : Subgroup H)))
    (cost : (P1 ⊔ P2 : Subgroup H) → ℕ) :
    let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
    ∃ actor : (P1 ⊔ P2 : Subgroup H), ∃ E A0 : Subgroup (P1 ⊔ P2 : Subgroup H),
      actor ∈ A ∧ actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      (∀ other : (P1 ⊔ P2 : Subgroup H), other ∈ A →
        other ∉ QAt ctx.Γ ctx.criticalPath.firstStep → cost actor ≤ cost other) ∧
      E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
        GAt ctx.Γ ctx.criticalPath.firstStep ∧
      Nonempty (QuotientDihedralProduct E (QAt ctx.Γ ctx.criticalPath.firstStep) A0) ∧
      Nonempty (SectionNine.NineThreeGeometricData ctx.Γ
        ctx.criticalPath.firstStep ctx.criticalPath.a A E A0 actor) := by
  obtain ⟨hnot, hphi⟩ := generated_eight_six_extraction_inputs
    ctx hlength previous D L Q hD hQ equation hlarge
  exact eight_six_minimal_actor_configuration ctx.sectionSeven ctx.Γ
    ctx.criticalPath.firstStep ctx.criticalPath.a
    ((SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj))
    _ inf_le_right hnot hphi cost

end Stellmacher.SectionEight
