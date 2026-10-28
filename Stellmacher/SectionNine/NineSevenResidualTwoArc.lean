module

public import Stellmacher.SectionNine.CubicLocalAction
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.ResidualTransport
public import Stellmacher.SectionFiveToSeven.Result7_6

/-!
# Rooted residual transport in Stellmacher (9.7)

At a vertex in the first-step orbit, its two-residual transports any two
nonbacktracking paths of length two that start there, provided the local
quotients on the opposite orbit are SL₂(2). The residual first moves the
middle vertex using the Sylow supplement. Its two-core then corrects the
outer vertex: transported (7.6)(b) shows that this core escapes the middle
vertex core, so the cubic action is transitive on the two remaining neighbors.

The generalized public theorem assumes only the opposite-orbit quotient
models. No quotient model at the first-step vertex enters the proof; the
original theorem retains that redundant hypothesis as a compatibility wrapper.
This supplies the rooted transport needed by the nearby-neighborhood
contraction in the long-distance branch and the large Section Ten predecessor
transport, where the first-step quotient is Frobenius of order twenty.
It does not require residual
two-transitivity on the neighbors of a single vertex. Source: Stellmacher,
printed p.54 / PDF p.44, the first paragraph of the proof of (9.7).
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
variable {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}

private theorem residualAt_act (Γ : CosetGraphContext G T A B)
    (actor : G) (vertex : Γ.Vertex) :
    EAt Γ (Γ.act actor vertex) =
      (EAt Γ vertex).map (MulAut.conj actor⁻¹).toMonoidHom := by
  change Γ.twoResidualAt _ = (Γ.twoResidualAt _).map _
  rw [Γ.twoResidualAt_def, Γ.twoResidualAt_def]
  change twoResidualIn (stabilizer Γ (Γ.act actor vertex)) = _
  rw [stabilizer_act, conjugateBy, twoResidualIn_map_equiv]
  rfl

/-- The vertex two-residual acts transitively on its neighboring vertices. -/
public theorem nine_seven_residual_neighbor_transitive
    (h7 : SectionSevenHypotheses G T A B) (Γ : CosetGraphContext G T A B)
    (root left right : Γ.Vertex)
    (hleft : Γ.adjacent root left) (hright : Γ.adjacent root right) :
    ∃ actor : G, actor ∈ EAt Γ root ∧ Γ.act actor left = right := by
  let P := GAt Γ root
  let E := EAt Γ root
  let edge := GAt Γ root ⊓ GAt Γ left
  let sylow : Sylow 2 edge := default
  let W := sylowTwoAmbient edge sylow
  have hWP : IsSylowTwoIn W P :=
    ((lemma_seven_three h7 Γ).sylow_and_core root left
      ((mem_neighborhood_iff_adjacent Γ).mpr hleft) sylow).1
  have hWedge : W ≤ edge := Subgroup.map_subtype_le _
  have hEP : E ≤ P := by
    change Γ.twoResidualAt root ≤ Γ.stabilizer root
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hsup : E ⊔ W = P := by
    change Γ.twoResidualAt root ⊔ W = Γ.stabilizer root
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_sup_sylow hWP
  let _ : (E.subgroupOf P).Normal := by
    change ((Γ.twoResidualAt root).subgroupOf (Γ.stabilizer root)).Normal
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_normal _
  have hnative : W.subgroupOf P ⊔ E.subgroupOf P = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hWP.1 hEP, sup_comm, hsup,
      Subgroup.subgroupOf_self]
  obtain ⟨mover, hmover⟩ := (lemma_seven_one h7 Γ).local_transitivity root
    ((mem_neighborhood_iff_adjacent Γ).mpr hleft)
    ((mem_neighborhood_iff_adjacent Γ).mpr hright)
  obtain ⟨w, hw, e, he, hwe⟩ := Subgroup.mem_sup_of_normal_right.mp
    (show mover ∈ W.subgroupOf P ⊔ E.subgroupOf P by rw [hnative]; trivial)
  have hwfix : Γ.act (w : G) left = left :=
    (Set.ext_iff.mp (Γ.stabilizer_def left) _).mp (hWedge hw).2
  refine ⟨e, he, ?_⟩
  have hproduct : (w : G) * (e : G) = (mover : G) := congrArg Subtype.val hwe
  rwa [← hproduct, Γ.act_mul, hwfix] at hmover

private theorem next_orbit_edge_alignment
    (ctx : SectionNineLocalContext G T A B) (root middle : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep root)
    (hadj : ctx.Γ.adjacent root middle) :
    ∃ actor : G, ctx.Γ.act actor ctx.criticalPath.firstStep = root ∧
      ctx.Γ.act actor ctx.criticalPath.a = middle := by
  obtain ⟨first, hfirst⟩ := horbit
  have hneighbor := adjacent_act ctx.Γ first
    (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj)
  rw [hfirst] at hneighbor
  obtain ⟨second, hsecond⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    root ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hneighbor)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
  refine ⟨first * (second : G), ?_, ?_⟩
  · rw [ctx.Γ.act_mul, hfirst]
    exact (Set.ext_iff.mp (ctx.Γ.stabilizer_def root) _).mp second.property
  · rw [ctx.Γ.act_mul]
    exact hsecond

public theorem nine_seven_residual_core_escapes_neighbor
    (ctx : SectionNineLocalContext G T A B) (root middle : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep root)
    (hadj : ctx.Γ.adjacent root middle) :
    ¬ twoCoreIn (EAt ctx.Γ root) ≤ QAt ctx.Γ middle := by
  obtain ⟨actor, hroot, hmiddle⟩ := next_orbit_edge_alignment ctx root middle horbit hadj
  intro hle
  rw [← hroot, ← hmiddle, residualAt_act, twoCoreIn_map_equiv, QAt, q_act] at hle
  exact (lemma_seven_six ctx.sectionSeven ctx.Γ ctx.criticalPath).next_residual_core.1
    ((Subgroup.map_le_map_iff_of_injective (MulAut.conj actor⁻¹).injective).mp hle)

public theorem nine_seven_residual_two_arc_transport_of_opposite_models
    (ctx : SectionNineLocalContext G T A B)
    (hstartModels : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two)
    (root : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep root)
    (middle outer targetMiddle targetOuter : ctx.Γ.Vertex)
    (hfirst : ctx.Γ.adjacent root middle)
    (hsecond : ctx.Γ.adjacent middle outer) (hback : root ≠ outer)
    (htargetFirst : ctx.Γ.adjacent root targetMiddle)
    (htargetSecond : ctx.Γ.adjacent targetMiddle targetOuter)
    (htargetBack : root ≠ targetOuter) :
    ∃ actor : G, actor ∈ EAt ctx.Γ root ∧
      ctx.Γ.act actor middle = targetMiddle ∧
      ctx.Γ.act actor outer = targetOuter := by
  obtain ⟨first, hfirstE, hfirstMove⟩ := nine_seven_residual_neighbor_transitive
    ctx.sectionSeven ctx.Γ root middle targetMiddle hfirst htargetFirst
  have hEP : EAt ctx.Γ root ≤ GAt ctx.Γ root := by
    change ctx.Γ.twoResidualAt root ≤ ctx.Γ.stabilizer root
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hfirstFix : ctx.Γ.act first root = root :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def root) _).mp (hEP hfirstE)
  have hmoveAdj := adjacent_act ctx.Γ first hsecond
  rw [hfirstMove] at hmoveAdj
  have hmoveNe : ctx.Γ.act first outer ≠ root := by
    intro heq
    apply hback
    have hcancel := congrArg (ctx.Γ.act first⁻¹) (hfirstFix.trans heq.symm)
    simpa only [← ctx.Γ.act_mul, mul_inv_cancel, ctx.Γ.act_one] using hcancel
  let K := twoCoreIn (EAt ctx.Γ root)
  have hKQ : K ≤ QAt ctx.Γ root := by
    change twoCoreIn (ctx.Γ.twoResidualAt root) ≤ ctx.Γ.twoCoreAt root
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hQneighbor : QAt ctx.Γ root ≤ GAt ctx.Γ targetMiddle :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core root targetMiddle
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr htargetFirst) default).2.2
  have hKedge : K ≤ GAt ctx.Γ targetMiddle ⊓ GAt ctx.Γ root :=
    le_inf (hKQ.trans hQneighbor) ((twoCoreIn_le _).trans hEP)
  obtain ⟨aligner, _, halign⟩ := next_orbit_edge_alignment ctx root targetMiddle horbit htargetFirst
  have hmodel := hstartModels targetMiddle ⟨aligner, halign⟩
  have htrans := (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven
    targetMiddle hmodel).punctured_transitivity root (ctx.Γ.adjacent_symm htargetFirst)
      K hKedge (nine_seven_residual_core_escapes_neighbor ctx root targetMiddle horbit htargetFirst)
  obtain ⟨second, hsecondMove⟩ := htrans
    ⟨(mem_neighborhood_iff_adjacent ctx.Γ).mpr hmoveAdj, hmoveNe⟩
    ⟨(mem_neighborhood_iff_adjacent ctx.Γ).mpr htargetSecond, htargetBack.symm⟩
  have hsecondFix : ctx.Γ.act (second : G) targetMiddle = targetMiddle :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def targetMiddle) _).mp (hKedge second.property).1
  refine ⟨first * (second : G), (EAt ctx.Γ root).mul_mem hfirstE
    (twoCoreIn_le _ second.property), ?_, ?_⟩
  · rw [ctx.Γ.act_mul, hfirstMove, hsecondFix]
  · rw [ctx.Γ.act_mul]
    exact hsecondMove


public theorem nine_seven_residual_two_arc_transport
    (ctx : SectionNineLocalContext G T A B)
    (_hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hstartModels : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two)
    (root : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep root)
    (middle outer targetMiddle targetOuter : ctx.Γ.Vertex)
    (hfirst : ctx.Γ.adjacent root middle)
    (hsecond : ctx.Γ.adjacent middle outer) (hback : root ≠ outer)
    (htargetFirst : ctx.Γ.adjacent root targetMiddle)
    (htargetSecond : ctx.Γ.adjacent targetMiddle targetOuter)
    (htargetBack : root ≠ targetOuter) :
    ∃ actor : G, actor ∈ EAt ctx.Γ root ∧
      ctx.Γ.act actor middle = targetMiddle ∧
      ctx.Γ.act actor outer = targetOuter := by
  exact nine_seven_residual_two_arc_transport_of_opposite_models ctx hstartModels root horbit
    middle outer targetMiddle targetOuter hfirst hsecond hback htargetFirst htargetSecond htargetBack

end Stellmacher.SectionNine
