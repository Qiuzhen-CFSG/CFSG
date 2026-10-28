module
public import Stellmacher.SectionTen.OpeningData
public import Stellmacher.SectionNine.NineNextCenterCommutator
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore

/-!
# The generated subgroup W lies in W₀ in Stellmacher (10.1)

Under the original ambient Section Ten hypotheses, the conjugate closure of
V at the first step intersected with the terminal core lies in every core
neighboring the middle vertex and in its generated neighborhood module.
Thus W lies in the actual W₀, without any extra containment assumptions.

Local transitivity transports the (7.6)(b) core noncontainment to the middle
edge. The cubic local action is therefore transitive on the other two
neighbors. The equality [Vfirst,Qfirst] = Zfirst and the center containment
from the opening data show that Qfirst normalizes the seed. Its transitivity
transfers the seed's terminal-core containment to every neighboring core.
Covariance under the middle stabilizer passes this property to the conjugate
closure; covariance of V gives the generated-neighborhood containment.

Source: Stellmacher, Journal of Algebra 190 (1997), first sentence of the
proof of (10.1), printed p.60/PDF p.50 of
`refs/files/stellmacher-n-group.pdf`, and `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u

variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem first_core_escapes_middle
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    {middle : ctx.Γ.Vertex}
    (hfirst : ctx.Γ.adjacent middle ctx.criticalPath.firstStep) :
    ¬ QAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ middle := by
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    ctx.criticalPath.firstStep
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj))
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hfirst))
  have hfix : ctx.Γ.act (actor : G) ctx.criticalPath.firstStep =
      ctx.criticalPath.firstStep :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def _) _).mp actor.property
  have hcoreFixed : (QAt ctx.Γ ctx.criticalPath.firstStep).map
      (MulAut.conj (actor : G)⁻¹).toMonoidHom = QAt ctx.Γ ctx.criticalPath.firstStep := by
    exact (q_act ctx.Γ actor ctx.criticalPath.firstStep).symm.trans (congrArg _ hfix)
  intro hle
  have hinitial : QAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ ctx.criticalPath.a := by
    apply (Subgroup.map_le_map_iff_of_injective
      (f := (MulAut.conj (actor : G)⁻¹).toMonoidHom)
      (MulAut.conj (actor : G)⁻¹).injective).mp
    rw [hcoreFixed, ← q_act, hactor]
    exact hle
  apply (lemma_seven_six ctx.sectionSeven ctx.Γ ctx.criticalPath).next_residual_core.1
  apply le_trans ?_ hinitial
  change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.firstStep) ≤
    ctx.Γ.twoCoreAt ctx.criticalPath.firstStep
  rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
  exact inf_le_right

private theorem seed_le_neighbor_core
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ∀ neighbor, neighbor ∈ Neighborhood ctx.Γ middle →
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a' ≤
        QAt ctx.Γ neighbor := by
  let U := VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a'
  obtain ⟨horbit, hfirst, hterminal, hne⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hfour := (lemma_nine_three_ambient ctx.toAmbientSectionNineContext hb
    ctx.criticalPath.a ⟨1, ctx.Γ.act_one _⟩).2
  have hopen := sectionTenOpeningData ctx middle hpath
  have hZV : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
    have hZM : ZAt ctx.Γ ctx.criticalPath.firstStep ≤ ZAt ctx.Γ middle := by
      rw [hopen.center_direct_product.1]
      exact le_sup_left
    exact hZM.trans (nine_seven_neighbor_center_le_module ctx.Γ
      (ctx.Γ.adjacent_symm hfirst))
  have hZQ : ZAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    apply critical_minimality ctx.Γ ctx.criticalPath
    have hdist := ctx.Γ.distance_le_of_path 2
      ![ctx.criticalPath.firstStep, middle, ctx.criticalPath.a'] (by
        intro step
        fin_cases step
        · exact ctx.Γ.adjacent_symm hfirst
        · exact hterminal)
    change ctx.Γ.distance ctx.criticalPath.firstStep ctx.criticalPath.a' ≤ 2 at hdist
    rw [ctx.critical_length]
    omega
  have hUQ : U ≤ QAt ctx.Γ ctx.criticalPath.firstStep :=
    inf_le_left.trans (neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hb _)
  have hnormal : QAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (U : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_right.mpr
    rw [Subgroup.commutator_comm]
    exact ((Subgroup.commutator_mono inf_le_left le_rfl).trans_eq
      (nine_next_module_commutator_of_initial_four ctx.toLocalContext.toSectionNineLocalContext
        hfour)).trans (le_inf hZV hZQ)
  have hQself : QAt ctx.Γ ctx.criticalPath.firstStep ≤ GAt ctx.Γ ctx.criticalPath.firstStep := by
    rw [QAt, q, ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQmiddle : QAt ctx.Γ ctx.criticalPath.firstStep ≤ GAt ctx.Γ middle :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hfirst)) default).2.2
  have htrans := (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven
    middle hopen.quotient_model).punctured_transitivity ctx.criticalPath.firstStep hfirst
      (QAt ctx.Γ ctx.criticalPath.firstStep) (le_inf hQmiddle hQself)
      (first_core_escapes_middle ctx hfirst)
  intro neighbor hneighbor
  by_cases heq : neighbor = ctx.criticalPath.firstStep
  · simpa only [heq] using hUQ
  obtain ⟨actor, hactor⟩ := htrans
    ⟨(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal, hne.symm⟩ ⟨hneighbor, heq⟩
  change U ≤ q ctx.Γ neighbor
  rw [← hactor, q_act]
  intro element helement
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_inv]
  exact ((Subgroup.mem_normalizer_iff.mp (hnormal actor.property) element).mp helement).2

/-- The first common containment in the proof of Stellmacher (10.1). -/
public theorem ten_one_generated_containment
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    conjugateClosure
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
        (GAt ctx.Γ middle) ≤
      NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
        GeneratedNeighborhoodV ctx.Γ middle := by
  obtain ⟨_, hfirst, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hseed := seed_le_neighbor_core ctx middle hpath
  rw [conjugateClosure, Subgroup.closure_le]
  rintro element ⟨actor, generator, rfl⟩
  have hfix : ctx.Γ.act (actor : G) middle = middle :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def middle) _).mp actor.property
  have hfixInv : ctx.Γ.act (actor : G)⁻¹ middle = middle :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def middle) _).mp
      ((GAt ctx.Γ middle).inv_mem actor.property)
  constructor
  · change _ ∈ NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle)
    rw [NeighborhoodQIntersection, Subgroup.mem_sInf]
    rintro core ⟨neighbor, hneighbor, rfl⟩
    have hadj := adjacent_act ctx.Γ (actor : G)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor)
    rw [hfix] at hadj
    have hmem := hseed (ctx.Γ.act (actor : G) neighbor)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj) generator.property
    change (generator : G) ∈ q ctx.Γ (ctx.Γ.act (actor : G) neighbor) at hmem
    rw [q_act, Subgroup.mem_map_equiv] at hmem
    simpa only [MulAut.conj_symm_apply, inv_inv] using hmem
  · have hadj := adjacent_act ctx.Γ (actor : G)⁻¹ hfirst
    rw [hfixInv] at hadj
    have hle : VAt ctx.Γ (ctx.Γ.act (actor : G)⁻¹ ctx.criticalPath.firstStep) ≤
        GeneratedNeighborhoodV ctx.Γ middle :=
      le_sSup ⟨_, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj, rfl⟩
    apply hle
    change _ ∈ v ctx.Γ (ctx.Γ.act (actor : G)⁻¹ ctx.criticalPath.firstStep)
    rw [v_act, inv_inv]
    exact Subgroup.mem_map_of_mem _ generator.property.1

/-- The same containment for the original single-carrier Section Ten context. -/
public theorem ten_one_generated_containment_legacy
    (ctx : SectionTenContext H S0 S P1 P2)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    conjugateClosure
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
        (GAt ctx.Γ middle) ≤
      NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
        GeneratedNeighborhoodV ctx.Γ middle :=
  ten_one_generated_containment ctx.toAmbientContext middle hpath

end Stellmacher.SectionTen
