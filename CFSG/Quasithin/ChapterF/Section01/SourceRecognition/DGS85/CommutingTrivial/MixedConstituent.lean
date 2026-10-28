module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ConstituentBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.MixedActions

/-!
# The critical center on the opposite residual section

Construct an irreducible constituent of the literal
V_alpha_prime/C_V_alpha_prime(O²(L_alpha_prime)), and descend its action
through the actual local two-core. The actor is the original Z_alpha,
with its exact core index and an upper bound by the original centralizer
index. For a supplied linear quotient this sandwiches the defining-field
order between those two original indices.

This is the opposite-side estimate in the second case of DGS 9.3,
printed p.142. No whole-section descent or naturality is assumed.
MixedLinearRecognition applies it to the literal small-neighbor branch;
initial quotient recognition and the terminal distance bound remain open.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The original critical center acts on a constructed irreducible constituent
of the opposite residual neighborhood section, with its exact core index. -/
theorem reduced_critical_opposite_constituent (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {D : Type*} [Group D] [Finite D]
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* D) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a'
    let A := (V Γ a' 1).subgroupOf H
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    let Aq := ((Z Γ a).subgroupOf H).map q
    letI : ∀ i, Finite (Γ i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal Γ a' H (sylowGenerated_le _)
    ∃ hb2 : 2 < b Γ,
      letI := neighborhoodIn_elementary Γ (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) a' hb2 H
      Nonempty (ResidualConstituent (fixedQuotientAction A (pResidual 2 H)) q Aq
        ((Q Γ a').relIndex (Z Γ a))
        ((centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1))) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a'
  let A := (V Γ a' 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ a' H (sylowGenerated_le _)
  have hb3 := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.1
  have hb2 : 2 < b Γ := by
    change 3 ≤ b Γ at hb3
    omega
  refine ⟨hb2,?_⟩
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2 H
  obtain ⟨⟨c⟩,hr,hquad⟩ := neighborhood_residual_section ht (Reduction.reduced_kernel_sylow h)
    a' hb2 H (core_le_graphLocalGroup ht a') (sylowGenerated_le _)
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base Γ a'
  have ha' : (graph Γ).Adj a' (g • base Γ (!a'.type)) := by
    rw [←hg]
    exact (Subgroup.CosetGeometry.translationGraphIso Γ g).map_adj_iff.mpr
      ⟨by change a'.type ≠ !a'.type; cases a'.type <;> decide,
        Subgroup.CosetGeometry.incident_base _ _ _⟩
  let : Nontrivial (FixedQuotient A (pResidual 2 H)) :=
    local_residual_section_nontrivial ht (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) ha' (fixedQuotientAction A (pResidual 2 H)) c
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hVL : V Γ a' 1 ≤ H := neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) a' a' hb (by
      change (graph Γ).dist a' a' + 1 ≤ b Γ
      rw [SimpleGraph.dist_self,zero_add]
      exact hb.le)
  let : Finite (V Γ a' 1) := Finite.of_injective (inclusion hVL) (inclusion_injective _)
  let : Finite (FixedQuotient A (pResidual 2 H)) :=
    Finite.of_surjective (fun x : V Γ a' 1 => (c.coordinates x).toAdd)
      (Multiplicative.toAdd.surjective.comp c.onto)
  have hZV : Z Γ a ≤ V Γ beta 1 := CommutingNontrivial.Z_neighbor_le_V Γ hab.symm
  have hZH := hZV.trans (neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) beta a' hb hd.le)
  have hk : q.ker = (Q Γ a').subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    have hcore : H.pCoreIn 2 = Q Γ a' := graphLocalGroup_core ht a'
    rw [←hcore]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  exact section_constituent H (Q Γ a') (V Γ a' 1) _ (Z Γ a)
    (fixedQuotientAction A (pResidual 2 H)) c hr q
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (hk.symm ▸ (isPGroup_pCoreIn 2 _).comap_subtype) hk hZH
    (Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a)
    (fun x hx y hy => hquad beta hd.le x (hZV hx) y (hZV hy))

/-- The constructed linear constituent bounds the original actor index
above and the original centralizer index below by the actual field order. -/
theorem reduced_critical_opposite_linear_field_bounds (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    (Q Γ a').relIndex (Z Γ a) ≤ Nat.card F ∧ Nat.card F ≤
      (centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a'
  let A := (V Γ a' 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((Z Γ a).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ a' H (sylowGenerated_le _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_opposite_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2 H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite d.space.toSubmodule := d.finiteSpace
  let : d.action.IsIrreducible := d.irreducible
  let : Nontrivial d.space.toSubmodule := Subrepresentation.irreducible_module_nontrivial d.action
  have hf := CommutingNontrivial.linear_quotient_action_faithful hn hF e d.action d.residualFixed
  obtain ⟨T,hT⟩ := d.elementary.isPGroup.exists_le_sylow
  have hcard : Nat.card Aq = (Q Γ a').relIndex (Z Γ a) := d.actorCard
  have hne : Aq ≠ ⊥ := by
    intro hbot
    rw [hbot,card_bot] at hcard
    exact hc.2 ((relIndex_eq_one.mp hcard.symm).trans (source_Z_Q_U ht a').2)
  have hlo := sl2_actor_field_bound d.action hf T Aq hT hne hF
  refine ⟨?_,hlo.trans d.fixedIndex⟩
  change (Q Γ a').relIndex (Z Γ a) ≤ Nat.card F
  rw [←hcard]
  exact (Nat.card_le_card_of_injective _ (inclusion_injective hT)).trans_eq
    (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
