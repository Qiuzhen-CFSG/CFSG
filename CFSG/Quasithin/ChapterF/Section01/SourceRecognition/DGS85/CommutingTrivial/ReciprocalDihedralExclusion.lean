module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.FullCatalogueBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReciprocalRecognizedSections

/-!
# Dihedral exclusion before reciprocal naturality

If the beta quotient is D10, conjugacy gives the same terminal quotient.
The opposite core index is then at most two. Zero displacement identifies
this with the original centralizer index, but the actual residual constituent
has the dihedral square lower bound. Escape makes its actor index greater
than one, giving the contradiction four at most two.

No Chapter 8 exchange or natural residual section is used in this exclusion.
It supplies the beta model witness needed to start the reciprocal branch
of Chapter 9. Source: DGS, Groups and Graphs (1985), 9.3, printed p.142.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem dihedral_two_actor_card_le (A : Subgroup (DihedralGroup 5))
    (hp : IsPGroup 2 A) : Nat.card A ≤ 2 := by
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  have hd : Nat.card A ∣ 2*5 := by
    simpa only [DihedralGroup.nat_card] using card_subgroup_dvd_card A
  have hco : (Nat.card A).Coprime 5 := by
    rw [hk]
    exact (by decide : Nat.Coprime 2 5).pow_left k
  exact Nat.le_of_dvd (by decide : 0 < 2) (hco.dvd_mul_right.mp hd)

/-- The escaping zero-displacement branch excludes D10 before any natural
residual section or binary-model witness has been constructed. -/
theorem reduced_large_neighbor_not_dihedral (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (he : ¬ V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    (ed : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* DihedralGroup 5) : False := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let H' := graphLocalGroup Γ a'
  let A := (V Γ beta 1).subgroupOf H
  let A' := (V Γ a' 1).subgroupOf H'
  let q := ed.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((V Γ a' 1).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  let := neighborhoodIn_normal Γ a' H' (sylowGenerated_le _)
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_residual_constituent h hc hab hd hb hcomm ed
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let : Finite d.space.toSubmodule := d.finiteSpace
  let : d.action.IsIrreducible := d.irreducible
  let : Nontrivial d.space.toSubmodule := Subrepresentation.irreducible_module_nontrivial d.action
  let : IsElementaryAbelian 2 Aq := d.elementary
  have hcore : pCore 2 (DihedralGroup 5) = ⊥ := by
    rw [←pCore_map_iso 2 ed, pCore_quotient_pCore_eq_bot, Subgroup.map_bot]
  have hsquare := card_ten_residual_fixed_quadratic_square_bound
    (show Nat.card (DihedralGroup 5) = 10 by rw [DihedralGroup.nat_card]) hcore
    d.action d.residualFixed Aq (IsElementaryAbelian.isPGroup 2 Aq) d.quadratic
  rw [d.actorCard] at hsquare
  have hbound := hsquare.trans d.fixedIndex
  have hcentral := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ beta 1))
    (reduced_neighbor_centralizer_eq_core_inter h beta a' hb hd htriv)
  change (V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) =
    (V Γ beta 1 ⊓ Q Γ a').relIndex (V Γ beta 1) at hcentral
  simp only [inf_relIndex_left] at hcentral
  rw [hcentral] at hbound
  obtain ⟨z,hz,hzc,_⟩ := reduced_reverse_criticalPair h (Reduction.reduced_kernel_sylow h) hd he
  have hzcomm : ⁅Z Γ z,Z Γ beta⁆ = ⊥ := reverse_critical_centers_commute ht hzc
    (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  have hd' : (graph Γ).dist a' beta + 1 = b Γ := by rwa [SimpleGraph.dist_comm]
  obtain ⟨g,e₀,f,hg,he₀,hf,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  let ed' := f.trans ed
  let q' := ed'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H'))
  let Aq' := ((V Γ beta 1).subgroupOf H').map q'
  obtain ⟨hb2',⟨d'⟩⟩ := reduced_critical_residual_constituent h hzc hz.symm hd' hb hzcomm ed'
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2' H'
  let : IsElementaryAbelian 2 Aq' := d'.elementary
  have hx := dihedral_two_actor_card_le Aq' (IsElementaryAbelian.isPGroup 2 Aq')
  rw [d'.actorCard] at hx
  have hv := V_le_stabilizer Γ ht.generate a' a'
    (show (graph Γ).dist a' a' + 1 ≤ b Γ by simpa only [SimpleGraph.dist_self,zero_add] using hb.le)
  let : Finite (V Γ a' 1) := Finite.of_injective (inclusion hv) (inclusion_injective _)
  have hy : 1 < (Q Γ beta).relIndex (V Γ a' 1) :=
    one_lt_index_of_ne_top (fun heq => he (subgroupOf_eq_top.mp heq))
  nlinarith

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
