module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.FullCatalogueBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.MixedInitialRecognition

/-!
# Mixed initial recognition from the full source catalogue

The small-neighbor branch compares the original alpha-center action with
an irreducible constituent of the terminal residual section. Their exact
centralizer identities give opposite inequalities on the same two core
indices. Both indices exceed one and hence lie strictly below their common
square. The full source bound excludes D10 alongside all nonlinear binary
rows, producing both actual linear quotient markings before any natural
section is used.

This removes the extra binary-model witnesses from the mixed branch of 9.3.
Source: DGS, Groups and Graphs (1985), 9.3, printed p.142.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Construct the actual center module and prove its mixed index estimate;
strictness selects the starting linear quotient from the full source catalogue. -/
theorem reduced_small_neighbor_source_center_bound_and_selection (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (hs : V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (M : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))) :
    let Γ := Reduction.reducedFamily L S₀
    (Q Γ a).relIndex (V Γ a' 1) ≤ (Q Γ a').relIndex (Z Γ a) ∧
      ((Q Γ a').relIndex (Z Γ a) < (Q Γ a).relIndex (V Γ a' 1)^2 →
        ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
          0 < n ∧ Nat.card F = 2^n ∧
          Nonempty ((graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃* SL(2,F))) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let H := graphLocalGroup Γ a
  let D := H ⧸ pCore 2 H
  let e := MulEquiv.refl D
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((V Γ a' 1).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (Z Γ a) := Finite.of_injective (inclusion (Z_le_stabilizer Γ a)) (inclusion_injective _)
  let : Nontrivial (Z Γ a) := CommutingNontrivial.source_center_nontrivial ht a
  obtain ⟨ρ,hact⟩ := CommutingNontrivial.source_exists_center_quotient_action ht d a e
  change Representation (ZMod 2) D (Additive (Z Γ a)) at ρ
  obtain ⟨T₀⟩ := Sylow.nonempty (p := 2) (G := stabilizer Γ a)
  have hgeom := Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm
  have hz := intrinsic_local_center_eq_bot_of_neighbor_central ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab hgeom.2.2.1
  obtain ⟨S,hS,hgen,hres⟩ := CommutingNontrivial.source_center_module_prepared_of_center_eq_bot
    ht d a hz T₀ e ρ hact
  have hp : IsPGroup 2 (V Γ a' 1) := (isPGroup_pCoreIn 2 _).to_le hs
  have hVH : V Γ a' 1 ≤ H := CommutingNontrivial.pGroup_le_localGroup Γ d a _ hp
    (hs.trans ((source_Z_Q_U ht beta).2.trans
      ((ballKernel_one_le_edge Γ hab.symm).trans inf_le_right)))
  have hZL : Z Γ a ≤ H := CommutingNontrivial.pGroup_le_localGroup Γ d a _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer Γ a)
  have hnZ : H ≤ normalizer (Z Γ a : Set (Reduction.G₀ L S₀)) :=
    (sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a)
  have hk : q.ker = (Q Γ a).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    have hcore : H.pCoreIn 2 = Q Γ a := graphLocalGroup_core ht a
    rw [←hcore]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hcard : Nat.card Aq = (Q Γ a).relIndex (V Γ a' 1) :=
    BinaryConjugationSection.actor_image_card_eq_relIndex H (Q Γ a) (V Γ a' 1) q hk hVH
  have hb2 : 2 < b Γ := by
    have hh := hgeom.2.1
    change 3 ≤ b Γ at hh
    omega
  let : IsElementaryAbelian 2 (V Γ a' 1) := V_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2
  let : IsElementaryAbelian 2 ((V Γ a' 1).subgroupOf H) :=
    IsElementaryAbelian.comap_of_injective H.subtype H.subtype_injective _
  let : IsElementaryAbelian 2 Aq := IsElementaryAbelian.map q
  have hAq : IsPGroup 2 Aq := (hp.comap_subtype (K := H)).map q
  obtain ⟨T,hAT⟩ := hAq.exists_le_sylow
  have hgT : GeneratedByFixedSpace (V := Additive (Z Γ a)) ρ (T : Subgroup D) := by
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq D S T
    exact generatedByFixedSpace_of_equivariant_surjection ρ ρ
      (MulAut.conj g).toMonoidHom (ρ g)
      (fun v => ⟨ρ g⁻¹ v, ρ.self_inv_apply g v⟩)
      (by intro a v; simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
        MulAut.conj_apply,map_mul,Module.End.mul_apply,ρ.inv_self_apply]) S hgen
  have hindex := CommutingNontrivial.center_action_fixed_index H (Z Γ a) (V Γ a' 1)
    hZL hnZ hVH q ρ hact
  have hc₀ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (Z Γ a))
    (mixed_center_centralizer ht (Reduction.reduced_kernel_sylow h) hab hd.le htriv)
  change (Z Γ a ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (Z Γ a) =
    (Z Γ a ⊓ Q Γ a').relIndex (Z Γ a) at hc₀
  simp only [inf_relIndex_left] at hc₀
  have hi : Nat.card (Additive (Z Γ a) ⧸ fixedSpace ρ Aq) = (Q Γ a').relIndex (Z Γ a) :=
    hindex.trans hc₀
  have hq : IsQuadratic ρ Aq := by
    apply BinaryConjugationSection.isQuadratic_of_triple_commutator_le H (Z Γ a) ⊥ (V Γ a' 1)
      ρ q (CommutingNontrivial.centerSection H (Z Γ a) hZL hnZ q ρ hact)
    have hquad := (reduced_critical_mixed_actions h hc hab hd hb hcomm htriv hs).2.2.2.2.2.2.2.1
    rw [commutator_comm (V Γ a' 1) (Z Γ a),commutator_comm]
    exact hquad.le
  have hbound := generated_source_rank_one_bound_and_selection e M ρ T Aq hAT hq hgT hres
  rwa [hi,hcard] at hbound

/-- Both adjacent local quotients are recognized from the full catalogues.
The two mixed core indices coincide; no initial linear marking is supplied. -/
theorem reduced_small_neighbor_source_linear_markings (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (hs : V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mα' : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a'))) :
    let Γ := Reduction.reducedFamily L S₀
    (Q Γ a').relIndex (Z Γ a) = (Q Γ a).relIndex (V Γ a' 1) ∧
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
        (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (n m : ℕ),
        0 < n ∧ Nat.card F = 2^n ∧ 0 < m ∧ Nat.card K = 2^m ∧
        Nonempty ((graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃* SL(2,F)) ∧
        Nonempty ((graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,K)) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a'
  let D := H ⧸ pCore 2 H
  let e := MulEquiv.refl D
  let A := (V Γ a' 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((Z Γ a).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ a' H (sylowGenerated_le _)
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_opposite_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2 H
  let : Finite d.space.toSubmodule := d.finiteSpace
  let : d.action.IsIrreducible := d.irreducible
  let : Nontrivial d.space.toSubmodule := Subrepresentation.irreducible_module_nontrivial d.action
  let : IsElementaryAbelian 2 Aq := d.elementary
  obtain ⟨T,hT⟩ := d.elementary.isPGroup.exists_le_sylow
  obtain ⟨hlo,hselect⟩ := generated_source_rank_one_bound_and_selection e Mα' d.action T Aq hT
    d.quadratic (d.generated T) d.residualFixed
  have hec := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ a' 1))
    (reduced_critical_mixed_centralizers h hc hab hd hb hcomm htriv hs).2.1
  change (V Γ a' 1 ⊓ centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) =
    (V Γ a' 1 ⊓ Q Γ a).relIndex (V Γ a' 1) at hec
  simp only [inf_relIndex_left] at hec
  have hupper : Nat.card (d.space.toSubmodule ⧸ fixedSpace d.action Aq) ≤
      (Q Γ a).relIndex (V Γ a' 1) := d.fixedIndex.trans_eq hec
  rw [d.actorCard] at hlo
  have hxy : (Q Γ a').relIndex (Z Γ a) ≤ (Q Γ a).relIndex (V Γ a' 1) := hlo.trans hupper
  obtain ⟨hyx,hselectα⟩ :=
    reduced_small_neighbor_source_center_bound_and_selection h hc hab hd hb hcomm htriv hs hob Mα
  have heq : (Q Γ a').relIndex (Z Γ a) = (Q Γ a).relIndex (V Γ a' 1) := le_antisymm hxy hyx
  let : Finite (Z Γ a) := Finite.of_injective
    (inclusion (Z_le_stabilizer Γ a)) (inclusion_injective _)
  have hx : 1 < (Q Γ a').relIndex (Z Γ a) := by
    apply one_lt_index_of_ne_top
    intro he
    exact hc.2 ((subgroupOf_eq_top.mp he).trans (source_Z_Q_U ht a').2)
  have hstrict : (Q Γ a').relIndex (Z Γ a) < (Q Γ a).relIndex (V Γ a' 1)^2 := by
    rw [←heq]
    nlinarith
  obtain ⟨F,instF,finF,charF,n,hn,hF,eα⟩ := hselectα hstrict
  obtain ⟨K,instK,finK,charK,m,hm,hK,⟨eα'⟩⟩ := hselect (by
    rw [d.actorCard]
    exact hupper.trans_lt (by rw [←heq]; nlinarith))
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  obtain ⟨g,e₀,f,hg,he₀,hf,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  exact ⟨heq,F,instF,finF,charF,K,instK,finK,charK,n,m,hn,hF,hm,hK,eα,⟨f.symm.trans eα'⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
