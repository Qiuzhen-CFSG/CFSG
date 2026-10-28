module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PathBorelComplete
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.DistanceSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration
public import Theory.GroupTheory.IrreducibleImageInterval

/-!
# Both original linear intervals on the distance-three path

The full-catalogue path Borel theorem applies at both ends of the literal
beta, alpha+2, alpha-prime path. The two neighborhood images are nonzero
normal subgroups of the corresponding roots, so both images are the full
Sylows. Their core indices equal the same field order, using the existing
conjugation transport between the two endpoint quotients.

Borel irreducibility lifts through each exact core kernel: each interval
has no intermediate subgroup invariant under its displayed local path actor.
The original F1.11 application discharges distance three and the earlier
core obstruction. No natural-section, central-containment or reverse-failure
hypothesis is used.

The two interval actors are displayed separately. This does not identify
their local-group intersections, nor prove that the beta residual-fixed
denominator lies in the terminal core. Those are not supplied by the two
separate Borel images; the remaining natural-module step of 8.5 is distinct.

Source: DGS, *Groups and Graphs* (1985), 8.5--8.6, printed pp.139--140.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Lift root irreducibility through the literal beta quotient map and its
original core kernel, retaining the actual local path normalizer. -/
theorem source_path_root_interval
    (h : LocallyRankOneTriple P B) {beta mid a' : Vertex (family P)}
    (A : Subgroup G) (hAL : A ≤ graphLocalGroup (family P) beta)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,k))
    (T : Sylow 2 SL(2,k))
    (hA : (A.subgroupOf (graphLocalGroup (family P) beta)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) beta)))) = T)
    (hK : ((stabilizer (family P) mid ⊓ stabilizer (family P) a').subgroupOf
      (graphLocalGroup (family P) beta)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) beta)))) =
      normalizer (T : Set SL(2,k)))
    (D : Subgroup G) (hAD : A ⊓ Q (family P) beta ≤ D) (hDA : D ≤ A)
    (hn : graphLocalGroup (family P) beta ⊓
      (stabilizer (family P) mid ⊓ stabilizer (family P) a') ≤ normalizer (D : Set G)) :
    D = A ⊓ Q (family P) beta ∨ D = A := by
  let F := family P
  let L := graphLocalGroup F beta
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let R := (stabilizer F mid ⊓ stabilizer F a').subgroupOf L
  change (A.subgroupOf L).map q = T at hA
  change R.map q = normalizer (T : Set SL(2,k)) at hK
  have hker : q.ker = (Q F beta).subgroupOf L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    have hcore : (pCore 2 L).map L.subtype = Q F beta := graphLocalGroup_core h beta
    rw [←hcore]
    exact (comap_map_eq_self_of_injective L.subtype_injective _).symm
  have hh := interval_of_irreducible_image q R (A.subgroupOf L)
    ((A ⊓ Q F beta).subgroupOf L) (by rw [hker]; rfl)
    (by
      intro X hX hnX
      by_cases hx : X = ⊥
      · exact Or.inl hx
      · right
        rw [hA] at hX ⊢
        exact Matrix.SpecialLinearGroup.sylow_eq_of_normalized T X hX hx
          (by simpa only [hK] using hnX))
    (D.subgroupOf L) (comap_mono hAD) (comap_mono hDA) (by
      intro l hl
      rw [←subgroupOf_normalizer_eq (hDA.trans hAL)]
      exact hn ⟨l.property,hl⟩)
  have hDL := hDA.trans hAL
  rcases hh with hh | hh
  · left
    have hm := congrArg (map L.subtype) hh
    rw [map_subgroupOf_eq_of_le hDL,
      map_subgroupOf_eq_of_le (inf_le_left.trans hAL)] at hm
    exact hm
  · right
    have hm := congrArg (map L.subtype) hh
    rw [map_subgroupOf_eq_of_le hDL,map_subgroupOf_eq_of_le hAL] at hm
    exact hm

/-- Both original quotient intervals have field-size index and no invariant
intermediate subgroup under the respective local path actors. Distance three
and the 6.5 obstruction are consequences of the original source hypotheses. -/
theorem reduced_critical_linear_paired_intervals
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) beta)) ≃* SL(2,k)) :
    let F := Reduction.reducedFamily J S₀
    b F = 3 ∧
      (Q F beta).relIndex (V F a' 1) = Nat.card k ∧
      (Q F a').relIndex (V F beta 1) = Nat.card k ∧
      ∃ mid : Vertex F, (graph F).Adj beta mid ∧ (graph F).Adj a' mid ∧
        (∀ D : Subgroup (Reduction.G₀ J S₀),
          V F a' 1 ⊓ Q F beta ≤ D → D ≤ V F a' 1 →
          graphLocalGroup F beta ⊓ (stabilizer F mid ⊓ stabilizer F a') ≤ normalizer (D : Set _) →
          D = V F a' 1 ⊓ Q F beta ∨ D = V F a' 1) ∧
        (∀ D : Subgroup (Reduction.G₀ J S₀),
          V F beta 1 ⊓ Q F a' ≤ D → D ≤ V F beta 1 →
          graphLocalGroup F a' ⊓ (stabilizer F mid ⊓ stabilizer F beta) ≤ normalizer (D : Set _) →
          D = V F beta 1 ⊓ Q F a' ∨ D = V F beta 1) := by
  let F := Reduction.reducedFamily J S₀
  let ht := Reduction.reduced_triple h
  let hob := Reduction.reduced_graph_core_obstruction h
  let hB := Reduction.reduced_borel_core_sylow h
  let hS := Reduction.reduced_vertex_sylow h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hb3 := reduced_distance_three_of_catalogue h models hc hab hd hb hcomm hne
  obtain ⟨mid,hbm,ham,hVm,_,T,hT,hK,_⟩ :=
    reduced_critical_path_borel h hob models hc hab hd hb3 hcomm e
  have hV'm : V F a' 1 ≤ Q F mid := V_le_Q_of_dist_add_lt_b F ht.generate
    (fun v => (source_Z_Q_U ht v).1) a' mid 1
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr ham]; change 1+1 < b (Reduction.reducedFamily J S₀); omega)
    (Reduction.reduced_kernel_sylow h mid)
  have hV'L : V F a' 1 ≤ graphLocalGroup F beta :=
    hV'm.trans (neighbor_core_le_localGroup ht hB hS hbm)
  have hVL' : V F beta 1 ≤ graphLocalGroup F a' :=
    hVm.trans (neighbor_core_le_localGroup ht hB hS ham)
  have hesc' := reduced_reciprocal_escape h hob models hc hab hd hb hcomm hne
  have hesc : ¬ V F beta 1 ≤ Q F a' := by
    intro he
    exact hc.2 ((Z_neighbor_le_V F hab.symm).trans (he.trans (source_Z_Q_U ht a').2))
  have hroot := source_path_normalized_sylow_image ht (V F a' 1) hV'L hV'm hesc'
    (stabilizer_normalizes_V F a' 1) e T hT hK
  obtain ⟨_,_,f,_,_,_,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  let e' := f.trans e
  have hneq : beta ≠ a' := by
    intro he
    rw [he,SimpleGraph.dist_self,hb3] at hd
    omega
  obtain ⟨T',hT',hK',_⟩ := reduced_linear_path_borel_image h hob models ham hbm hneq.symm e'
  have hroot' := source_path_normalized_sylow_image ht (V F beta 1) hVL' hVm hesc
    (stabilizer_normalizes_V F beta 1) e' T' hT' hK'
  have index {v : Vertex F} (A : Subgroup (Reduction.G₀ J S₀)) (hAL : A ≤ graphLocalGroup F v)
      (ev : (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,k))
      (R : Sylow 2 SL(2,k))
      (hR : (A.subgroupOf (graphLocalGroup F v)).map
        (ev.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup F v)))) = R) :
      (Q F v).relIndex A = Nat.card k := by
    let L := graphLocalGroup F v
    let q := ev.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    have hk : q.ker = (Q F v).subgroupOf L := by
      rw [MonoidHom.ker_comp_of_injective _ _ ev.injective,QuotientGroup.ker_mk']
      have hcore : (pCore 2 L).map L.subtype = Q F v := graphLocalGroup_core ht v
      rw [←hcore]
      exact (comap_map_eq_self_of_injective L.subtype_injective _).symm
    have hh := Representation.BinaryConjugationSection.actor_image_card_eq_relIndex L (Q F v) A q hk hAL
    change (A.subgroupOf L).map q = R at hR
    rw [hR] at hh
    exact hh.symm.trans (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 R).symm.toEquiv)
  refine ⟨hb3,index _ hV'L e T hroot,index _ hVL' e' T' hroot',mid,hbm,ham,?_,?_⟩
  · exact fun D hAD hDA hn => source_path_root_interval ht (V F a' 1) hV'L e T hroot hK D hAD hDA hn
  · exact fun D hAD hDA hn => source_path_root_interval ht (V F beta 1) hVL' e' T' hroot' hK' D hAD hDA hn

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
