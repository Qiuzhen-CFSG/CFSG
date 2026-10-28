module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.RemoteCenterPropagation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.PathCoreControl
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCenterPair
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.Transport

/-!
# Centralizer propagation along the actual nine-path

Critical-center saturation identifies the image of the remote center with
the previously computed span image, of order q. Conjugating the common
Sylow and all graph vertices together gives the same index for any incoming
edge, so neither of the two numerical indices is an extra path premise.

For a nonbacktracking nine-path with its fourth and fifth vertices at the
base edge, every two-subgroup of the path fixer lies in all eight interior
cores. It therefore centralizes the centers at vertices two, four, five
and eight. The critical pairs at vertices two/five and eight/five supply
the two remote-center indices. RemoteCenterPropagation now proves that
the whole span at vertex five centralizes that path subgroup, also after
the original completion inclusion. Both orientations are included.

Source: DGS85, Groups and Graphs, (12.3)(a), (12.4)(b), (12.7), printed
pp.179,181,184. The source critical pairs and common Sylows remain earlier
inputs. This proves the first propagation in (12.7) for q > 2; the subsequent
centralizer case analysis, the binary parameter and the assertion that
nine-path fixers have odd order remain to be proved.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem critical_center_index_base
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex (Z (reducedFamily L S) a) = 2^(2*n+1) := by
  let F := reducedFamily L S
  let A := star L S i
  let y := base F i
  let m := base F (!i)
  have hbase : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hs := source_suzuki_critical_center_saturation h i hb hc hxa hxm hn eSuz eLin R hR
  have hi := (source_suzuki_first_index h i hb hc hxa hxm hbase hn eSuz eLin R hR).1
  have hVA : V F x 1 ≤ A := (V_le_neighbor_Q F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hxm).trans
      ((le_sup_left.trans hR.ge).trans (map_subtype_le _))
  have hZA : Z F a ≤ A := (Z_neighbor_le_V F hxa).trans hVA
  have hQA : Q F y ≤ A := (le_sup_right.trans hR.ge).trans (map_subtype_le _)
  let : ((Q F y).subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer
    ((star_le_stabilizer i).trans (stabilizer_normalizes_Q F y))
  rw [inf_relIndex_left] at hi
  have he := congrArg (Subgroup.subgroupOf · A) hs
  rw [subgroupOf_sup hVA hQA,subgroupOf_sup hZA hQA] at he
  calc
    (Q F y).relIndex (Z F a) = ((Q F y).subgroupOf A).relIndex ((Z F a).subgroupOf A) := (relIndex_subgroupOf hZA).symm
    _ = ((Q F y).subgroupOf A).relIndex ((Z F a).subgroupOf A ⊔ (Q F y).subgroupOf A) := (relIndex_sup_right _ _).symm
    _ = ((Q F y).subgroupOf A).relIndex ((V F x 1).subgroupOf A ⊔ (Q F y).subgroupOf A) := by rw [he]
    _ = ((Q F y).subgroupOf A).relIndex ((V F x 1).subgroupOf A) := relIndex_sup_right _ _
    _ = (Q F y).relIndex (V F x 1) := relIndex_subgroupOf hVA
    _ = _ := hi

/-- The actual critical center has image of order q through any incoming edge. -/
theorem source_suzuki_critical_center_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x m : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) m)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) m ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex (Z (reducedFamily L S) a) = 2^(2*n+1) := by
  let F := reducedFamily L S
  let A := star L S i
  let y := base F i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  change IsCriticalPair F a y at hc
  have hbase : (graph F).Adj y (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨g,hg,hgm⟩ := star_locally_transitive h i hym hbase
  have hgy : g • y = y := star_le_stabilizer i hg
  let t : A := ⟨g,hg⟩
  let R' := R.mapSurjective (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).surjective
  have hf : A.subtype.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp A.subtype := by ext u; rfl
  have hR' : (R' : Subgroup A).map A.subtype = Q F (base F (!i)) ⊔ Q F y := by
    change ((R : Subgroup A).map (MulAut.conj t).toMonoidHom).map A.subtype = _
    rw [map_map,hf,←map_map,hR,Subgroup.map_sup,←Q_translate F,←Q_translate F,hgm,hgy]
  have hca : IsCriticalPair F (g • a) y := by
    simpa only [hgy] using criticalPair_translate F hc g
  have hax : (graph F).Adj (g • x) (g • a) :=
    (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hxa
  have hmx : (graph F).Adj (g • x) (base F (!i)) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hxm
    change (graph F).Adj (g • x) (g • m) at hh
    rwa [hgm] at hh
  have hi := critical_center_index_base h i hb hca hax hmx hn eSuz eLin R' hR'
  have he := relIndex_map_map_of_injective (Q F y) (Z F a) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [←Q_translate F,←Z_translate F,hgy] at he
  exact he.symm.trans hi
open SimpleGraph
open scoped MatrixGroups

/-- For an actual nine-path, the two remote critical centers propagate its two-subgroups
into the centralizer of the whole middle Suzuki span. -/
theorem source_suzuki_nine_path_span_centralizer
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    (hy : (p.2.2.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (p.2.2.2.2.2.1 : Vertex (reducedFamily L S)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hca : IsCriticalPair (reducedFamily L S)
      (p.2.1 : Vertex (reducedFamily L S)) (base (reducedFamily L S) i))
    (hcc : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (base (reducedFamily L S) i))
    (D : Subgroup (G₀ L S)) (hD : IsPGroup 2 D)
    (hfix : D ≤ pathStabilizer (reducedFamily L S) p) :
    let F := reducedFamily L S
    V F (base F i) 1 ≤ centralizer (D : Set (G₀ L S)) ∧
    (V F (base F i) 1).map (G₀ L S).subtype ≤ centralizer (D.map (G₀ L S).subtype : Set G) := by
  let F := reducedFamily L S
  have hcore := source_mixed_path_two_subgroup_core h (!i) eLin
    (by cases i <;> exact eSuz) p hp D hD hfix
  rcases p with ⟨⟨v1,h01⟩,⟨⟨v2,h12⟩,⟨⟨v3,h23⟩,⟨⟨v4,h34⟩,⟨⟨v5,h45⟩,
    ⟨⟨v6,h56⟩,⟨⟨v7,h67⟩,⟨⟨v8,h78⟩,⟨⟨v9,h89⟩,tail⟩⟩⟩⟩⟩⟩⟩⟩⟩
  change v4 = base F (!i) at hm
  change v5 = base F i at hy
  change IsCriticalPair F v2 (base F i) at hca
  change IsCriticalPair F v8 (base F i) at hcc
  change (R : Subgroup (star L S i)).map (star L S i).subtype = Q F v6 ⊔ Q F (base F i) at hR
  change (graph F).Adj v2 v3 at h23
  change (graph F).Adj v3 v4 at h34
  change (graph F).Adj v4 v5 at h45
  change (graph F).Adj v5 v6 at h56
  change (graph F).Adj v6 v7 at h67
  change (graph F).Adj v7 v8 at h78
  have hia := source_suzuki_critical_center_index h i hb hca h23.symm h34
    (by rw [←hy]; exact h45.symm) hn eSuz eLin T (by rw [hm]; exact hT)
  have hic := source_suzuki_critical_center_index h i hb hcc h78 h67.symm
    (by rw [←hy]; exact h56) hn eSuz eLin R hR
  have hne : v6 ≠ v4 := hp.2.2.2.2.1
  have hd24 : (graph F).dist v2 v4 ≤ 2 := by
    exact (SimpleGraph.dist_le (SimpleGraph.Walk.cons h23 (SimpleGraph.Walk.cons h34 .nil))).trans_eq (by rfl)
  have hd86 : (graph F).dist v8 v6 ≤ 2 := by
    exact (SimpleGraph.dist_le (SimpleGraph.Walk.cons h78.symm (SimpleGraph.Walk.cons h67.symm .nil))).trans_eq (by rfl)
  have hZa := CommutingNontrivial.Z_le_Q_of_dist_lt_b F (fun v => (source_Z_Q_U (reduced_triple h) v).1)
    v2 v4 (lt_of_le_of_lt hd24 hb) (reduced_kernel_sylow h v4)
  have hZc := CommutingNontrivial.Z_le_Q_of_dist_lt_b F (fun v => (source_Z_Q_U (reduced_triple h) v).1)
    v8 v6 (lt_of_le_of_lt hd86 hb) (reduced_kernel_sylow h v6)
  have hDm : D ≤ Q F v4 := hcore v4 (by change v4 ∈ [v1,v2,v3,v4,v5,v6,v7,v8]; simp)
  have hDy : D ≤ Q F v5 := hcore v5 (by change v5 ∈ [v1,v2,v3,v4,v5,v6,v7,v8]; simp)
  have hDa : D ≤ Q F v2 := hcore v2 (by change v2 ∈ [v1,v2,v3,v4,v5,v6,v7,v8]; simp)
  have hDc : D ≤ Q F v8 := hcore v8 (by change v8 ∈ [v1,v2,v3,v4,v5,v6,v7,v8]; simp)
  have hCa : Z F v2 ≤ centralizer (D : Set (G₀ L S)) :=
    (Z_centralizes_Q F v2 (source_Z_Q_U (reduced_triple h) v2).1).trans (centralizer_le hDa)
  have hCc : Z F v8 ≤ centralizer (D : Set (G₀ L S)) :=
    (Z_centralizes_Q F v8 (source_Z_Q_U (reduced_triple h) v8).1).trans (centralizer_le hDc)
  rw [hm] at hZa hDm hne
  change (graph F).Adj v5 v6 at h56
  rw [hy] at hDy h56
  exact source_suzuki_remote_center_propagation h i hn eSuz h56 hne T R hT hR
    hZa hZc hia hic D hDy hDm hCa hCc

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
