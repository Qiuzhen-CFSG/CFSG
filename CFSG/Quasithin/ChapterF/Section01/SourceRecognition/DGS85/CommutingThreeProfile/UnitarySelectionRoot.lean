module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.UnitaryThreePathImage
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.UnitarySelectionCentralizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.UnitaryApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FullCoreProduct

/-!
# The constructed involution in the original unitary root quotient

Use the original (12.5) element, already constructed in the intersection of
V_y and the two remote cores. Construct an actual three-path z--y--m--x:
finite valence supplies z, and the original critical pair proves x ≠ y.
The earlier source bound s > 3 makes its interior-core intersection fill
the incoming Sylow at x. The original linear common Sylow supplies the full
edge product; conjugation transports the original nonbinary unitary marking
to x and supplies all local model hypotheses used by the path theorem.

The centralizer of the same involution therefore has image index at most q
in that Sylow, and image order at least q² in the literal x quotient. Both the canonical quotient projection
and the inclusion into the original completion are retained. No additional
three-path, common-Sylow image, local model, or centralizer-index premise is
introduced. The source's subsequent centralizer transitivity and unitary
contradiction, the binary alternatives, exhaustive Suzuki selection, and
remaining Chapter 12/13.1 premise discharge remain with this theorem family.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.5), printed p.182, using the original (12.1) inputs and (12.4)(b).
-/

public noncomputable section
open Subgroup SimpleGraph BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem unitary_marking_at
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n) ∨
      IsSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n))
    (v : Vertex (reducedFamily L S)) (hv : v.type = i) :
    ClassicalGroup.IsPSU (graphLocalGroup (reducedFamily L S) v ⧸ pCore 2 (graphLocalGroup (reducedFamily L S) v)) 3 (2^n) ∨
      IsSU (graphLocalGroup (reducedFamily L S) v ⧸ pCore 2 (graphLocalGroup (reducedFamily L S) v)) 3 (2^n) := by
  let F := reducedFamily L S
  let A := graphLocalGroup F (base F i)
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  have heq : A.map (MulAut.conj g).toMonoidHom = graphLocalGroup F v :=
    (graphLocalGroup_conjugate (reduced_triple h) g (base F i)).symm.trans
      (congrArg (graphLocalGroup F) hg)
  let a : A ≃* graphLocalGroup F v :=
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr heq)
  let eQ := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    have e' : (family L i ⧸ pCore 2 (family L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J := by
      cases i <;> exact e
    exact Or.inl ⟨K,inferInstance,inferInstance,J,hK,hconj,
      ⟨eQ.symm.trans (reduced_graphProjectiveUnitaryQuotient h i J hn hK hconj e')⟩⟩
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    have e' : (family L i ⧸ pCore 2 (family L i)) ≃* J.specialSubgroup := by
      cases i <;> exact e
    exact Or.inr ⟨K,inferInstance,inferInstance,J,hK,hconj,
      ⟨eQ.symm.trans (reduced_graphSpecialUnitaryQuotient h i J hn hK hconj e')⟩⟩

private theorem linear_unitary_models
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 2 ≤ n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hu : ClassicalGroup.IsPSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n) ∨
      IsSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n))
    (v : Vertex (reducedFamily L S)) :
    IsRankOneModel (graphLocalGroup (reducedFamily L S) v ⧸ pCore 2 (graphLocalGroup (reducedFamily L S) v)) := by
  let F := reducedFamily L S
  have hb (j : Bool) : IsRankOneModel (graphLocalGroup F (base F j) ⧸ pCore 2 (graphLocalGroup F (base F j))) := by
    by_cases hj : j=i
    · subst j
      rcases unitary_marking_at h i hn hu (base F i) rfl with hp | hs
      · exact .projective_unitary n (by omega) hp
      · exact .special_unitary n (by omega) hs
    · have hj : j = !i := Bool.eq_not_iff.mpr hj
      subst j
      let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
        MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
          ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
      have e' : (family L (!i) ⧸ pCore 2 (family L (!i))) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k := by
        cases i <;> exact eLin.trans ep
      have hq : IsRankOneModel (family L (!i) ⧸ pCore 2 (family L (!i))) := by
        cases i
        · exact h.quotient 1
        · exact h.quotient 0
      exact hq.of_equiv ((reduced_graphLinearQuotient h (!i) e').trans e'.symm)
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  let A := graphLocalGroup F (base F v.type)
  have heq : A.map (MulAut.conj g).toMonoidHom = graphLocalGroup F v :=
    (graphLocalGroup_conjugate (reduced_triple h) g (base F v.type)).symm.trans
      (congrArg (graphLocalGroup F) hg)
  let a : A ≃* graphLocalGroup F v :=
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr heq)
  exact (hb v.type).of_equiv (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm

private theorem linear_common_sylow_full_edge
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {v w : Vertex (reducedFamily L S)} (hvw : (graph (reducedFamily L S)).Adj v w) :
    Q (reducedFamily L S) v ⊔ Q (reducedFamily L S) w =
      (stabilizer (reducedFamily L S) v ⊓ stabilizer (reducedFamily L S) w).pCoreIn 2 := by
  let F := reducedFamily L S
  let A := star L S i
  let E := stabilizer F (base F i) ⊓ stabilizer F (base F (!i))
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F (base F i) from inf_le_left)) (inclusion_injective _)
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  let d := reducedFullEarlierLocalTheorems h
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow (reduced_triple h) (reduced_borel_core_sylow h) d hadj
  have hEA : E.pCoreIn 2 ≤ A := by
    have hh := (hT ▸ map_subtype_le (T : Subgroup (d.localGroup (base F i))))
    change E.pCoreIn 2 ≤ graphLocalGroup F (base F i) at hh
    rwa [source_linear_graphLocalGroup_eq_star h i e] at hh
  have hRE : (R : Subgroup A).map A.subtype ≤ E := by
    rw [hR]
    apply sup_le
    · exact (source_Z_Q_U (reduced_triple h) (base F (!i))).2.trans
        ((ballKernel_one_le_edge F hadj.symm).trans (by rw [inf_comm]))
    · exact (source_Z_Q_U (reduced_triple h) (base F i)).2.trans (ballKernel_one_le_edge F hadj)
  have hRQ : (R : Subgroup A).map A.subtype ≤ E.pCoreIn 2 :=
    pGroup_le_core_of_core_sylow E _ hRE (R.isPGroup'.map _) (source_edge_core_sylow (reduced_triple h) (reduced_borel_core_sylow h) hadj)
  have hRN : (R : Subgroup A) ≤ (E.pCoreIn 2).subgroupOf A := fun r hr => hRQ (mem_map_of_mem A.subtype hr)
  have he : (E.pCoreIn 2).subgroupOf A = (R : Subgroup A) :=
    R.is_maximal' (isPGroup_pCoreIn 2 E).comap_subtype hRN
  have hh := congrArg (Subgroup.map A.subtype) he
  rw [map_subgroupOf_eq_of_le hEA,hR] at hh
  exact source_full_core_product_all_edges F hadj (by simpa only [sup_comm] using hh.symm) hvw

/-- The involution constructed from the two original remote paths has an actual
unitary centralizer image of index at most q in the displayed Sylow and
order at least q² at the opposite endpoint. -/
theorem source_unitary_selection_centralizer_root
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmx : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) (!i)) x)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    {n : ℕ} (hn : 2 ≤ n) (hfield : Nat.card k = 2^n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hu : ClassicalGroup.IsPSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n) ∨
      IsSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n))
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = 2^n)
    (T : Sylow 2 (star L S i)) (R : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    {u v d e : Vertex (reducedFamily L S)}
    (hyu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) u)
    (hyv : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) v)
    (p : (graph (reducedFamily L S)).Walk u d) (hp : p.length = 4)
    (r : (graph (reducedFamily L S)).Walk v e) (hr : r.length = 2)
    (hs : 3 < sourceS (P := fun j => (P₀ L S j).subgroupOf (G₀ L S))) :
    let F := reducedFamily L S
    let y := base F i
    let m := base F (!i)
    let A := graphLocalGroup F x
    let I := Q F y ⊓ Q F m
    ∃ t : G₀ L S, t ∈ V F y 1 ⊓ (Q F d ⊓ Q F e) ∧ t ≠ 1 ∧ t^2 = 1 ∧
      Z F y ⊔ Z F d ⊔ Z F e ≤ centralizer ({t} : Set (G₀ L S)) ∧
      (∃ T : Sylow 2 (A ⧸ pCore 2 A),
        (I.subgroupOf A).map (QuotientGroup.mk' (pCore 2 A)) = T ∧
        (((I ⊓ centralizer ({t} : Set (G₀ L S))).subgroupOf A).map
          (QuotientGroup.mk' (pCore 2 A))).relIndex (T : Subgroup (A ⧸ pCore 2 A)) ≤ 2^n) ∧
      (2^n)^2 ≤ (Q F x).relIndex (I ⊓ centralizer ({t} : Set (G₀ L S))) ∧
      (2^n)^2 ≤ Nat.card (((I ⊓ centralizer ({t} : Set (G₀ L S))).subgroupOf A).map
        (QuotientGroup.mk' (pCore 2 A))) ∧
      (t : G) ≠ 1 ∧
      (2^n)^2 ≤ ((Q F x).map (G₀ L S).subtype).relIndex
        ((I ⊓ centralizer ({t} : Set (G₀ L S))).map (G₀ L S).subtype) := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let d₀ := reducedFullEarlierLocalTheorems h
  obtain ⟨_,_,_,_,t,ht,ht1,ht2,hi,hZ,htG,_⟩ := source_unitary_selection_centralizer
    h i hb hc hxa hmx hzy hcomm hn hfield eLin hu hcard T R hT hR hyu hyv p hp r hr
  have hxy : x ≠ y := by
    intro he
    have hd := hc.1
    have he1 : (graph F).dist a y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr (he ▸ hxa.symm)
    rw [he1] at hd
    omega
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hval : 1 < ((graph F).neighborSet y).ncard := by
    change 1 < Nat.card ((graph F).neighborSet y)
    rw [card_neighbors_of_indices F
      (fun j => ((F (!j)).subgroupOf (F j)).index) (fun _ => rfl)]
    exact lt_of_lt_of_le (by decide) (source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) y.type)
  obtain ⟨z,hz,hzn⟩ := Set.exists_ne_of_one_lt_ncard hval m
  have hzy₀ : (graph F).Adj z y := (show (graph F).Adj y z from hz).symm
  let p₀ : BasedWalk (graph F) 3 z := ⟨⟨y,hzy₀⟩,⟨⟨m,hadj⟩,⟨⟨x,hmx⟩,PUnit.unit⟩⟩⟩
  have hp₀ : p₀.Nonbacktracking := ⟨hzn.symm,hxy,trivial⟩
  have hprod : Q F m ⊔ Q F x = (stabilizer F x ⊓ stabilizer F m).pCoreIn 2 := by
    simpa only [Bool.not_not,inf_comm] using
      linear_common_sylow_full_edge h (!i) eLin R (by simpa only [Bool.not_not] using hR) hmx
  have hx : x.type = i := by
    have ht : x.type ≠ !i := hmx.1.symm
    simpa only [Bool.not_not] using Bool.eq_not_iff.mpr ht
  have hunitary := unitary_marking_at h i hn hu x hx
  have hmodels : ∀ v, IsRankOneModel (d₀.localGroup v ⧸ pCore 2 (d₀.localGroup v)) :=
    linear_unitary_models h i hn eLin hu
  obtain ⟨himage,hlower,hcardImage⟩ := unitary_three_path_centralizer_image
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    d₀ hmodels hs p₀ hp₀ hprod (by omega) hunitary t hi
  refine ⟨t,ht,ht1,ht2,hZ,himage,hlower,hcardImage,htG,?_⟩
  rwa [relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
