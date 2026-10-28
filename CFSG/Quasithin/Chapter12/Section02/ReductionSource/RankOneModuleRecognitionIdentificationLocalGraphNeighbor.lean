module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalGraphNeighbor
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalGraph
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalFiveOuter

/-!
# The index-two graph neighbor on the original Chapter12 layer

In the contrary core branch the actual minimal H-star vertex has generation
parameter one and a unique maximal subgroup containing T. Its intersection
with the normalizer of the original layer is exactly H intersect M. These
source inputs give the first F.7.13 neighbor in the original LT--H graph,
with index two on the actual elementary H-conjugate closure.

This is the first neighbor selection in 6.2.8. The field-plane analysis,
reverse neighbor and non-two pair still have to be supplied before the core
escape and LocalAnalysis can be assembled. Choosing the original H-star vertex still uses the earlier 6.1.5 escape;
this module applies to that chosen vertex without assuming the escape.
Source: Aschbacher--Smith, 6.2.8, printed pp.684--685, and F.7.13(1),
printed p.314; the Chapter12 application is 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterF.Section07.Track CFSG.Quasithin.ChapterF.Section07.CriticalPairs
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- The first index-two neighbor in source 6.2.8 on the literal Chapter12
coset graph, with all E-generation and normalizer inputs discharged. -/
theorem source_local_graph_index_two_neighbor
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ centralizer ({z} : Set G))
    (hcore : commutatorLayer T L ≤ H.pCoreIn 2) :
    let K := (L ⊔ (T : Subgroup G)) ⊔ H
    let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
      else (L ⊔ (T : Subgroup G)).subgroupOf K
    ∃ (d : SourceSetup F) (hne : d.V ≠ ⊥),
      d.seed.map K.subtype = commutatorLayer T L ∧
      Odd (d.track hne) ∧ 3 ≤ d.track hne ∧
      ∃ (e : NormalizedEndpoint d hne) (α : Vertex F),
        (graph F).Adj e.vertex α ∧
        (((vertexModule F d.seed (base F true)).map K.subtype) ⊓
          normalizer ((firstModule F d.seed α).map K.subtype : Set G)).relIndex
            ((vertexModule F d.seed (base F true)).map K.subtype) = 2 := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hN : H ⊓ normalizer (commutatorLayer T L : Set G) = H ⊓ normalizer (L : Set G) := by
    apply le_antisymm (inf_le_inf_left _ hE.normalizer_le)
    intro x hx
    have he := local_layer_normalizer hE hz ho
    exact ⟨hx.1,(he.symm.le ⟨hHz hx.1,hx.2⟩).2⟩
  exact local_graph_index_two_neighbor h611 hnatural hE
    (source_central_line_normalizer_factorization D h.toHypothesis1221 h611 hnatural.2.2.2.1)
    (Chapter4.Section03.RankOneUniqueness.unique_sylow_join D h.toHypothesis1221).2.2 hH hN hcore

end CFSG.Quasithin.Chapter12.Section02.RankOneModule


namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterF.Section07.Track CFSG.Quasithin.ChapterF.Section07.CriticalPairs
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

private theorem pair_centralizes_of_normalizes
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (a b : G)
    (hAB : (commutatorLayer T L).map (MulAut.conj a).toMonoidHom ≤
      normalizer ((commutatorLayer T L).map (MulAut.conj b).toMonoidHom : Set G)) :
    (commutatorLayer T L).map (MulAut.conj b).toMonoidHom ≤
      centralizer ((commutatorLayer T L).map (MulAut.conj a).toMonoidHom : Set G) := by
  have hh := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hAB
  rw [fusion_map_conj_inverse,map_equiv_normalizer_eq,fusion_map_conj_mul] at hh
  have hc := source_local_one_sided_centralizes D h h611 hnatural (a⁻¹*b) hh
  have hm := map_mono (f := (MulAut.conj a).toMonoidHom) hc
  rw [fusion_map_conj_mul,mul_inv_cancel_left,Theory.Quasithin.map_centralizer] at hm
  exact hm

/-- The two actual graph seeds selected in the first paragraph of 6.2.8:
beta has normalizer of index two on alpha, and neither seed normalizes
the other. The reverse nonnormalization uses the proved source 6.2.7. -/
theorem source_local_graph_moving_pair
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ centralizer ({z} : Set G))
    (hcore : commutatorLayer T L ≤ H.pCoreIn 2) :
    let K := (L ⊔ (T : Subgroup G)) ⊔ H
    let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
      else (L ⊔ (T : Subgroup G)).subgroupOf K
    ∃ (d : SourceSetup F) (hne : d.V ≠ ⊥),
      d.seed.map K.subtype = commutatorLayer T L ∧
      Odd (d.track hne) ∧ 3 ≤ d.track hne ∧
      ∃ (e : NormalizedEndpoint d hne) (α β : Vertex F),
        (graph F).Adj e.vertex α ∧ (graph F).Adj (base F true) β ∧
        (((vertexModule F d.seed (base F true)).map K.subtype) ⊓
          normalizer ((firstModule F d.seed α).map K.subtype : Set G)).relIndex
            ((vertexModule F d.seed (base F true)).map K.subtype) = 2 ∧
        (((firstModule F d.seed β).map K.subtype) ⊓
          normalizer ((firstModule F d.seed α).map K.subtype : Set G)).relIndex
            ((firstModule F d.seed β).map K.subtype) = 2 ∧
        ¬ (firstModule F d.seed α).map K.subtype ≤
          normalizer ((firstModule F d.seed β).map K.subtype : Set G) := by
  let K := (L ⊔ (T : Subgroup G)) ⊔ H
  let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
    else (L ⊔ (T : Subgroup G)).subgroupOf K
  obtain ⟨d,hne,hseed,hodd,hb,e,α,hα,hi⟩ :=
    source_local_graph_index_two_neighbor D h h611 hnatural hz ho hH hHz hcore
  obtain ⟨β,hβ,hiβ⟩ := local_graph_select_moving_seed F d K.subtype α hi
  refine ⟨d,hne,hseed,hodd,hb,e,α,β,hα,hβ,hi,hiβ,?_⟩
  have hconj (v : Vertex F) (hv : v.type = false) :
      ∃ a : G, (firstModule F d.seed v).map K.subtype =
        (commutatorLayer T L).map (MulAut.conj a).toMonoidHom := by
    obtain ⟨a,ha⟩ := Subgroup.CosetGeometry.exists_smul_base F v
    rw [hv] at ha
    refine ⟨a,?_⟩
    rw [←ha,firstModule_translate_base F d.seed d.seed_normalized,map_map]
    have he : K.subtype.comp (MulAut.conj a).toMonoidHom =
        (MulAut.conj (a:G)).toMonoidHom.comp K.subtype := rfl
    rw [he,←map_map,hseed]
  have hαt : α.type = false := by
    have hh : true ≠ α.type := hα.1
    cases ht : α.type
    · rfl
    · exact (hh ht.symm).elim
  have hβt : β.type = false := by
    have hh : true ≠ β.type := hβ.1
    cases ht : β.type
    · rfl
    · exact (hh ht.symm).elim
  obtain ⟨a,ha⟩ := hconj α hαt
  obtain ⟨b,hb'⟩ := hconj β hβt
  intro hn
  rw [ha,hb'] at hn
  have hc := pair_centralizes_of_normalizes D h h611 hnatural a b hn
  have hbn : (firstModule F d.seed β).map K.subtype ≤
      normalizer ((firstModule F d.seed α).map K.subtype : Set G) := by
    rw [ha,hb']
    exact hc.trans (Subgroup.centralizer_le_normalizer _)
  have he := relIndex_eq_one.mpr (le_inf le_rfl hbn)
  rw [hiβ] at he
  omega
end CFSG.Quasithin.Chapter12.Section02.RankOneModule
