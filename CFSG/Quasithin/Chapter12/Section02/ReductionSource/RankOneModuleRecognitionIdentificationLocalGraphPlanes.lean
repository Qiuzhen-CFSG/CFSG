module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalGraphPlanes
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalGraphNeighbor

/-!
# The field planes on the original Chapter 12 graph

The actual index-two moving pair has both centralizer planes of order four.
The opposite endpoint seed normalizes the original elementary H-closure,
so its commutator with the normalizer hyperplane is precisely its fixed
plane. The natural field-action dichotomy gives the second fixed plane.
The coordinates of both planes are the literal inverse conjugations of
the original commutator layer. Once the reverse normalizer has index two,
hyperplane rigidity supplies a nonidentity point in both seeds.

This discharges the field-plane paragraph of 6.2.8. The reverse neighbor
and non-two pair still have to be constructed for the final core escape.
Source: Aschbacher--Smith, 6.2.8, printed pp.684--685, applied in
12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterF.Section07.Track CFSG.Quasithin.ChapterF.Section07.CriticalPairs
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- The two field planes for the actual moving neighbors of the original
LT--H graph, with the natural-module coordinates retained explicitly. -/
theorem source_local_graph_field_planes
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
        let X := (firstModule F d.seed α).map K.subtype
        let Y := (firstModule F d.seed β).map K.subtype
        let Uα := X ⊓ centralizer (Y : Set G)
        let Uβ := Y ⊓ centralizer (X : Set G)
        (((vertexModule F d.seed (base F true)).map K.subtype) ⊓
          normalizer (X : Set G)).relIndex
            ((vertexModule F d.seed (base F true)).map K.subtype) = 2 ∧
        (Y ⊓ normalizer (X : Set G)).relIndex Y = 2 ∧
        ¬ X ≤ normalizer (Y : Set G) ∧
        ⁅Y ⊓ normalizer (X : Set G),X⁆ = Uα ∧ Nat.card Uα = 4 ∧ Nat.card Uβ = 4 ∧
        ∃ a b : G, X = (commutatorLayer T L).map (MulAut.conj a).toMonoidHom ∧
          Y = (commutatorLayer T L).map (MulAut.conj b).toMonoidHom ∧
          IsInvolutoryFieldFixedSpace L (normalizer (L : Set G)) (commutatorLayer T L)
            (Uα.map (MulAut.conj a⁻¹).toMonoidHom) n ∧
          IsInvolutoryFieldFixedSpace L (normalizer (L : Set G)) (commutatorLayer T L)
            (Uβ.map (MulAut.conj b⁻¹).toMonoidHom) n ∧
          ((X ⊓ normalizer (Y : Set G)).relIndex X = 2 →
            ∃ w ∈ X ⊓ Y, w ≠ (1 : G)) := by
  let K := (L ⊔ (T : Subgroup G)) ⊔ H
  let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
    else (L ⊔ (T : Subgroup G)).subgroupOf K
  obtain ⟨d,hne,hseed,hodd,hb,e,α,β,hα,hβ,hi,hiβ,hn⟩ :=
    source_local_graph_moving_pair D h h611 hnatural hz ho hH hHz hcore
  let U0 := vertexModule F d.seed (base F true)
  let U := U0.map K.subtype
  let X := (firstModule F d.seed α).map K.subtype
  let Y := (firstModule F d.seed β).map K.subtype
  change (Y ⊓ normalizer (X : Set G)).relIndex Y = 2 at hiβ
  change ¬ X ≤ normalizer (Y : Set G) at hn
  have htrue : (F true).map K.subtype = H := map_subgroupOf_eq_of_le le_sup_right
  have hcore' : d.seed ≤ (F true).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rw [map_pCoreIn_of_injective 2 _ _ K.subtype_injective,htrue,hseed]
    exact hcore
  have hU0 : IsElementaryAbelian 2 U0 := by
    rw [show U0 = vertexModule F d.seed (base F true) from rfl,
      second_base_module_eq_conjugate_join F d.seed d.seed_normalized]
    exact Completion.conjugate_join_elementary_of_odd F d hne hcore' hodd
  let _ := hU0
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  have hYU : Y ≤ U := map_mono (firstModule_le_vertexModule_of_adj F d.seed rfl hβ)
  have hXU : X ≤ normalizer (U : Set G) := by
    have hX0 : firstModule F d.seed α ≤ F true :=
      (firstModule_le_vertexModule_of_adj F d.seed rfl hα).trans (e.endpoint_module_le hb)
    have hN : F true ≤ normalizer (U0 : Set K) := by
      simpa only [Subgroup.CosetGeometry.stabilizer_base] using
        stabilizer_normalizes_vertexModule F d.seed d.seed_normalized (base F true)
    exact (map_mono (hX0.trans hN)).trans (U0.le_normalizer_map K.subtype)
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
  change X = (commutatorLayer T L).map (MulAut.conj a).toMonoidHom at ha
  change Y = (commutatorLayer T L).map (MulAut.conj b).toMonoidHom at hb'
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  obtain ⟨hcomm,hCa,hCb,hfa,hfb⟩ := local_conjugate_graph_pair_planes h611 hnatural hE a b U
    (hb' ▸ hYU) (ha ▸ hXU) (by rwa [ha,hb'] at hiβ) (by rwa [ha,hb'] at hn)
  refine ⟨d,hne,hseed,hodd,hb,e,α,β,hα,hβ,hi,hiβ,hn,?_,?_,?_,a,b,ha,hb',?_,?_,?_⟩
  · change ⁅Y ⊓ normalizer (X : Set G),X⁆ = X ⊓ centralizer (Y : Set G)
    rw [ha,hb']
    exact hcomm
  · change Nat.card (X ⊓ centralizer (Y : Set G) : Subgroup G) = 4
    rw [ha,hb']
    exact hCa
  · change Nat.card (Y ⊓ centralizer (X : Set G) : Subgroup G) = 4
    rw [ha,hb']
    exact hCb
  · change IsInvolutoryFieldFixedSpace L (normalizer (L : Set G)) (commutatorLayer T L)
      ((X ⊓ centralizer (Y : Set G)).map (MulAut.conj a⁻¹).toMonoidHom) n
    rw [ha,hb']
    exact hfa
  · change IsInvolutoryFieldFixedSpace L (normalizer (L : Set G)) (commutatorLayer T L)
      ((Y ⊓ centralizer (X : Set G)).map (MulAut.conj b⁻¹).toMonoidHom) n
    rw [ha,hb']
    exact hfb
  · change (X ⊓ normalizer (Y : Set G)).relIndex X = 2 → ∃ w ∈ X ⊓ Y, w ≠ (1 : G)
    intro hr
    rw [ha,hb'] at hr ⊢
    exact local_conjugate_graph_pair_common_point h611 hnatural hE a b hr
      (by rwa [ha,hb'] at hiβ) hCb

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
