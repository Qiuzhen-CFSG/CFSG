module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalGraphReverse
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalGraphPlanes

/-!
# Source 6.2.8 on the original Chapter 12 layer

Choose the reverse neighbor in the original LT--H graph. Source 6.2.7
forces it to move the endpoint seed, so the original closure index gives
the forward index two as well. The two endpoint closures now give both
field planes, both commutator identities and a nonidentity common point.

If the layer lay in the marked centralizer core, natural point transitivity
and the core's normalization of every layer through the marked point would
force the two seeds to normalize each other. Their actual index two is the
contradiction. This proves the 6.2.8 core escape directly, retaining only
the earlier marked-centralizer escape used to choose H. In particular no
reverse-index, common-point or terminal-pair premise remains.

Source: Aschbacher--Smith, 6.2.8, pp.684--685, applied to the literal
[R₂(LT),L] in 12.2.2(3d), p.795. The simultaneous point/core transport is
an alternative to the printed F.7.13(2) non-two-pair argument.
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
theorem source_local_graph_symmetric_pair
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
        (X ⊓ normalizer (Y : Set G)).relIndex X = 2 ∧
        ¬ X ≤ H.pCoreIn 2 ∧ ¬ X ≤ normalizer (Y : Set G) ∧
        ⁅Y ⊓ normalizer (X : Set G),X⁆ = Uα ∧
        ⁅X ⊓ normalizer (Y : Set G),Y⁆ = Uβ ∧ Nat.card Uα = 4 ∧ Nat.card Uβ = 4 ∧
        ∃ a b : G, X = (commutatorLayer T L).map (MulAut.conj a).toMonoidHom ∧
          Y = (commutatorLayer T L).map (MulAut.conj b).toMonoidHom ∧
          IsInvolutoryFieldFixedSpace L (normalizer (L : Set G)) (commutatorLayer T L)
            (Uα.map (MulAut.conj a⁻¹).toMonoidHom) n ∧
          IsInvolutoryFieldFixedSpace L (normalizer (L : Set G)) (commutatorLayer T L)
            (Uβ.map (MulAut.conj b⁻¹).toMonoidHom) n ∧
          (∃ w ∈ Uα ⊓ Uβ, w ≠ (1 : G)) := by
  let K := (L ⊔ (T : Subgroup G)) ⊔ H
  let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
    else (L ⊔ (T : Subgroup G)).subgroupOf K
  obtain ⟨d,hne,hseed,hodd,hb,e,α,β0,hα,hβ0,hi,hiβ0,hn0⟩ :=
    source_local_graph_moving_pair D h h611 hnatural hz ho hH hHz hcore
  have hαt : α.type = false := by
    have hh : true ≠ α.type := hα.1
    cases ht : α.type
    · rfl
    · exact (hh ht.symm).elim
  have htrue : (F true).map K.subtype = H := map_subgroupOf_eq_of_le le_sup_right
  have hXH : (firstModule F d.seed α).map K.subtype ≤ H := by
    exact (map_mono ((firstModule_le_vertexModule_of_adj F d.seed rfl hα).trans
      (e.endpoint_module_le hb))).trans_eq htrue
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hN : H ⊓ normalizer (commutatorLayer T L : Set G) = H ⊓ normalizer (L : Set G) := by
    apply le_antisymm (inf_le_inf_left _ hE.normalizer_le)
    intro x hx
    have he := local_layer_normalizer hE hz ho
    exact ⟨hx.1,(he.symm.le ⟨hHz hx.1,hx.2⟩).2⟩
  obtain ⟨hXcore,β,hβ,hr⟩ := local_graph_reverse_neighbor h611 hH hN F htrue d hseed
    α β0 hαt hXH hβ0 hn0
  let U0 := vertexModule F d.seed (base F true)
  let U := U0.map K.subtype
  let X := (firstModule F d.seed α).map K.subtype
  let Y := (firstModule F d.seed β).map K.subtype
  change (X ⊓ normalizer (Y : Set G)).relIndex X = 2 at hr
  have hn : ¬ X ≤ normalizer (Y : Set G) := by
    intro hh
    have he := relIndex_eq_one.mpr (le_inf le_rfl hh)
    rw [hr] at he
    omega
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
  let Ue0 := vertexModule F d.seed e.vertex
  let Ue := Ue0.map K.subtype
  have hUe0 : IsElementaryAbelian 2 Ue0 := by
    have he : Ue0 = U0.map (MulAut.conj (e:K)).toMonoidHom :=
      vertexModule_translate F d.seed d.seed_normalized (e:K) (base F true)
    rw [he]
    exact IsElementaryAbelian.map _
  let _ := hUe0
  let _ : IsElementaryAbelian 2 Ue := IsElementaryAbelian.map _
  have hXUe : X ≤ Ue := map_mono (firstModule_le_vertexModule_of_adj F d.seed rfl hα)
  have hYUe : Y ≤ normalizer (Ue : Set G) := by
    have hUN : U0 ≤ normalizer (Ue0 : Set K) :=
      le_normalizer_iff_commutator_le_right.mpr ((e.commutator_le hb).trans inf_le_right)
    exact hYU.trans ((map_mono hUN).trans (Ue0.le_normalizer_map K.subtype))
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
  have hβt : β.type = false := by
    have hh : true ≠ β.type := hβ.1
    cases ht : β.type
    · rfl
    · exact (hh ht.symm).elim
  obtain ⟨a,ha⟩ := hconj α hαt
  obtain ⟨b,hb'⟩ := hconj β hβt
  change X = (commutatorLayer T L).map (MulAut.conj a).toMonoidHom at ha
  change Y = (commutatorLayer T L).map (MulAut.conj b).toMonoidHom at hb'
  have hYnX : ¬ Y ≤ normalizer (X : Set G) := by
    intro hYX
    rw [ha,hb'] at hYX
    have hh := map_mono (f := (MulAut.conj b⁻¹).toMonoidHom) hYX
    rw [fusion_map_conj_inverse,map_equiv_normalizer_eq,fusion_map_conj_mul] at hh
    have hc := source_local_one_sided_centralizes D h h611 hnatural (b⁻¹*a) hh
    have hm := map_mono (f := (MulAut.conj b).toMonoidHom) hc
    rw [fusion_map_conj_mul,mul_inv_cancel_left,Theory.Quasithin.map_centralizer] at hm
    apply hn
    rw [ha,hb']
    exact hm.trans (Subgroup.centralizer_le_normalizer _)
  have hiβ : (Y ⊓ normalizer (X : Set G)).relIndex Y = 2 :=
    normalizer_relIndex_eq_two_of_index_two_overgroup Y U
      (U ⊓ normalizer (X : Set G)) X hYU hi inf_le_right
      (SetLike.not_le_iff_exists.mp hYnX)
  obtain ⟨hcomm,hcomm',hCa,hCb,hfa,hfb,hpoint⟩ :=
    local_conjugate_graph_symmetric_planes h611 hnatural hE a b U Ue
      (hb' ▸ hYU) (ha ▸ hXU) (ha ▸ hXUe) (hb' ▸ hYUe)
      (by rwa [ha,hb'] at hr) (by rwa [ha,hb'] at hiβ)
  refine ⟨d,hne,hseed,hodd,hb,e,α,β,hα,hβ,hi,hiβ,hr,hXcore,hn,?_,?_,?_,?_,a,b,ha,hb',?_,?_,?_⟩
  · change ⁅Y ⊓ normalizer (X : Set G),X⁆ = X ⊓ centralizer (Y : Set G)
    rw [ha,hb']
    exact hcomm
  · change ⁅X ⊓ normalizer (Y : Set G),Y⁆ = Y ⊓ centralizer (X : Set G)
    rw [ha,hb']
    exact hcomm'
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
  · change ∃ w ∈ (X ⊓ centralizer (Y : Set G)) ⊓
        (Y ⊓ centralizer (X : Set G)), w ≠ (1 : G)
    rw [ha,hb']
    exact hpoint

end CFSG.Quasithin.Chapter12.Section02.RankOneModule

namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- Source 6.2.8 on the original layer. The reverse graph pair has a common
nonidentity point; natural point transitivity makes core containment force
normalization, contradicting that pair's actual index two. The only earlier
input retained is the escape of the marked involution centralizer. -/
theorem source_local_layer_not_le_point_core_of_escape
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hescape : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G)) :
    ¬ commutatorLayer T L ≤ (centralizer ({z} : Set G)).pCoreIn 2 := by
  intro hcore
  obtain ⟨H,hH,hHz,_⟩ := local_exists_hstar_in_centralizer h611 ho hT hescape
  have hVH : commutatorLayer T L ≤ H.pCoreIn 2 := hcore.trans
    (Chapter3.twoCore_le_of_sylow_le T hH.1.1.2 hHz)
  obtain ⟨d,hne,hseed,hodd,hb,e,α,β,hα,hβ,hi,hiβ,hr,hXcore,hn,hcomm,hcomm',hCa,hCb,
    a,b,ha,hb',hfa,hfb,w,hw,hw1⟩ :=
    source_local_graph_symmetric_pair D h h611 hnatural hz ho hH hHz hVH
  apply hn
  have hpoint : w ∈ (commutatorLayer T L).map (MulAut.conj a).toMonoidHom ⊓
      (commutatorLayer T L).map (MulAut.conj b).toMonoidHom := by
    rw [←ha,←hb']
    exact ⟨hw.1.1,hw.2.1⟩
  rw [ha,hb']
  exact local_intersecting_conjugates_normalize_of_point_core h611
    (hnatural.1 ▸ hnatural.2.1) hz (by intro he; simp [he] at ho) hcore a b hpoint hw1
end CFSG.Quasithin.Chapter12.Section02.RankOneModule
