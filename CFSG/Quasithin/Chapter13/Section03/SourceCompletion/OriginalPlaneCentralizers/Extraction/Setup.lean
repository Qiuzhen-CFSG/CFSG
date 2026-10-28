module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.LocalControl
public import Theory.GroupTheory.SymmetricThreeCubicCore
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original plane-centralizer pushing-up setup

Q = O₂(LT) is Sylow in C_G(V), hence in its normal closure in C_M(A).
The cubic in the actual pointwise-plane action kills the image of
O₂(N_H(Q)); Sylow maximality identifies this core with Q. Thus Q is
radical in H = C_G(A), and all clauses of Hypothesis C.2.3 follow from
the original context, without a radicality or Sylow callback.

Source: Aschbacher--Smith 13.3.12, printed p.889, and C.2.3.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

theorem Context.core_sylow_centralizer (s : Context T L V) :
    ∃ S : Sylow 2 (centralizer (V : Set G)),
      (S : Subgroup (centralizer (V : Set G))).map (centralizer (V : Set G)).subtype =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let N := normalizer (V : Set G)
  let C := centralizer (V : Set G)
  have hTN : (T : Subgroup G) ≤ N := s.earlier_geometry.1.sylow_le_normalizer
  let TN := T.subtype hTN
  let CN := C.subgroupOf N
  obtain ⟨S, hS⟩ := TN.exists_subgroupOf_eq_of_normal CN
  let e : CN ≃* C := subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer _)
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((S : Subgroup CN).map e.toMonoidHom).map C.subtype = _
  rw [hS, map_map]
  rw [← s.earlier_geometry.2.1]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩
  · rintro ⟨hxT, hxC⟩
    exact ⟨⟨⟨x, Subgroup.centralizer_le_normalizer _ hxC⟩, hxC⟩, hxT, rfl⟩

theorem Context.core_sylow_normalClosure (s : Context T L V) (d : MarkedPlane V) :
    Chapter1.IsSylowIn 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      ((normalClosure (↑(((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
        (centralizer (d.A : Set G) ⊓ normalizer (L : Set G))))).map
          (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)).subtype) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let M := centralizer (d.A : Set G) ⊓ normalizer (L : Set G)
  let C := centralizer (V : Set G)
  have hQM : Q ≤ M := le_inf (s.plane_local_control d).1
    ((pCoreIn_le 2 _).trans (sup_le L.le_normalizer s.chosen.sylow_normalizes_component))
  have hCM : C ≤ M := le_inf (Subgroup.centralizer_le d.le_module)
    s.earlier_geometry.1.centralizer_le
  let C0 := C.subgroupOf M
  have hCn : C0.Normal := by
    apply normal_subgroupOf_of_le_normalizer
    exact (s.plane_local_control d).2.2.2.trans (normalizer_le_normalizer_centralizer V)
  let := hCn
  have hclosure : normalClosure (Q.subgroupOf M : Set M) ≤ C0 :=
    normalClosure_le_normal (fun x hx => s.chosen.core_centralizes hx)
  have hQC : Q ≤ (normalClosure (Q.subgroupOf M : Set M)).map M.subtype := by
    intro q hq
    exact ⟨⟨q,hQM hq⟩,subset_normalClosure hq,rfl⟩
  exact (show Chapter1.IsSylowIn 2 Q C from s.core_sylow_centralizer).restrict hQC (by
    rintro x ⟨m, hm, rfl⟩
    exact hclosure hm)

theorem Context.core_plane_radical (s : Context T L V) (d : MarkedPlane V) :
    IsPRadical 2 (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
      (centralizer (d.A : Set G))) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let H := centralizer (d.A : Set G)
  let M := H ⊓ normalizer (L : Set G)
  let N := H ⊓ normalizer (Q : Set G)
  have hQH : Q ≤ H := (s.plane_local_control d).1
  have hNM : N ≤ M := le_inf inf_le_left
    (inf_le_right.trans s.earlier_geometry.2.2)
  let f := (s.planeCentralizerAction d).comp (inclusion hNM)
  obtain ⟨e⟩ := pointwise_plane_equiv_s3
  let f3 := e.toMonoidHom.comp f
  obtain ⟨n, hn, hnH, hnL, _⟩ := s.marked_cubic d.chart d.coordinates
    d.equivariant d.A d.le_module d.plane_space
  have hnQ : n.val ∈ normalizer (Q : Set G) := by
    exact ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
        (show n.val ∈ L ⊔ (T : Subgroup G) from mem_sup_left hnL)
  let x : N := ⟨n.val, hnH, hnQ⟩
  have hx : orderOf (f3 x) = 3 := by
    rw [show f3 x = e (f x) from rfl, e.orderOf_eq]
    rw [← Subgroup.orderOf_coe (f x)]
    rw [show (f x).val = d.chart (V.normalizerMonoidHom.rangeRestrict n) from
      s.planeCentralizerAction_apply d (inclusion hNM x)]
    rw [hn, orderOf_cubic]
  have hpC : N.pCoreIn 2 ≤ centralizer (V : Set G) := by
    rintro y ⟨z, hz, rfl⟩
    have hz3 := twoCore_le_ker_of_permThree_cubic f3 x hx hz
    have hz1 : f z = 1 := e.injective (by exact hz3.trans (map_one e).symm)
    have hzker : inclusion hNM z ∈ (s.planeCentralizerAction d).ker := hz1
    rw [s.planeCentralizerAction_ker d] at hzker
    exact hzker
  have hQN : Q ≤ N := le_inf hQH Q.le_normalizer
  have hQP : Q ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) hQN inf_le_right
  have he : N.pCoreIn 2 = Q :=
    (Chapter1.isSylowIn_iff.mp (show Chapter1.IsSylowIn 2 Q
      (centralizer (V : Set G)) from s.core_sylow_centralizer)).2.2 _
        (isPGroup_pCoreIn 2 _) hQP hpC
  refine ⟨?_, ?_⟩
  · intro hb
    change Q.subgroupOf H = ⊥ at hb
    have hQb : Q = ⊥ := by
      simpa only [map_subgroupOf_eq_of_le hQH, Subgroup.map_bot] using
        congrArg (map H.subtype) hb
    exact s.chosen.ne_bot (le_bot_iff.mp (hQb ▸ s.chosen.le_core))
  · change (normalizer (Q.subgroupOf H : Set H)).pCoreIn 2 = Q.subgroupOf H
    rw [← subgroupOf_normalizer_eq hQH]
    have hn : (normalizer (Q : Set G)).subgroupOf H = N.subgroupOf H := by
      ext y
      exact ⟨fun hy => ⟨y.property,hy⟩, fun hy => hy.2⟩
    rw [hn, pCoreIn_subgroupOf 2 N H inf_le_left, he]

theorem Context.source_pushingUpSetup (s : Context T L V) (d : MarkedPlane V) :
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
      (centralizer (d.A : Set G)) ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)) :=
  s.pushingUpSetup d (s.core_plane_radical d) (s.core_sylow_normalClosure d)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
