module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerOrbit
public import Theory.GroupAction.CubicTree.DistanceTwoGeometry
public import Theory.GroupAction.CubicTree.ComponentAction
public import Theory.GroupAction.CubicTree.TrackTranslation

/-!
# The normalizer's distance-two component and its faithful quotient

The vertices are the actual normalizer orbit of the first base vertex; edges
mean distance two in the original tree. The candidate's paired-neighbor
property makes each connected component a cubic tree. The component stabilizer
acts transitively, with the same local stabilizer as the full normalizer.

Every even vertex of the selected track lies in the base component. Fixing
these vertices fixes the intervening odd vertices, so the full pointwise
fixer in the original group is exactly the track fixer. We descend the
component action through that literal subgroup and retain its finite local
groups, vertex transitivity and local transitivity. These are the hypotheses
used by the independent regularity-existence theorem.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.2),
printed p.394. The candidate itself is produced by (5.1).
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

noncomputable abbrev normalizerGraph (F : Bool → Subgroup G) (Q : Subgroup G) :
    SimpleGraph (normalizerOrbit F Q) :=
  DistanceTwoGeometry.graph (RankTwo.graph F) (normalizerOrbit F Q)

def normalizerBase (F : Bool → Subgroup G) (Q : Subgroup G) : normalizerOrbit F Q :=
  ⟨RankTwo.base F false,MulAction.mem_orbit_self _⟩

noncomputable def normalizerComponent (F : Bool → Subgroup G) (Q : Subgroup G) :
    (normalizerGraph F Q).ConnectedComponent :=
  (normalizerGraph F Q).connectedComponentMk (normalizerBase F Q)

noncomputable abbrev normalizerComponentGroup (F : Bool → Subgroup G) (Q : Subgroup G) :
    Subgroup (normalizer (Q:Set G)) :=
  ComponentAction.stabilizer (normalizer (Q:Set G)) (normalizerComponent F Q)

noncomputable abbrev normalizerComponentKernel (F : Bool → Subgroup G) (Q : Subgroup G) :
    Subgroup (normalizerComponentGroup F Q) :=
  (Q.subgroupOf (normalizer (Q:Set G))).subgroupOf (normalizerComponentGroup F Q)

noncomputable abbrev normalizerComponentQuotient (F : Bool → Subgroup G) (Q : Subgroup G) :=
  normalizerComponentGroup F Q ⧸ normalizerComponentKernel F Q

def normalizerComponentVertices (F : Bool → Subgroup G) (Q : Subgroup G) :
    Set (RankTwo.Vertex F) := Subtype.val '' (normalizerComponent F Q).supp

def normalizerComponentBase (F : Bool → Subgroup G) (Q : Subgroup G) :
    normalizerComponent F Q :=
  ⟨normalizerBase F Q,ConnectedComponent.connectedComponentMk_mem⟩

theorem normalizerGraphAction (F : Bool → Subgroup G) (Q : Subgroup G) :
    GraphAction (normalizerGraph F Q) (normalizer (Q:Set G)) := by
  constructor
  intro a x y hxy
  change (RankTwo.graph F).dist ((a:G) • x.val) ((a:G) • y.val) = 2
  rw [trackGraphAction.dist_smul]
  exact hxy

theorem NormalizerCandidate.component_isTree (h : CubicTreeAction F)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q) :
    (normalizerComponent F Q).toSimpleGraph.IsTree :=
  (DistanceTwoGeometry.isAcyclic h.tree (hQ.paired_neighbors h)).isTree_connectedComponent _

theorem NormalizerCandidate.component_card_neighbor (h : CubicTreeAction F)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q) (v : normalizerComponent F Q) :
    Nat.card ((normalizerComponent F Q).toSimpleGraph.neighborSet v) = 3 := by
  rw [DistanceTwoGeometry.card_component_neighborSet h.tree (hQ.paired_neighbors h)]
  exact h.card_neighbor _

theorem NormalizerCandidate.graph_locally_transitive (h : CubicTreeAction F)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q)
    (x y z : normalizerOrbit F Q)
    (hy : (normalizerGraph F Q).Adj x y) (hz : (normalizerGraph F Q).Adj x z) :
    ∃ g : normalizer (Q:Set G), g • x = x ∧ g • y = z := by
  obtain ⟨hxy,m,hxm,hmy⟩ := (DistanceTwoGeometry.dist_eq_two_iff h.tree).1 hy
  obtain ⟨hxz,n,hxn,hnz⟩ := (DistanceTwoGeometry.dist_eq_two_iff h.tree).1 hz
  obtain ⟨a,ha,hax,ham⟩ := hQ.orbit_locally_transitive h x hxm hxn
  let aL : normalizer (Q:Set G) := ⟨a,ha⟩
  have hu : (aL • y).val ≠ x.val ∧ (RankTwo.graph F).Adj n (aL • y).val := by
    constructor
    · change a • y.val ≠ x.val
      rw [←hax]
      exact fun he => hxy ((MulAction.toPerm a).injective he).symm
    · have he := trackGraphAction.map_adj a hmy
      rwa [ham] at he
  obtain ⟨w,hw,hwunique⟩ := hQ.paired_neighbors h x n hxn
  refine ⟨aL,Subtype.ext hax,?_⟩
  exact (hwunique _ hu).trans (hwunique _ ⟨hxz.symm,hnz⟩).symm

theorem normalizerGraph_transitive (F : Bool → Subgroup G) (Q : Subgroup G)
    (x y : normalizerOrbit F Q) : ∃ a : normalizer (Q:Set G), a • x = y :=
  MulAction.exists_smul_eq _ x y

theorem normalizerOrbit_stabilizer_map (F : Bool → Subgroup G) (Q : Subgroup G)
    (v : normalizerOrbit F Q) :
    (MulAction.stabilizer (normalizer (Q:Set G)) v).map (normalizer (Q:Set G)).subtype =
      normalizer (Q:Set G) ⊓ RankTwo.stabilizer F v.val := by
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨b.property,congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hb)⟩
  · intro ha
    exact ⟨⟨a,ha.1⟩,Subtype.ext ha.2,rfl⟩

theorem normalizerComponent_base_stabilizer_map (F : Bool → Subgroup G) (Q : Subgroup G) :
    (MulAction.stabilizer (normalizerComponentGroup F Q) (normalizerComponentBase F Q)).map
      ((normalizer (Q:Set G)).subtype.comp (normalizerComponentGroup F Q).subtype) =
      localNormalizer F Q false := by
  rw [←Subgroup.map_map,ComponentAction.map_stabilizer_eq _ (normalizerGraphAction F Q),
    normalizerOrbit_stabilizer_map]
  change normalizer (Q:Set G) ⊓ RankTwo.stabilizer F (RankTwo.base F false) = _
  rw [RankTwo.stabilizer,RankTwo.base,stabilizer_base]
  rfl

theorem CubicTreeAction.finite_normalizerOrbit_stabilizer (h : CubicTreeAction F)
    (Q : Subgroup G) (v : normalizerOrbit F Q) :
    Finite (MulAction.stabilizer (normalizer (Q:Set G)) v) := by
  let : ∀ i, Finite (F i) := h.finite
  let f : MulAction.stabilizer (normalizer (Q:Set G)) v → RankTwo.stabilizer F v.val :=
    fun a => ⟨a.val.val,congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp a.property)⟩
  apply Finite.of_injective f
  intro a b he
  have he' : a.val.val = b.val.val := congrArg (fun x : RankTwo.stabilizer F v.val => (x:G)) he
  exact Subtype.ext (Subtype.ext he')

noncomputable def trackEvenVertex (t : Track (RankTwo.graph F) G)
    (ht0 : t.vertex 0 = RankTwo.base F false) (i : ℤ) :
    normalizerOrbit F (trackFixer t) := by
  refine ⟨t.vertex (2*i),?_⟩
  refine ⟨⟨t.translation^i,zpow_mem (translation_mem_trackNormalizer t) i⟩,?_⟩
  change t.translation^i • RankTwo.base F false = t.vertex (2*i)
  rw [←ht0,t.zpow_translate,zero_add]

theorem trackEvenVertex_adj (h : CubicTreeAction F) (t : Track (RankTwo.graph F) G)
    (ht0 : t.vertex 0 = RankTwo.base F false) (i : ℤ) :
    (normalizerGraph F (trackFixer t)).Adj (trackEvenVertex t ht0 i)
      (trackEvenVertex t ht0 (i+1)) := by
  apply (DistanceTwoGeometry.dist_eq_two_iff h.tree).2
  refine ⟨fun he => ?_,t.vertex (2*i+1),t.adjacent (2*i),?_⟩
  · have he' := t.injective he
    omega
  · change (RankTwo.graph F).Adj (t.vertex (2*i+1)) (t.vertex (2*(i+1)))
    rw [show 2*(i+1) = 2*i+1+1 by omega]
    exact t.adjacent (2*i+1)

theorem trackEvenVertex_mem_component (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false) (i : ℤ) :
    trackEvenVertex t ht0 i ∈ (normalizerComponent F (trackFixer t)).supp := by
  induction i using Int.induction_on with
  | zero =>
    have he : trackEvenVertex t ht0 0 = normalizerBase F (trackFixer t) := by
      apply Subtype.ext
      change t.vertex (2*0) = RankTwo.base F false
      simpa only [mul_zero] using ht0
    rw [he]
    exact ConnectedComponent.connectedComponentMk_mem
  | succ i ih =>
    exact ((normalizerComponent F (trackFixer t)).mem_supp_congr_adj
      (trackEvenVertex_adj h t ht0 i)).mp ih
  | pred i ih =>
    have he := trackEvenVertex_adj h t ht0 (-(i:ℤ)-1)
    rw [sub_add_cancel] at he
    convert ((normalizerComponent F (trackFixer t)).mem_supp_congr_adj he).mpr ih using 1

/-- The original even track, now as vertices of the normalizer component. -/
noncomputable def trackEvenComponentVertex (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false) (i : ℤ) :
    normalizerComponent F (trackFixer t) :=
  ⟨trackEvenVertex t ht0 i,trackEvenVertex_mem_component h t ht0 i⟩

@[simp] theorem trackEvenComponentVertex_val (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false) (i : ℤ) :
    (trackEvenComponentVertex h t ht0 i).val.val = t.vertex (2*i) := rfl

theorem trackEvenComponentVertex_adj (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false) (i : ℤ) :
    (normalizerComponent F (trackFixer t)).toSimpleGraph.Adj
      (trackEvenComponentVertex h t ht0 i) (trackEvenComponentVertex h t ht0 (i+1)) :=
  trackEvenVertex_adj h t ht0 i

theorem componentFixer_eq_trackFixer (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false) :
    fixingSubgroup G (normalizerComponentVertices F (trackFixer t)) =
      trackFixer t := by
  ext a
  constructor
  · intro ha
    have heven : ∀ i : ℤ, a • t.vertex (2*i) = t.vertex (2*i) := by
      intro i
      exact (mem_fixingSubgroup_iff G).mp ha _
        ⟨trackEvenVertex t ht0 i,trackEvenVertex_mem_component h t ht0 i,rfl⟩
    apply t.mem_fixer.mpr
    intro i
    obtain ⟨k,hi|hi⟩ := even_or_odd_index i
    · rw [hi]
      exact heven k
    · rw [hi]
      exact t.toLine.fixed_between h.tree.isAcyclic trackGraphAction
        (heven k) (heven (k+1)) (by omega) (by omega)
  · intro ha
    apply (mem_fixingSubgroup_iff G).mpr
    rintro _ ⟨v,hv,rfl⟩
    have hle : trackFixer t ≤ F false := by
      have hh := trackFixer_le_stabilizer t 0
      rwa [ht0,RankTwo.stabilizer,RankTwo.base,stabilizer_base] at hh
    exact normalizerOrbit_fixed hle ha v

theorem normalizerComponent_kernel (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false) :
    (trackFixer t).subgroupOf (normalizer (trackFixer t : Set G)) =
      fixingSubgroup (normalizer (trackFixer t : Set G))
        (normalizerComponent F (trackFixer t)).supp := by
  ext a
  rw [Subgroup.mem_subgroupOf,mem_fixingSubgroup_iff]
  constructor
  · intro ha v hv
    have ha' : (a:G) ∈ fixingSubgroup G (normalizerComponentVertices F (trackFixer t)) := by
      rwa [componentFixer_eq_trackFixer h t ht0]
    exact Subtype.ext ((mem_fixingSubgroup_iff G).mp ha' _ ⟨v,hv,rfl⟩)
  · intro ha
    have ha' : (a:G) ∈ fixingSubgroup G (normalizerComponentVertices F (trackFixer t)) := by
      apply (mem_fixingSubgroup_iff G).mpr
      rintro _ ⟨w,hw,rfl⟩
      exact congrArg Subtype.val (ha w hw)
    rwa [componentFixer_eq_trackFixer h t ht0] at ha'

theorem normalizerComponent_kernel_le (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false) :
    (trackFixer t).subgroupOf (normalizer (trackFixer t : Set G)) ≤
      normalizerComponentGroup F (trackFixer t) := by
  intro a ha
  have hk := normalizerComponent_kernel h t ht0
  have ha' : a ∈ fixingSubgroup (normalizer (trackFixer t : Set G))
      (normalizerComponent F (trackFixer t)).supp := by
    rw [←hk]
    exact ha
  apply ComponentAction.stabilizer_le (normalizerComponent F (trackFixer t))
    (normalizerGraphAction F (trackFixer t)) (normalizerComponentBase F (trackFixer t))
  exact (mem_fixingSubgroup_iff _).mp ha' _ (normalizerComponentBase F (trackFixer t)).property

@[instance_reducible] noncomputable def normalizerQuotientAction (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false) :
    MulAction (normalizerComponentQuotient F (trackFixer t))
      (normalizerComponent F (trackFixer t)) :=
  ComponentAction.quotientAction (normalizerComponent F (trackFixer t))
    ((trackFixer t).subgroupOf (normalizer (trackFixer t : Set G))) (normalizerComponent_kernel h t ht0)

theorem normalizerQuotient_geometry (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false)
    (hQ : NormalizerCandidate F (trackFixer t)) :
    letI := normalizerQuotientAction h t ht0
    (normalizerComponent F (trackFixer t)).toSimpleGraph.IsTree ∧
    (∀ v : normalizerComponent F (trackFixer t),
      Nat.card ((normalizerComponent F (trackFixer t)).toSimpleGraph.neighborSet v) = 3) ∧
    FaithfulSMul (normalizerComponentQuotient F (trackFixer t))
      (normalizerComponent F (trackFixer t)) ∧
    GraphAction (normalizerComponent F (trackFixer t)).toSimpleGraph
      (normalizerComponentQuotient F (trackFixer t)) ∧
    (∀ x y : normalizerComponent F (trackFixer t),
      ∃ a : normalizerComponentQuotient F (trackFixer t), a • x = y) ∧
    (∀ x y z : normalizerComponent F (trackFixer t),
      (normalizerComponent F (trackFixer t)).toSimpleGraph.Adj x y →
      (normalizerComponent F (trackFixer t)).toSimpleGraph.Adj x z →
      ∃ a : normalizerComponentQuotient F (trackFixer t), a • x = x ∧ a • y = z) ∧
    (∀ x : normalizerComponent F (trackFixer t),
      Finite (MulAction.stabilizer (normalizerComponentQuotient F (trackFixer t)) x)) := by
  let C := normalizerComponent F (trackFixer t)
  let Q := (trackFixer t).subgroupOf (normalizer (trackFixer t : Set G))
  have hk := normalizerComponent_kernel h t ht0
  have hact := normalizerGraphAction F (trackFixer t)
  refine ⟨hQ.component_isTree h,hQ.component_card_neighbor h,
    ComponentAction.quotient_faithful C Q hk,
    ComponentAction.quotient_graphAction C Q hk hact,
    ComponentAction.quotient_transitive C Q hk hact (normalizerGraph_transitive F (trackFixer t)),
    ComponentAction.quotient_locally_transitive C Q hk hact (hQ.graph_locally_transitive h),?_⟩
  intro x
  have := h.finite_normalizerOrbit_stabilizer (trackFixer t) x.val
  exact ComponentAction.quotient_finite_stabilizer C Q hk x

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
