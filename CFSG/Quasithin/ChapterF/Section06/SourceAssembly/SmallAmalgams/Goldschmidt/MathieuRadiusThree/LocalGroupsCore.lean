module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.Contracts
public import Theory.GroupTheory.ThreeInvolutionFourCommutators
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth

/-!
# The radius-three label core in the Mathieu branch

Three length-three arms at an unlabelled vertex supply involutions whose
pairwise commutators are the three neighboring labels. They generate the
actual radius-three label group, of order thirty-two. The radius-two
eight-groups give the upper bound and the six-arc relation gives the exact
nonabelian lower bound.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.12), the calculation of `⟨z^[3](β)⟩` on printed p.405.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry
open scoped commutatorElement
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem exists_forward (h : CubicTreeAction F) (v a : RankTwo.Vertex F) :
    ∃ u, (RankTwo.graph F).Adj v u ∧ u ≠ a := by
  by_contra! hh
  have hi : Subsingleton ((RankTwo.graph F).neighborSet v) := ⟨fun x y =>
    Subtype.ext ((hh x x.property).trans (hh y y.property).symm)⟩
  have hc : Nat.card ((RankTwo.graph F).neighborSet v) ≤ 1 := by
    let f : (RankTwo.graph F).neighborSet v → Unit := fun _ => ()
    simpa using Nat.card_le_card_of_injective f (fun x y _ => Subsingleton.elim _ _)
  rw [h.card_neighbor v] at hc
  omega

private theorem neighbor_side (d : CanonicalLabelSetup F s)
    {v a : RankTwo.Vertex F} (hv : v.type ≠ d.side)
    (ha : (RankTwo.graph F).Adj v a) : a.type = d.side := by
  have hn := ha.1
  cases h0 : v.type <;> cases h1 : a.type <;> cases h2 : d.side <;> simp_all

private theorem frame_dist_three (h : CubicTreeAction F)
    {v : RankTwo.Vertex F} (f : BranchFrame F v)
    (w : Fin 3 → RankTwo.Vertex F)
    (hw : ∀ i, (RankTwo.graph F).Adj (f.c i) (w i))
    (hne : ∀ i, w i ≠ (f.e i).val) (i : Fin 3) :
    (RankTwo.graph F).dist v (w i) = 3 := by
  let p : BasedWalk (RankTwo.graph F) 3 v :=
    ⟨⟨(f.e i).val, (f.e i).property⟩,
      ⟨⟨f.c i, f.c_adj i⟩, ⟨⟨w i, hw i⟩, PUnit.unit⟩⟩⟩
  have hp : p.Nonbacktracking := ⟨f.c_ne_center i, hne i, trivial⟩
  exact geodesic_of_nonbacktracking_of_cycle_bound h.tree.connected
    (N := 6) (fun _ _ hc => (h.tree.isAcyclic _ hc).elim) p hp (by decide)

private theorem frame_six_commutator
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) {v : RankTwo.Vertex F} (hv : v.type ≠ d.side)
    (f : BranchFrame F v) (w : Fin 3 → RankTwo.Vertex F)
    (hw : ∀ i, (RankTwo.graph F).Adj (f.c i) (w i))
    (hne : ∀ i, w i ≠ (f.e i).val) {i j : Fin 3} (hij : i ≠ j) :
    ⁅d.label (w i), d.label (w j)⁆ = d.label (f.e i).val * d.label (f.e j).val := by
  let t := h.action.toCubicTreeAction
  have hadj (k : Fin 3) : (RankTwo.graph F).Adj v (f.e k).val := (f.e k).property
  have hmid : (f.e i).val ≠ (f.e j).val := fun he =>
    hij (f.e.injective (Subtype.ext he))
  let p : BasedWalk (RankTwo.graph F) 6 (w i) :=
    ⟨⟨f.c i, (hw i).symm⟩, ⟨⟨(f.e i).val, (f.c_adj i).symm⟩,
      ⟨⟨v, (hadj i).symm⟩, ⟨⟨(f.e j).val, hadj j⟩,
        ⟨⟨f.c j, f.c_adj j⟩, ⟨⟨w j, hw j⟩, PUnit.unit⟩⟩⟩⟩⟩⟩
  have hp : p.Nonbacktracking :=
    ⟨(hne i).symm, (f.c_ne_center i).symm, hmid.symm, f.c_ne_center j, hne j, trivial⟩
  have hpath : p.toWalk.IsPath := isPath_of_nonbacktracking_of_cycle_bound
    (N := 7) (fun _ _ hc => (t.tree.isAcyclic _ hc).elim) p hp (by decide)
  have hd : (RankTwo.graph F).dist (f.e i).val (w i) = 2 :=
    (DistanceTwoGeometry.dist_eq_two_iff t.tree).mpr
      ⟨(hne i).symm, f.c i, f.c_adj i, hw i⟩
  have htype : (w i).type = d.side :=
    ((RankTwo.even_dist_iff F t.generated _ _).mp (by rw [hd]; decide)).symm.trans
      (neighbor_side d hv (f.e i).property)
  exact r.six_arc (w i) (w j) p.toWalk htype hpath rfl

/-- The six-arc relation already constructs an actual order-thirty-two
subgroup of the opposite radius-three label group. -/
theorem LocalRelations.exists_radiusThree_nonabelian_subgroup
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side) :
    ∃ K : Subgroup G, K ≤ d.labelBall v 3 ∧ Nat.card K = 32 ∧ ¬ IsMulCommutative K := by
  let t := h.action.toCubicTreeAction
  obtain ⟨f⟩ := t.exists_branchFrame v
  have hadj (i : Fin 3) : (RankTwo.graph F).Adj v (f.e i).val := (f.e i).property
  choose w hw hne using fun i : Fin 3 => exists_forward t (f.c i) (f.e i).val
  let a : Fin 3 → G := fun i => d.label (f.e i).val
  let x : Fin 3 → G := fun i => d.label (w i)
  have hat (i : Fin 3) : (f.e i).val.type = d.side := neighbor_side d hv (f.e i).property
  have hxt (i : Fin 3) : (w i).type = d.side := by
    have hd : (RankTwo.graph F).dist (f.e i).val (w i) = 2 :=
      (DistanceTwoGeometry.dist_eq_two_iff t.tree).mpr
        ⟨(hne i).symm, f.c i, f.c_adj i, hw i⟩
    exact ((RankTwo.even_dist_iff F t.generated _ _).mp
      (by rw [hd]; decide)).symm.trans (hat i)
  have hao (i : Fin 3) : orderOf (a i) = 2 := d.order_two _ (hat i)
  have hxo (i : Fin 3) : x i ^ 2 = 1 := by
    simpa only [x, d.order_two _ (hxt i)] using pow_orderOf_eq_one (x i)
  have ha2 (i : Fin 3) : a i * a i = 1 := d.label_mul_self (hat i)
  have hani (i : Fin 3) : a i ≠ 1 := by
    intro he
    have hh := hao i
    rw [he, orderOf_one] at hh
    omega
  have hdistinct (i j : Fin 3) (hij : i ≠ j) : (f.e i).val ≠ (f.e j).val :=
    fun he => hij (f.e.injective (Subtype.ext he))
  have hp : a 0 * a 1 * a 2 = 1 := d.neighbor_product v _ _ _
    (f.e 0).property (f.e 1).property (f.e 2).property
    (hdistinct 0 1 (by decide)) (hdistinct 0 2 (by decide)) (hdistinct 1 2 (by decide))
    (hat 0)
  have h01 : a 0 * a 1 = a 2 := by
    simpa only [a, d.label_inv (hat 2)] using mul_eq_one_iff_eq_inv.mp hp
  have h02 : a 0 * a 2 = a 1 := by rw [← h01, ← mul_assoc, ha2, one_mul]
  have hac (i j : Fin 3) : Commute (a i) (a j) := by
    have hd : (RankTwo.graph F).dist (f.e i).val (f.e j).val ≤ 2 := by
      have hh := t.tree.connected.dist_triangle (u := (f.e i).val) (v := v)
        (w := (f.e j).val)
      simpa only [dist_eq_one_iff_adj.mpr (hadj i).symm,
        dist_eq_one_iff_adj.mpr (hadj j)] using hh
    exact d.labels_commute_of_dist_le (hat i) (hat j) (by omega) (by have := h.five_le; omega)
  have h12 : a 1 * a 2 = a 0 := by rw [← h01, ← mul_assoc, (hac 1 0).eq, mul_assoc, ha2, mul_one]
  have ha21 : a 2 ≠ a 1 := by
    intro he
    apply hani 0
    apply mul_right_cancel (b := a 1)
    simpa only [one_mul] using h01.trans he
  have hxcomm (i j : Fin 3) (hij : i ≠ j) : ⁅x i,x j⁆ = a i * a j :=
    frame_six_commutator r hv f w hw hne hij
  have hax (i j : Fin 3) : Commute (a i) (x j) := by
    have hd : (RankTwo.graph F).dist (f.e i).val (w j) ≤ 4 := by
      have hh := t.tree.connected.dist_triangle (u := (f.e i).val) (v := v) (w := w j)
      simpa only [dist_eq_one_iff_adj.mpr (hadj i).symm,
        frame_dist_three t f w hw hne j] using hh
    exact d.labels_commute_of_dist_le (hat i) (hxt j) (by omega) (by have := h.five_le; omega)
  refine ⟨closure ({x 0,x 1,x 2} : Set G), ?_, ?_, ?_⟩
  · apply (closure_le _).mpr
    rintro y (rfl | rfl | rfl)
    · exact d.label_mem_labelBall (hxt 0) (le_of_eq (frame_dist_three t f w hw hne 0))
    · exact d.label_mem_labelBall (hxt 1) (le_of_eq (frame_dist_three t f w hw hne 1))
    · exact d.label_mem_labelBall (hxt 2) (le_of_eq (frame_dist_three t f w hw hne 2))
  · apply ThreeInvolutionFourCommutators.card_closure_eq_thirty_two
      (x 0) (x 1) (x 2) (a 2) (a 1) (hxo 0) (hxo 1) (hxo 2)
      (hao 2) (hao 1) ha21
    · exact (hxcomm 0 1 (by decide)).trans h01
    · exact (hxcomm 0 2 (by decide)).trans h02
    · rw [(hxcomm 1 2 (by decide)), h12, (hac 2 1).eq, h12]
    · exact hax 1 0
    · exact hax 1 1
    · exact hax 1 2
  · intro hcomm
    have hh := isMulCommutative_iff.mp hcomm
      (⟨x 0, subset_closure (by simp)⟩ : closure ({x 0,x 1,x 2} : Set G))
      (⟨x 1, subset_closure (by simp)⟩ : closure ({x 0,x 1,x 2} : Set G))
    have hc : Commute (x 0) (x 1) := congrArg Subtype.val hh
    exact hani 2 (h01.symm.trans ((hxcomm 0 1 (by decide)).symm.trans
      (commutatorElement_eq_one_iff_commute.mpr hc)))

theorem LocalRelations.exists_radiusThree_subgroup
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side) :
    ∃ K : Subgroup G, K ≤ d.labelBall v 3 ∧ Nat.card K = 32 := by
  obtain ⟨K, hK, hcard, _⟩ := r.exists_radiusThree_nonabelian_subgroup hr v hv
  exact ⟨K, hK, hcard⟩

/-- The lower bound is on the literal label group inside the original
vertex stabilizer, so it can be combined with its local upper bound. -/
theorem LocalRelations.radiusThree_card_ge
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side) :
    32 ≤ Nat.card (d.labelBall v 3) := by
  obtain ⟨K, hK, hcard⟩ := r.exists_radiusThree_subgroup hr v hv
  let : Finite (RankTwo.stabilizer F v) := h.action.finite_stabilizer v
  let : Finite (d.labelBall v 3) := Finite.of_injective
    (Subgroup.inclusion (d.labelBall_le_stabilizer v 3 (by omega) (by have := h.five_le; omega)))
    (Subgroup.inclusion_injective _)
  rw [← hcard]
  exact Nat.card_le_card_of_injective (Subgroup.inclusion hK) (Subgroup.inclusion_injective hK)

/-- The three normal eight-groups have a common four-group, so their
product has order at most thirty-two. All groups are the literal source
label groups. -/
theorem LocalRelations.radiusThree_card_le
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side) :
    Nat.card (d.labelBall v 3) ≤ 32 := by
  let t := h.action.toCubicTreeAction
  obtain ⟨f⟩ := t.exists_branchFrame v
  have hadj (i : Fin 3) : (RankTwo.graph F).Adj v (f.e i).val := (f.e i).property
  let H : Fin 3 → Subgroup G := fun i => d.labelBall (f.e i).val 2
  let Q := d.labelBall v 3
  have hat (i : Fin 3) : (f.e i).val.type = d.side := neighbor_side d hv (f.e i).property
  have hdist (i j : Fin 3) : (RankTwo.graph F).dist (f.e i).val (f.e j).val ≤ 2 := by
    have hh := t.tree.connected.dist_triangle (u := (f.e i).val) (v := v) (w := (f.e j).val)
    simpa only [dist_eq_one_iff_adj.mpr (hadj i).symm,
      dist_eq_one_iff_adj.mpr (hadj j)] using hh
  have hHQ (i : Fin 3) : H i ≤ Q := by
    apply (closure_le _).mpr
    rintro _ ⟨w, ⟨hw, hd⟩, rfl⟩
    apply d.label_mem_labelBall hw
    have hh := t.tree.connected.dist_triangle (u := v) (v := (f.e i).val) (w := w)
    rw [dist_eq_one_iff_adj.mpr (hadj i)] at hh
    omega
  have hQ : Q = H 0 ⊔ H 1 ⊔ H 2 := by
    apply le_antisymm
    · apply (closure_le _).mpr
      rintro _ ⟨w, ⟨hw, hd⟩, rfl⟩
      obtain ⟨p, hp⟩ := t.tree.connected.exists_walk_length_eq_dist v w
      have hp0 : 0 < p.length := by
        by_contra! he
        have hd0 : (RankTwo.graph F).dist v w = 0 := by omega
        have hew := t.tree.connected.dist_eq_zero_iff.mp hd0
        exact hv (hew ▸ hw)
      have ha : (RankTwo.graph F).Adj v (p.getVert 1) := by
        simpa only [Walk.getVert_zero] using p.adj_getVert_succ hp0
      obtain ⟨i, hi⟩ := f.e.surjective ⟨p.getVert 1, ha⟩
      have hi' : (f.e i).val = p.getVert 1 := congrArg Subtype.val hi
      have hd' : (RankTwo.graph F).dist (f.e i).val w ≤ 2 := by
        rw [hi']
        have hh := dist_le (p.drop 1)
        rw [Walk.drop_length, hp] at hh
        omega
      have hm : d.label w ∈ H i := d.label_mem_labelBall hw hd'
      fin_cases i
      · exact mem_sup_left (mem_sup_left hm)
      · exact mem_sup_left (mem_sup_right hm)
      · exact mem_sup_right hm
    · exact sup_le (sup_le (hHQ 0) (hHQ 1)) (hHQ 2)
  have hnorm (i j : Fin 3) : H i ≤ normalizer (H j : Set G) :=
    d.nearby_labelBall_normalizes t hr (by have := h.five_le; omega) (hdist i j)
  have hnormal (i : Fin 3) : ((H i).subgroupOf Q).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer (hHQ i)).mpr
    rw [hQ]
    exact sup_le (sup_le (hnorm 0 i) (hnorm 1 i)) (hnorm 2 i)
  let : Finite (RankTwo.stabilizer F v) := t.finite_stabilizer v
  let : Finite Q := Finite.of_injective
    (Subgroup.inclusion (d.labelBall_le_stabilizer v 3 (by omega) (by have := h.five_le; omega)))
    (Subgroup.inclusion_injective _)
  let E : Fin 3 → Subgroup Q := fun i => (H i).subgroupOf Q
  have hE (i : Fin 3) : Nat.card (E i) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe (hHQ i)).toEquiv).trans (r.labelBall_card _ (hat i))
  let a : Fin 3 → G := fun i => d.label (f.e i).val
  have hao (i : Fin 3) : orderOf (a i) = 2 := d.order_two _ (hat i)
  have hdistinct (i j : Fin 3) (hij : i ≠ j) : (f.e i).val ≠ (f.e j).val :=
    fun he => hij (f.e.injective (Subtype.ext he))
  have hp : a 0 * a 1 * a 2 = 1 := d.neighbor_product v _ _ _
    (f.e 0).property (f.e 1).property (f.e 2).property
    (hdistinct 0 1 (by decide)) (hdistinct 0 2 (by decide)) (hdistinct 1 2 (by decide))
    (hat 0)
  have h01 : a 0 ≠ a 1 := by
    intro he
    rw [he, d.label_mul_self (hat 1), one_mul] at hp
    have ho := hao 2
    rw [hp, orderOf_one] at ho
    omega
  have hc : Commute (a 0) (a 1) := d.labels_commute_of_dist_le (hat 0) (hat 1)
    ((hdist 0 1).trans (by omega)) ((hdist 0 1).trans (by have := h.five_le; omega))
  let V := closure ({a 0,a 1} : Set G)
  let : IsKleinFour V := isKleinFour_closure_pair_of_orderOf (a 0) (a 1) (hao 0) (hao 1) h01 hc
  have hVH (i : Fin 3) : V ≤ H i := by
    apply (closure_le _).mpr
    rintro x (hx | hx)
    · exact hx ▸ d.label_mem_labelBall (hat 0) (hdist i 0)
    · exact (Set.mem_singleton_iff.mp hx) ▸ d.label_mem_labelBall (hat 1) (hdist i 1)
  let W : Subgroup Q := V.subgroupOf Q
  have hW : Nat.card W = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe ((hVH 0).trans (hHQ 0))).toEquiv).trans
      IsKleinFour.card_four
  have hWE (i : Fin 3) : W ≤ E i := fun _ hx => hVH i hx
  let : (E 0).Normal := hnormal 0
  let : (E 1).Normal := hnormal 1
  let : (E 2).Normal := hnormal 2
  have hI : 4 ≤ Nat.card (E 0 ⊓ E 1 : Subgroup Q) := by
    rw [← hW]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion (le_inf (hWE 0) (hWE 1)))
      (Subgroup.inclusion_injective _)
  have hp01 := card_mul_eq_card_inf_mul_card_sup_of_normalizes (E 0) (E 1)
    (by rw [(E 0).normalizer_eq_top]; exact le_top)
  rw [hE, hE] at hp01
  have hE01 : Nat.card (E 0 ⊔ E 1 : Subgroup Q) ≤ 16 := by nlinarith
  have hI2 : 4 ≤ Nat.card ((E 0 ⊔ E 1) ⊓ E 2 : Subgroup Q) := by
    rw [← hW]
    exact Nat.card_le_card_of_injective
      (Subgroup.inclusion (le_inf ((hWE 0).trans le_sup_left) (hWE 2)))
      (Subgroup.inclusion_injective _)
  have hp012 := card_mul_eq_card_inf_mul_card_sup_of_normalizes (E 0 ⊔ E 1) (E 2)
    (by rw [(E 0 ⊔ E 1).normalizer_eq_top]; exact le_top)
  rw [hE] at hp012
  have hall : E 0 ⊔ E 1 ⊔ E 2 = ⊤ := by
    change (H 0).subgroupOf Q ⊔ (H 1).subgroupOf Q ⊔ (H 2).subgroupOf Q = ⊤
    apply map_injective Q.subtype_injective
    simp only [Subgroup.map_sup, map_subgroupOf_eq_of_le (hHQ 0),
      map_subgroupOf_eq_of_le (hHQ 1), map_subgroupOf_eq_of_le (hHQ 2),
      ← MonoidHom.range_eq_map, range_subtype]
    exact hQ.symm
  rw [hall, Nat.card_congr (Subgroup.topEquiv (G := Q)).toEquiv] at hp012
  change Nat.card Q ≤ 32
  nlinarith

/-- The full opposite radius-three label core has its source order. -/
theorem LocalRelations.radiusThree_card
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side) :
    Nat.card (d.labelBall v 3) = 32 :=
  le_antisymm (r.radiusThree_card_le hr v hv) (r.radiusThree_card_ge hr v hv)

theorem LocalRelations.radiusThree_nonabelian
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side) :
    ¬ IsMulCommutative (d.labelBall v 3) := by
  obtain ⟨K, hK, _, hnc⟩ := r.exists_radiusThree_nonabelian_subgroup hr v hv
  intro hc
  apply hnc
  apply isMulCommutative_iff.mpr
  intro x y
  apply Subtype.ext
  change (x : G) * (y : G) = (y : G) * (x : G)
  exact congrArg Subtype.val (isMulCommutative_iff.mp hc
    (⟨x.val, hK x.property⟩ : d.labelBall v 3)
    (⟨y.val, hK y.property⟩ : d.labelBall v 3))

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
