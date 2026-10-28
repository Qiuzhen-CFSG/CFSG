module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.G2RadiusTwoFirstCore
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalBranchAction

/-!
# The literal local action of the radius-two source subgroup

The three-label relation puts every neighboring label in the distance-three
label subgroup. A label down each branch fixes that branch and interchanges
the other two, giving the full symmetric local action. The order-sixteen
first core lies in the actual point stabilizer of this subgroup.

Source: Goldschmidt (1980), (6.9), printed pp.400--401.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem three_edge_distance (h : CubicTreeAction F)
    {a b v u : RankTwo.Vertex F}
    (hab : (RankTwo.graph F).Adj a b) (hbv : (RankTwo.graph F).Adj b v)
    (hvu : (RankTwo.graph F).Adj v u) (hva : v ≠ a) (hub : u ≠ b) :
    (RankTwo.graph F).dist a u = 3 := by
  let p : BasedWalk (RankTwo.graph F) 3 a :=
    ⟨⟨b, hab⟩, ⟨⟨v, hbv⟩, ⟨⟨u, hvu⟩, PUnit.unit⟩⟩⟩
  have hp : p.Nonbacktracking := ⟨hva, hub, trivial⟩
  exact geodesic_of_nonbacktracking_of_cycle_bound h.tree.connected
    (N := 6) (fun _ _ hc => (h.tree.isAcyclic _ hc).elim) p hp (by decide)

private theorem exists_other_neighbor (h : CubicTreeAction F)
    (a b : RankTwo.Vertex F) : ∃ v, (RankTwo.graph F).Adj a v ∧ v ≠ b := by
  by_contra! hh
  have hi : Subsingleton ((RankTwo.graph F).neighborSet a) := ⟨fun x y =>
    Subtype.ext ((hh x x.property).trans (hh y y.property).symm)⟩
  have hc : Nat.card ((RankTwo.graph F).neighborSet a) ≤ 1 := by
    let f : (RankTwo.graph F).neighborSet a → Unit := fun _ => ()
    simpa using Nat.card_le_card_of_injective f (fun x y _ => Subsingleton.elim _ _)
  rw [h.card_neighbor a] at hc
  omega

/-- The lower labels in (6.9) are elements of the literal distance-three group,
by the three-label relation at a vertex two steps from the center. -/
theorem CanonicalLabelSetup.neighbor_label_mem_radiusTwoSecondGroup
    (c : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    {β a : RankTwo.Vertex F} (hβa : (RankTwo.graph F).Adj β a)
    (ha : a.type = c.side) : c.label a ∈ c.radiusTwoSecondGroup β := by
  obtain ⟨v, hav, hvβ⟩ := exists_other_neighbor h a β
  obtain ⟨f⟩ := h.exists_branchFrame a
  obtain ⟨i, hi⟩ := f.e.surjective ⟨v, hav⟩
  have hival : (f.e i).val = v := congrArg Subtype.val hi
  have hcu : (RankTwo.graph F).Adj v (f.c i) := hival ▸ f.c_adj i
  have hdu : (RankTwo.graph F).Adj v (f.d i) := hival ▸ f.d_adj i
  have hc3 := three_edge_distance h hβa hav hcu hvβ (f.c_ne_center i)
  have hd3 := three_edge_distance h hβa hav hdu hvβ (f.d_ne_center i)
  have hcside : (f.c i).type = c.side :=
    ((RankTwo.even_dist_iff F h.generated a (f.c i)).mp
      (by rw [f.c_dist h i]; decide)).symm.trans ha
  have hdside : (f.d i).type = c.side :=
    ((RankTwo.even_dist_iff F h.generated a (f.d i)).mp
      (by rw [f.d_dist h i]; decide)).symm.trans ha
  have hc : c.label (f.c i) ∈ c.radiusTwoSecondGroup β :=
    subset_closure ⟨f.c i, ⟨hc3, hcside⟩, rfl⟩
  have hd : c.label (f.d i) ∈ c.radiusTwoSecondGroup β :=
    subset_closure ⟨f.d i, ⟨hd3, hdside⟩, rfl⟩
  have hp := c.neighbor_product v a (f.c i) (f.d i) hav.symm hcu hdu
    (f.c_ne_center i).symm (f.d_ne_center i).symm (f.c_ne_d i) ha
  rw [mul_assoc] at hp
  exact (mul_eq_one_iff_eq_inv.mp hp).symm ▸ inv_mem (mul_mem hc hd)

/-- The source normal four-group is inside the original distance-three group. -/
theorem CanonicalLabelSetup.radiusTwo_neighborLabelGroup_le_second
    (c : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    {β : RankTwo.Vertex F} (hβ : β.type ≠ c.side) :
    c.neighborLabelGroup β ≤ c.radiusTwoSecondGroup β := by
  apply (closure_le _).mpr
  rintro _ ⟨a, ha, rfl⟩
  have hside : a.type = c.side := by
    have hn := ha.1
    cases ht : β.type <;> cases ht' : a.type <;> cases hc : c.side <;> simp_all
  exact c.neighbor_label_mem_radiusTwoSecondGroup h ha hside

/-- Conjugation by the full original vertex stabilizer preserves its
neighboring label group. -/
theorem CanonicalLabelSetup.stabilizer_normalizes_neighborLabelGroup
    (c : CanonicalLabelSetup F s) {β : RankTwo.Vertex F} (hβ : β.type ≠ c.side) :
    RankTwo.stabilizer F β ≤ normalizer (c.neighborLabelGroup β : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro g hg _ ⟨a, ha, rfl⟩
  have hside : a.type = c.side := by
    have hn := ha.1
    cases ht : β.type <;> cases ht' : a.type <;> cases hc : c.side <;> simp_all
  have he := (translationGraphIso F g).toHom.map_adj ha
  change (RankTwo.graph F).Adj (g • β) (g • a) at he
  rw [show g • β = β from hg] at he
  exact subset_closure ⟨g • a, he, c.conjugate g a hside⟩

/-- The four-group used in the source quotient is normal in the literal
second source group. -/
theorem CanonicalLabelSetup.radiusTwo_neighborLabelGroup_normal
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 3 ≤ s)
    (h : CubicTreeAction F) {β : RankTwo.Vertex F} (hβ : β.type ≠ c.side) :
    ((c.neighborLabelGroup β).subgroupOf (c.radiusTwoSecondGroup β)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (c.radiusTwo_neighborLabelGroup_le_second h hβ)).mpr
    ((c.radiusTwo_second_le_stabilizer hr hs β).trans
      (c.stabilizer_normalizes_neighborLabelGroup hβ))

/-- The first order-sixteen core is contained in the second source group's
literal point stabilizer. This is the inclusion used on printed p.401. -/
theorem CanonicalLabelSetup.radiusTwo_sphere_two_le_pointStabilizer
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 3 ≤ s)
    (h : CubicTreeAction F) {a β : RankTwo.Vertex F}
    (haβ : (RankTwo.graph F).Adj a β) :
    c.sphereLabelGroup a 2 ≤ c.radiusTwoSecondGroup β ⊓ RankTwo.stabilizer F a := by
  apply le_inf _ (c.sphereLabelGroup_le_stabilizer a 2 (by omega) (by omega))
  apply (closure_le _).mpr
  rintro _ ⟨w, ⟨hd, hw⟩, rfl⟩
  have hdist : (RankTwo.graph F).dist β w ≤ 3 := by
    have ht := h.tree.connected.dist_triangle (u := β) (v := a) (w := w)
    rw [dist_eq_one_iff_adj.mpr haβ.symm, hd] at ht
    exact ht
  have heven := (RankTwo.even_dist_iff F h.generated a w).mp (by rw [hd]; decide)
  have hn : β.type ≠ w.type := fun he => haβ.1 (heven.trans he.symm)
  have hodd : ¬ Even ((RankTwo.graph F).dist β w) := fun he =>
    hn ((RankTwo.even_dist_iff F h.generated β w).mp he)
  have hcases : (RankTwo.graph F).dist β w = 1 ∨ (RankTwo.graph F).dist β w = 3 := by
    have := Nat.even_or_odd ((RankTwo.graph F).dist β w)
    rcases this with he | ⟨k, hk⟩
    · exact (hodd he).elim
    · omega
  rcases hcases with hd1 | hd3
  · exact c.neighbor_label_mem_radiusTwoSecondGroup h (dist_eq_one_iff_adj.mp hd1) hw
  · exact subset_closure ⟨w, ⟨hd3, hw⟩, rfl⟩

/-- The source first group contains the actual nonabelian order-sixteen core;
no abstract model subgroup is substituted for the label subgroup. -/
theorem CanonicalLabelSetup.radiusTwo_sphere_two_le_first
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 3 ≤ s)
    (h : CubicTreeAction F) {a β : RankTwo.Vertex F}
    (haβ : (RankTwo.graph F).Adj a β) :
    c.sphereLabelGroup a 2 ≤ c.radiusTwoFirstGroup a β :=
  (c.radiusTwo_sphere_two_le_pointStabilizer hr hs h haβ).trans
    (c.radiusTwo_second_inter_first_le_first a β)

/-- The actual homomorphism on the three branches, restricted to the
source distance-three subgroup. -/
noncomputable def CanonicalLabelSetup.radiusTwoSecondAction
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 3 ≤ s)
    {β : RankTwo.Vertex F} (f : BranchFrame F β) :
    c.radiusTwoSecondGroup β →* Equiv.Perm (Fin 3) :=
  f.branchAction.comp (Subgroup.inclusion (c.radiusTwo_second_le_stabilizer hr hs β))

private theorem permutation_three_fixed :
    ∀ (p : Equiv.Perm (Fin 3)) (i : Fin 3),
      (∀ j, p j = j ↔ j = i) → p = Equiv.swap (i + 1) (i + 2) := by decide

private theorem permutation_three_cases :
    ∀ p : Equiv.Perm (Fin 3), p = 1 ∨ p = Equiv.swap 0 1 ∨ p = Equiv.swap 0 2 ∨
      p = Equiv.swap 1 2 ∨ p = Equiv.swap 0 1 * Equiv.swap 1 2 ∨
      p = Equiv.swap 1 2 * Equiv.swap 0 1 := by decide

/-- Each branch has a distance-three label whose local action is the
transposition of the other two branches. -/
theorem CanonicalLabelSetup.radiusTwoSecondAction_transposition
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
    (h : CubicTreeAction F) {β : RankTwo.Vertex F}
    (hβ : β.type ≠ c.side) (f : BranchFrame F β) (i : Fin 3) :
    Equiv.swap (i + 1) (i + 2) ∈
      (c.radiusTwoSecondAction hr (by omega) f).range := by
  let a := (f.e i).val
  obtain ⟨v, hav, hvβ⟩ := exists_other_neighbor h a β
  obtain ⟨u, hvu, hua⟩ := exists_other_neighbor h v a
  have hβa : (RankTwo.graph F).Adj β a := (f.e i).property
  have hβu := three_edge_distance h hβa hav hvu hvβ hua
  have hau : (RankTwo.graph F).dist a u = 2 :=
    (Theory.GroupAction.CubicTree.DistanceTwoGeometry.dist_eq_two_iff h.tree).mpr
      ⟨hua.symm, v, hav, hvu⟩
  have ha : a.type = c.side := by
    have hn := hβa.1
    cases ht : β.type <;> cases ht' : a.type <;> cases hc : c.side <;> simp_all
  have hu : u.type = c.side :=
    ((RankTwo.even_dist_iff F h.generated a u).mp (by rw [hau]; decide)).symm.trans ha
  have huH : c.label u ∈ c.radiusTwoSecondGroup β :=
    subset_closure ⟨u, ⟨hβu, hu⟩, rfl⟩
  let g : c.radiusTwoSecondGroup β := ⟨c.label u, huH⟩
  refine ⟨g, permutation_three_fixed _ i ?_⟩
  intro j
  have he : (f.e (c.radiusTwoSecondAction hr (by omega) f g j)).val =
      c.label u • (f.e j).val := f.branchAction_eval _ j
  constructor
  · intro hj
    by_contra hji
    have hneq : (f.e j).val ≠ a := fun hh => hji (f.e.injective (Subtype.ext hh))
    let p : BasedWalk (RankTwo.graph F) 4 u :=
      ⟨⟨v, hvu.symm⟩, ⟨⟨a, hav.symm⟩,
        ⟨⟨β, hβa.symm⟩, ⟨⟨(f.e j).val, (f.e j).property⟩, PUnit.unit⟩⟩⟩⟩
    have hp : p.Nonbacktracking := ⟨hua.symm, hvβ.symm, hneq, trivial⟩
    have hd : (RankTwo.graph F).dist u (f.e j).val = 4 :=
      geodesic_of_nonbacktracking_of_cycle_bound h.tree.connected
        (N := 8) (fun _ _ hc => (h.tree.isAcyclic _ hc).elim) p hp (by decide)
    exact c.moves_sphere u hu (by omega) (f.e j).val (by omega) (by rw [hj] at he; exact he.symm)
  · rintro rfl
    apply f.e.injective
    apply Subtype.ext
    rw [he]
    exact c.fixes_ball u hu a (by rw [dist_comm, hau]; omega)
      (by rw [dist_comm, hau]; omega)

/-- The distance-three subgroup induces the full symmetric action on the
three neighbors; this is the original local action, with its given labels. -/
theorem CanonicalLabelSetup.radiusTwoSecondAction_surjective
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
    (h : CubicTreeAction F) {β : RankTwo.Vertex F}
    (hβ : β.type ≠ c.side) (f : BranchFrame F β) :
    Function.Surjective (c.radiusTwoSecondAction hr (by omega) f) := by
  let R := (c.radiusTwoSecondAction hr (by omega) f).range
  have h01 : Equiv.swap (0 : Fin 3) 1 ∈ R := by
    simpa only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
      using c.radiusTwoSecondAction_transposition hr hs h hβ f 2
  have h02 : Equiv.swap (0 : Fin 3) 2 ∈ R := by
    simpa only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
      Equiv.swap_comm] using c.radiusTwoSecondAction_transposition hr hs h hβ f 1
  have h12 : Equiv.swap (1 : Fin 3) 2 ∈ R := by
    simpa only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl]
      using c.radiusTwoSecondAction_transposition hr hs h hβ f 0
  intro p
  change p ∈ R
  rcases permutation_three_cases p with rfl | rfl | rfl | rfl | rfl | rfl
  · exact R.one_mem
  · exact h01
  · exact h02
  · exact h12
  · exact R.mul_mem h01 h12
  · exact R.mul_mem h12 h01

/-- The original neighbors lie in one orbit of the source subgroup. -/
theorem CanonicalLabelSetup.radiusTwo_second_neighbor_transitive
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
    (h : CubicTreeAction F) {β a b : RankTwo.Vertex F}
    (hβ : β.type ≠ c.side) (ha : (RankTwo.graph F).Adj β a)
    (hb : (RankTwo.graph F).Adj β b) :
    ∃ g ∈ c.radiusTwoSecondGroup β, g • a = b := by
  obtain ⟨f⟩ := h.exists_branchFrame β
  obtain ⟨i, hi⟩ := f.e.surjective ⟨a, ha⟩
  obtain ⟨j, hj⟩ := f.e.surjective ⟨b, hb⟩
  obtain ⟨g, hg⟩ := c.radiusTwoSecondAction_surjective hr hs h hβ f (Equiv.swap i j)
  refine ⟨g.val, g.property, ?_⟩
  have he := f.branchAction_eval
    (Subgroup.inclusion (c.radiusTwo_second_le_stabilizer hr (by omega) β) g) i
  change (f.e (c.radiusTwoSecondAction hr (by omega) f g i)).val = g.val • (f.e i).val at he
  rw [hg, Equiv.swap_apply_left, hi, hj] at he
  exact he.symm

/-- The literal point stabilizer has index three in the distance-three group. -/
theorem CanonicalLabelSetup.radiusTwo_second_pointStabilizer_index
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
    (h : CubicTreeAction F) {β a : RankTwo.Vertex F}
    (hβ : β.type ≠ c.side) (ha : (RankTwo.graph F).Adj β a) :
    (c.radiusTwoSecondGroup β ⊓ RankTwo.stabilizer F a).relIndex
      (c.radiusTwoSecondGroup β) = 3 := by
  let H := c.radiusTwoSecondGroup β
  have ho : MulAction.orbit H a = (RankTwo.graph F).neighborSet β := by
    ext b
    constructor
    · rintro ⟨g, rfl⟩
      have he := (translationGraphIso F g.val).toHom.map_adj ha
      change (RankTwo.graph F).Adj (g.val • β) (g.val • a) at he
      change (RankTwo.graph F).Adj β (g.val • a)
      simpa only [show g.val • β = β from
        c.radiusTwo_second_le_stabilizer hr (by omega) β g.property] using he
    · intro hb
      obtain ⟨g, hg, he⟩ := c.radiusTwo_second_neighbor_transitive hr hs h hβ ha hb
      exact ⟨⟨g, hg⟩, he⟩
  have he : (H ⊓ RankTwo.stabilizer F a).subgroupOf H = MulAction.stabilizer H a := by
    ext g
    exact ⟨fun hg => hg.2, fun hg => ⟨g.property, hg⟩⟩
  change (H ⊓ RankTwo.stabilizer F a).relIndex H = 3
  rw [Subgroup.relIndex, he, MulAction.index_stabilizer, ho, ← Nat.card_coe_set_eq]
  exact h.card_neighbor β

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
