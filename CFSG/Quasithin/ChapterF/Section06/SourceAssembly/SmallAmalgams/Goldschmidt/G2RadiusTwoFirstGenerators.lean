module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.G2RadiusTwoQuotient

/-!
# The three original arms at the first radius-two endpoint

The normal closure in the first endpoint equals the join of the three actual
neighboring point stabilizers. The six-label S₄ quotient makes the second
source group transitive on its distance-two sphere, so each arm exchanges
the other two neighbors. Each arm has order thirty-two and contains the
original order-sixteen distance-two label subgroup.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.9),
printed pp.400–401.
-/

@[expose] public section
open Subgroup SimpleGraph
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

theorem CanonicalLabelSetup.sphereLabelGroup_map_conj (c : CanonicalLabelSetup F s)
    (v : RankTwo.Vertex F) (n : ℕ) (g : G) :
    (c.sphereLabelGroup v n).map (MulAut.conj g).toMonoidHom =
      c.sphereLabelGroup (g • v) n := by
  rw [CanonicalLabelSetup.sphereLabelGroup, MonoidHom.map_closure,
    CanonicalLabelSetup.sphereLabelGroup]
  congr 1
  ext x
  constructor
  · rintro ⟨_,⟨w,⟨hw,ht⟩,rfl⟩,rfl⟩
    refine ⟨g • w,⟨?_,ht⟩,c.conjugate g w ht⟩
    rw [RankTwo.dist_smul, hw]
  · rintro ⟨w,⟨hw,ht⟩,rfl⟩
    refine ⟨c.label (g⁻¹ • w),⟨g⁻¹ • w,⟨?_,ht⟩,rfl⟩,?_⟩
    · have he := RankTwo.dist_smul F g⁻¹ (g • v) w
      rw [inv_smul_smul] at he
      exact he.trans hw
    · change g * c.label (g⁻¹ • w) * g⁻¹ = c.label w
      rw [← c.conjugate g (g⁻¹ • w) ht, smul_inv_smul]

namespace RadiusTwoFirstArms

def arm (c : CanonicalLabelSetup F s) (a β : RankTwo.Vertex F) : Subgroup G :=
  c.radiusTwoSecondGroup β ⊓ RankTwo.stabilizer F a

def group (c : CanonicalLabelSetup F s) (a : RankTwo.Vertex F) : Subgroup G :=
  ⨆ β : (RankTwo.graph F).neighborSet a, arm c a β.val

theorem arm_le (c : CanonicalLabelSetup F s) {a β : RankTwo.Vertex F}
    (hβ : (RankTwo.graph F).Adj a β) : arm c a β ≤ group c a :=
  le_iSup (fun β : (RankTwo.graph F).neighborSet a => arm c a β.val) ⟨β,hβ⟩

theorem group_le_stabilizer (c : CanonicalLabelSetup F s) (a : RankTwo.Vertex F) :
    group c a ≤ RankTwo.stabilizer F a := iSup_le fun _ => inf_le_right

theorem sphere_two_le_arm (c : CanonicalLabelSetup F s) (hr : c.radius = 2)
    (hs : 3 ≤ s) (h : CubicTreeAction F) {a β : RankTwo.Vertex F}
    (hβ : (RankTwo.graph F).Adj a β) : c.sphereLabelGroup a 2 ≤ arm c a β :=
  c.radiusTwo_sphere_two_le_pointStabilizer hr hs h hβ

theorem sphere_two_le_group (c : CanonicalLabelSetup F s) (hr : c.radius = 2)
    (hs : 3 ≤ s) (h : CubicTreeAction F) (a : RankTwo.Vertex F) :
    c.sphereLabelGroup a 2 ≤ group c a := by
  obtain ⟨f⟩ := h.exists_branchFrame a
  exact (sphere_two_le_arm c hr hs h (f.e 0).property).trans (arm_le c (f.e 0).property)

theorem arm_map_conj (c : CanonicalLabelSetup F s) (a β : RankTwo.Vertex F) (g : G) :
    (arm c a β).map (MulAut.conj g).toMonoidHom = arm c (g • a) (g • β) := by
  unfold arm CanonicalLabelSetup.radiusTwoSecondGroup
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, c.sphereLabelGroup_map_conj]
  change c.sphereLabelGroup (g • β) 3 ⊓
    (MulAction.stabilizer G a).map (MulAut.conj g).toMonoidHom = _
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]

theorem group_normalized (c : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    (a : RankTwo.Vertex F) : RankTwo.stabilizer F a ≤ normalizer (group c a : Set G) := by
  let : Finite (RankTwo.stabilizer F a) := h.finite_stabilizer a
  let : Finite (group c a) := Finite.of_injective
    (Subgroup.inclusion (group_le_stabilizer c a)) (Subgroup.inclusion_injective _)
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rw [group, Subgroup.map_iSup]
    apply iSup_le
    intro β
    change (arm c a β.val).map (MulAut.conj g).toMonoidHom ≤ group c a
    rw [arm_map_conj, show g • a = a from hg]
    apply arm_le
    have he := (translationGraphIso F g).toHom.map_adj β.property
    change (RankTwo.graph F).Adj (g • a) (g • β.val) at he
    simpa only [show g • a = a from hg] using he
  · exact (card_map_of_injective (MulAut.conj g).injective).ge

theorem sphere_two_normal_group (c : CanonicalLabelSetup F s) (hr : c.radius = 2)
    (hs : 3 ≤ s) (h : CubicTreeAction F) (a : RankTwo.Vertex F) :
    ((c.sphereLabelGroup a 2).subgroupOf (group c a)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (sphere_two_le_group c hr hs h a)).mpr
    ((group_le_stabilizer c a).trans (c.stabilizer_le_normalizer_sphereLabelGroup a 2))

/-- The three literal arms equal the source's normal closure of any one arm. -/
theorem group_eq_first (c : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    {a β : RankTwo.Vertex F} (hβ : (RankTwo.graph F).Adj a β) :
    group c a = c.radiusTwoFirstGroup a β := by
  apply le_antisymm
  · apply iSup_le
    intro γ
    obtain ⟨g,hga,hgβ⟩ := RankTwo.locally_transitive F hβ γ.property
    have he : arm c a γ.val = (arm c a β).map (MulAut.conj g).toMonoidHom := by
      rw [arm_map_conj, hga, hgβ]
    rw [he]
    rintro _ ⟨x,hx,rfl⟩
    exact subset_closure ⟨g,hga,x,hx,rfl⟩
  · exact conjugateSpanBy_le (arm_le c hβ) (group_normalized c h a)

end RadiusTwoFirstArms
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt

open Subgroup SimpleGraph
open Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoSixLabels.Frame
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}
variable {β : RankTwo.Vertex F} {f : BranchFrame F β} (r : RadiusTwoSixLabels.Frame f)
variable (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
variable (h : CubicTreeAction F) (hβ : β.type ≠ c.side)
include r c hr hs h hβ

/-- The marked pair product fixes the opposite original neighbor. -/
theorem first_pair_product_fixes_third_neighbor :
    (c.label (r.u (0,0)) * c.label (r.u (0,1))) • (f.e 2).val = (f.e 2).val := by
  let a : c.radiusTwoSecondGroup β := ⟨_,r.mem_second c h hβ (0,0)⟩
  let b : c.radiusTwoSecondGroup β := ⟨_,r.mem_second c h hβ (0,1)⟩
  let g := Subgroup.inclusion (c.radiusTwo_second_le_stabilizer hr (by omega) β) (a*b)
  have he := f.branchAction_eval g 2
  have hq : f.branchAction g = 1 := by
    let q := c.radiusTwoSecondAction hr (by omega) f
    have ha : q a = Equiv.swap (1 : Fin 3) 2 := r.label_branch_action c hr hs h hβ (0,0)
    have hb : q b = Equiv.swap (1 : Fin 3) 2 := r.label_branch_action c hr hs h hβ (0,1)
    change q (a*b) = 1
    rw [map_mul,ha,hb,Equiv.swap_mul_self]
  rw [hq, Equiv.Perm.one_apply] at he
  exact he.symm

/-- The same source element exchanges the two forward neighbors there. -/
theorem first_pair_product_moves_third_point :
    (c.label (r.u (0,0)) * c.label (r.u (0,1))) • f.point (2,0) ≠ f.point (2,0) := by
  let : (four c hr hs h hβ (β := β)).Normal :=
    c.radiusTwo_neighborLabelGroup_normal hr (by omega) h hβ
  obtain ⟨e,he0,he2,he1⟩ := r.reflection_quotient_symmetric_four c hr hs h hβ
  let a : c.radiusTwoSecondGroup β := ⟨_,r.mem_second c h hβ (0,0)⟩
  let b : c.radiusTwoSecondGroup β := ⟨_,r.mem_second c h hβ (0,1)⟩
  let g := a*b
  let g' := Subgroup.inclusion (c.radiusTwo_second_le_stabilizer hr (by omega) β) g
  intro hfix
  have hx : f.sphereAction h g' (2,0) = (2,0) := by
    apply f.point_injective h
    rw [f.sphereAction_eval]
    exact hfix
  have hconj := r.reflection_conjugate c hr hs h hβ g (2,0)
  rw [hx] at hconj
  have hg : QuotientGroup.mk' (four c hr hs h hβ (β := β)) g =
      r.reflection c hr hs h hβ (0,0) * r.reflection c hr hs h hβ (0,1) := by
    exact map_mul _ a b
  rw [hg] at hconj
  have hh := congrArg e hconj
  rw [map_mul,map_mul,map_inv,map_mul,he0,he1,he2] at hh
  exact (by decide : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) * Equiv.swap 1 2 *
    (Equiv.swap 0 1 * Equiv.swap 2 3)⁻¹ ≠ Equiv.swap 1 2) hh

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoSixLabels.Frame

namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoSixLabels.Frame
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}
variable {β : RankTwo.Vertex F} {f : BranchFrame F β} (r : RadiusTwoSixLabels.Frame f)
variable (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
variable (h : CubicTreeAction F) (hβ : β.type ≠ c.side)
include r c hr hs h hβ

/-- The original second source group acts transitively on all six distance-two vertices. -/
theorem second_sphere_transitive (x y : Fin 3 × ZMod 2) :
    ∃ g ∈ c.radiusTwoSecondGroup β, g • f.point x = f.point y := by
  let H := c.radiusTwoSecondGroup β
  let ι := Subgroup.inclusion (c.radiusTwo_second_le_stabilizer hr (by omega) β)
  let ρ := (f.sphereAction h).comp ι
  let a : H := ⟨_,r.mem_second c h hβ (0,0)⟩
  let b : H := ⟨_,r.mem_second c h hβ (0,1)⟩
  let p := a*b
  have hp : ρ p (2,0) = (2,1) := by
    have hfst : (ρ p (2,0)).1 = 2 := by
      change (f.sphereAction h (ι p) (2,0)).1 = 2
      rw [f.sphereAction_block]
      have he : f.branchAction (ι p) = 1 := by
        let q := c.radiusTwoSecondAction hr (by omega) f
        have ha : q a = Equiv.swap (1 : Fin 3) 2 := r.label_branch_action c hr hs h hβ (0,0)
        have hb : q b = Equiv.swap (1 : Fin 3) 2 := r.label_branch_action c hr hs h hβ (0,1)
        change q (a*b) = 1
        rw [map_mul,ha,hb,Equiv.swap_mul_self]
      rw [he, Equiv.Perm.one_apply]
    have hne : (ρ p (2,0)).2 ≠ 0 := by
      intro he
      have hz : ρ p (2,0) = (2,0) := Prod.ext hfst he
      apply r.first_pair_product_moves_third_point c hr hs h hβ
      have hh := f.sphereAction_eval h (ι p) (2,0)
      change f.point (ρ p (2,0)) = p.val • f.point (2,0) at hh
      rw [hz] at hh
      exact hh.symm
    exact Prod.ext hfst ((by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) _ hne)
  have reach (y : Fin 3 × ZMod 2) : ∃ g : H, ρ g (2,0) = y := by
    obtain ⟨g,hg⟩ := c.radiusTwoSecondAction_surjective hr hs h hβ f (Equiv.swap 2 y.1)
    let u := ρ g (2,0)
    let v := ρ g (2,1)
    have hu : u.1 = y.1 := by
      change (f.sphereAction h (ι g) (2,0)).1 = y.1
      rw [f.sphereAction_block]
      change c.radiusTwoSecondAction hr (by omega) f g 2 = y.1
      rw [hg,Equiv.swap_apply_left]
    have hv : v.1 = y.1 := by
      change (f.sphereAction h (ι g) (2,1)).1 = y.1
      rw [f.sphereAction_block]
      change c.radiusTwoSecondAction hr (by omega) f g 2 = y.1
      rw [hg,Equiv.swap_apply_left]
    have hne : u.2 ≠ v.2 := by
      intro he
      have hz : u = v := Prod.ext (hu.trans hv.symm) he
      have hi := (ρ g).injective hz
      exact (by decide : (0 : ZMod 2) ≠ 1) (congrArg Prod.snd hi)
    have he : y.2 = u.2 ∨ y.2 = v.2 :=
      (by decide : ∀ a b z : ZMod 2, a ≠ b → z=a ∨ z=b) _ _ _ hne
    rcases he with he | he
    · exact ⟨g, Prod.ext hu he.symm⟩
    · refine ⟨g*p, ?_⟩
      rw [map_mul,Equiv.Perm.mul_apply,hp]
      exact Prod.ext hv he.symm
  obtain ⟨gx,hgx⟩ := reach x
  obtain ⟨gy,hgy⟩ := reach y
  refine ⟨(gy*gx⁻¹).val,(gy*gx⁻¹).property,?_⟩
  have he : ρ (gy*gx⁻¹) x = y := by
    rw [map_mul,map_inv,Equiv.Perm.mul_apply,←hgx,Equiv.Perm.inv_def,Equiv.symm_apply_apply,hgy]
  have hh := f.sphereAction_eval h (ι (gy*gx⁻¹)) x
  change f.point (ρ (gy*gx⁻¹) x) = (gy*gx⁻¹).val • f.point x at hh
  rw [he] at hh
  exact hh.symm
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoSixLabels.Frame

open Subgroup SimpleGraph Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoFirstArms
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

theorem arm_card (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
    (h : CubicTreeAction F) {a β : RankTwo.Vertex F} (hβ : β.type ≠ c.side)
    (hadj : (RankTwo.graph F).Adj a β) : Nat.card (arm c a β) = 32 := by
  have hc := ((arm c a β).subgroupOf (c.radiusTwoSecondGroup β)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show arm c a β ≤ c.radiusTwoSecondGroup β from inf_le_left)).toEquiv,
    c.radiusTwo_second_card hr hs h hβ] at hc
  change Nat.card (arm c a β) * (arm c a β).relIndex (c.radiusTwoSecondGroup β) = 96 at hc
  have hi : (arm c a β).relIndex (c.radiusTwoSecondGroup β) = 3 :=
    c.radiusTwo_second_pointStabilizer_index hr hs h hβ hadj.symm
  rw [hi] at hc
  omega

/-- The arm from a neighbor exchanges the other two original neighbors. -/
theorem arm_neighbor_transitive (c : CanonicalLabelSetup F s) (hr : c.radius = 2)
    (hs : 4 ≤ s) (h : CubicTreeAction F) {a β b d : RankTwo.Vertex F}
    (hβ : β.type ≠ c.side) (haβ : (RankTwo.graph F).Adj a β)
    (hab : (RankTwo.graph F).Adj a b) (had : (RankTwo.graph F).Adj a d)
    (hβb : β ≠ b) (hβd : β ≠ d) :
    ∃ k ∈ arm c a β, k • b = d := by
  obtain ⟨f⟩ := h.exists_branchFrame β
  let r := RadiusTwoSixLabels.frame h f
  have hb : (RankTwo.graph F).dist β b = 2 :=
    (DistanceTwoGeometry.dist_eq_two_iff h.tree).mpr ⟨hβb,a,haβ.symm,hab⟩
  have hd : (RankTwo.graph F).dist β d = 2 :=
    (DistanceTwoGeometry.dist_eq_two_iff h.tree).mpr ⟨hβd,a,haβ.symm,had⟩
  obtain ⟨x,hx⟩ := (f.sphereEquiv h).surjective ⟨b,hb⟩
  obtain ⟨y,hy⟩ := (f.sphereEquiv h).surjective ⟨d,hd⟩
  have hx' : f.point x = b := congrArg Subtype.val hx
  have hy' : f.point y = d := congrArg Subtype.val hy
  obtain ⟨k,hk,hmove⟩ := r.second_sphere_transitive c hr hs h hβ x y
  have hkβ : k • β = β := c.radiusTwo_second_le_stabilizer hr (by omega) β hk
  have hbd : k • b = d := by simpa only [hx',hy'] using hmove
  have hka : k • a = a := by
    apply DistanceTwoGeometry.midpoint_unique h.tree.isAcyclic hβd
    · have hh := (translationGraphIso F k).toHom.map_adj haβ.symm
      change (RankTwo.graph F).Adj (k • β) (k • a) at hh
      simpa only [hkβ] using hh
    · have hh := (translationGraphIso F k).toHom.map_adj hab
      change (RankTwo.graph F).Adj (k • a) (k • b) at hh
      simpa only [hbd] using hh
    · exact haβ.symm
    · exact had
  exact ⟨k,⟨hk,hka⟩,hbd⟩

theorem group_neighbor_transitive (c : CanonicalLabelSetup F s) (hr : c.radius = 2)
    (hs : 4 ≤ s) (h : CubicTreeAction F) {a b d : RankTwo.Vertex F}
    (ha : a.type = c.side) (hab : (RankTwo.graph F).Adj a b)
    (had : (RankTwo.graph F).Adj a d) : ∃ k ∈ group c a, k • b = d := by
  obtain ⟨f⟩ := h.exists_branchFrame a
  obtain ⟨i,hi⟩ := f.e.surjective ⟨b,hab⟩
  obtain ⟨j,hj⟩ := f.e.surjective ⟨d,had⟩
  obtain ⟨l,hli,hlj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide : 2 < 3)
  have hl : (f.e l).val.type ≠ c.side := by
    rw [← ha]
    exact (f.e l).property.1.symm
  have hlb : (f.e l).val ≠ b := by
    intro he
    exact hli (f.e.injective ((Subtype.ext he).trans hi.symm))
  have hld : (f.e l).val ≠ d := by
    intro he
    exact hlj (f.e.injective ((Subtype.ext he).trans hj.symm))
  obtain ⟨k,hk,he⟩ := arm_neighbor_transitive c hr hs h hl (f.e l).property hab had hlb hld
  exact ⟨k,arm_le c (f.e l).property hk,he⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoFirstArms
