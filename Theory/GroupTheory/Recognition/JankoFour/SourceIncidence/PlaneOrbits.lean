module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LineClosure
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneChart

public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.HexadOrbits
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.PairOrbits

/-!
# The actual rank-three plane action

Plane closure identifies ambient adjacency with two-point intersection of
native hexads. The chart and the original cubic projection transport the
native counts and stabilizer orbits to every ambient plane. This proves
six unchanged Input fields, including all three point–line orbit clauses,
without presupposing global plane uniqueness.
Source: Aschbacher–Segev (1991), (5.3)(1),(3), p.600.
-/
public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu
namespace LocalData
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

theorem plane_adj_iff (x y : {x : Point a.P //
    OnPlane a.P x (Cosets.vertex (centralizer z) 1)}) :
    Adj a.L x.val y.val ↔ x ≠ y ∧
      2 ≤ ((a.planePoints x).val ∩ (a.planePoints y).val).card := by
  classical
  constructor
  · rintro ⟨hne,l,hxl,hyl⟩
    have hl := a.plane_closed x.val y.val l _ hne hxl hyl x.property y.property
    let l' : {l : Line a.L // LineOnPlane a.L l (Cosets.vertex (centralizer z) 1)} := ⟨l,hl⟩
    have hc := Finset.card_le_card (Finset.subset_inter
      ((a.plane_incidence x l').mp hxl) ((a.plane_incidence y l').mp hyl))
    rw [(a.planeLines l').property] at hc
    exact ⟨fun he => hne (congrArg Subtype.val he),hc⟩
  · rintro ⟨hne,hc⟩
    obtain ⟨B,hB,hBc⟩ := Finset.exists_subset_card_eq hc
    let l := a.planeLines.symm ⟨B,hBc⟩
    have he : (a.planeLines l).val = B := congrArg Subtype.val (a.planeLines.apply_symm_apply _)
    refine ⟨fun he => hne (Subtype.ext he),l.val,?_,?_⟩
    · apply (a.plane_incidence x l).mpr
      rw [he]
      exact hB.trans Finset.inter_subset_left
    · apply (a.plane_incidence y l).mpr
      rw [he]
      exact hB.trans Finset.inter_subset_right

theorem plane_adj_two (x y : {x : Point a.P //
    OnPlane a.P x (Cosets.vertex (centralizer z) 1)}) :
    Adj a.L x.val y.val ↔ ((a.planePoints y).val ∩ (a.planePoints x).val).card = 2 := by
  rw [a.plane_adj_iff,Finset.inter_comm]
  constructor
  · rintro ⟨hne,hc⟩
    rcases NativeHexads.cases (a.planePoints x) (a.planePoints y) with h0 | h2 | he
    · omega
    · exact h2
    · exact (hne (a.planePoints.injective he.symm)).elim
  · intro hc
    refine ⟨?_,by omega⟩
    intro he
    rw [he,Finset.inter_self,m22Block_card _ (a.planePoints y).property] at hc
    omega

theorem plane_nonneighbor_iff (x y : {x : Point a.P //
    OnPlane a.P x (Cosets.vertex (centralizer z) 1)}) :
    (y.val ≠ x.val ∧ ¬ Adj a.L x.val y.val) ↔
      ((a.planePoints y).val ∩ (a.planePoints x).val).card = 0 := by
  rw [a.plane_adj_two]
  constructor
  · rintro ⟨hne,hn⟩
    rcases NativeHexads.cases (a.planePoints x) (a.planePoints y) with h0 | h2 | he
    · exact h0
    · exact (hn h2).elim
    · exact (hne (congrArg Subtype.val (a.planePoints.injective he))).elim
  · intro hc
    refine ⟨?_,by omega⟩
    intro he
    have he' : y = x := Subtype.ext he
    rw [he',Finset.inter_self,m22Block_card _ (a.planePoints x).property] at hc
    omega

private theorem adj_smul_iff (g : G) (x y : Point a.P) :
    Adj a.L (g • x) (g • y) ↔ Adj a.L x y := by
  constructor
  · intro hh
    simpa only [inv_smul_smul] using adj_smul g⁻¹ hh
  · exact adj_smul g

omit [Finite G] in
private theorem plane_base_smul (π : Plane z) :
    representative π • Cosets.vertex (centralizer z) 1 = π := by
  rw [Cosets.smul_vertex,mul_one,vertex_representative]

private noncomputable def planeTransport (π : Plane z) :
    {x : Point a.P // OnPlane a.P x π} ≃
      {x : Point a.P // OnPlane a.P x (Cosets.vertex (centralizer z) 1)} where
  toFun x := ⟨(representative π)⁻¹ • x.val,by
    have hh := incident_smul (representative π)⁻¹ x.property
    have he : (representative π)⁻¹ • π = Cosets.vertex (centralizer z) 1 :=
        inv_smul_eq_iff.mpr (plane_base_smul π).symm
    rw [he] at hh
    exact hh⟩
  invFun x := ⟨representative π • x.val,by
    have hh := incident_smul (representative π) x.property
    rw [plane_base_smul π] at hh
    exact hh⟩
  left_inv x := Subtype.ext (smul_inv_smul _ _)
  right_inv x := Subtype.ext (inv_smul_smul _ _)

noncomputable def planePointsAt (π : Plane z) :
    {x : Point a.P // OnPlane a.P x π} ≃ Hexad :=
  (a.planeTransport π).trans a.planePoints

theorem planePointsAt_adj (π : Plane z) (x y : {x : Point a.P // OnPlane a.P x π}) :
    Adj a.L x.val y.val ↔
      ((a.planePointsAt π y).val ∩ (a.planePointsAt π x).val).card = 2 := by
  rw [←a.adj_smul_iff (representative π)⁻¹]
  exact a.plane_adj_two (a.planeTransport π x) (a.planeTransport π y)

theorem planePointsAt_nonneighbor (π : Plane z) (x y : {x : Point a.P // OnPlane a.P x π}) :
    (y.val ≠ x.val ∧ ¬ Adj a.L x.val y.val) ↔
      ((a.planePointsAt π y).val ∩ (a.planePointsAt π x).val).card = 0 := by
  have he : (representative π)⁻¹ • y.val ≠ (representative π)⁻¹ • x.val ↔ y.val ≠ x.val :=
    (MulAction.injective (representative π)⁻¹).ne_iff
  rw [←he,←a.adj_smul_iff (representative π)⁻¹]
  exact a.plane_nonneighbor_iff (a.planeTransport π x) (a.planeTransport π y)

private def planeSubsetEquiv (π : Plane z) (p : Point a.P → Prop) :
    {y : Point a.P // OnPlane a.P y π ∧ p y} ≃
      {y : {y : Point a.P // OnPlane a.P y π} // p y.val} where
  toFun y := ⟨⟨y.val,y.property.1⟩,y.property.2⟩
  invFun y := ⟨y.val.val,y.val.property,y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem plane_neighbor_card (π : Plane z) (x : Point a.P) (hx : OnPlane a.P x π) :
    {y | OnPlane a.P y π ∧ Adj a.L x y}.ncard = 60 := by
  rw [←Nat.card_coe_set_eq]
  change Nat.card {y : Point a.P // OnPlane a.P y π ∧ Adj a.L x y} = 60
  rw [Nat.card_congr (a.planeSubsetEquiv π (Adj a.L x))]
  rw [Nat.card_congr ((a.planePointsAt π).subtypeEquiv (p := fun y => Adj a.L x y.val)
    (q := fun B => (B.val ∩ (a.planePointsAt π ⟨x,hx⟩).val).card = 2)
    (a.planePointsAt_adj π ⟨x,hx⟩))]
  exact NativeHexads.neighbor_card _

theorem plane_nonneighbor_card (π : Plane z) (x : Point a.P) (hx : OnPlane a.P x π) :
    {y | OnPlane a.P y π ∧ y ≠ x ∧ ¬ Adj a.L x y}.ncard = 16 := by
  rw [←Nat.card_coe_set_eq]
  change Nat.card {y : Point a.P // OnPlane a.P y π ∧ y ≠ x ∧ ¬ Adj a.L x y} = 16
  rw [Nat.card_congr (a.planeSubsetEquiv π (fun y => y ≠ x ∧ ¬ Adj a.L x y))]
  rw [Nat.card_congr ((a.planePointsAt π).subtypeEquiv (p := fun y => y.val ≠ x ∧ ¬ Adj a.L x y.val)
    (q := fun B => (B.val ∩ (a.planePointsAt π ⟨x,hx⟩).val).card = 0)
    (a.planePointsAt_nonneighbor π ⟨x,hx⟩))]
  exact NativeHexads.nonneighbor_card _

end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence

namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open Subgroup LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu
open scoped Pointwise
namespace LocalData
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

omit [Finite G] in
private theorem centralizer_fixes_plane (c : centralizer z) :
    (c : G) • Cosets.vertex (centralizer z) 1 = Cosets.vertex (centralizer z) 1 := by
  rw [Cosets.smul_vertex,mul_one]
  exact (Cosets.vertex_eq_base _ _).mpr c.property

private theorem plane_point_eq_of_image (c : centralizer z)
    (x y : {x : Point a.P // OnPlane a.P x (Cosets.vertex (centralizer z) 1)})
    (he : a.designProjection c • (a.planePoints x).val = (a.planePoints y).val) :
    (c : G) • x.val = y.val := by
  let x' : {x : Point a.P // OnPlane a.P x (Cosets.vertex (centralizer z) 1)} :=
    ⟨(c : G) • x.val,by
      have hh := incident_smul (c : G) x.property
      rw [centralizer_fixes_plane c] at hh
      exact hh⟩
  change x'.val = y.val
  apply congrArg Subtype.val (a.planePoints.injective (show a.planePoints x' = a.planePoints y from Subtype.ext ?_))
  rw [a.planePoints_equivariant c (a.designProjection c) (a.designProjection_marking c).symm x x' rfl]
  exact he

private theorem plane_rank_three_base
    (x u v : {x : Point a.P // OnPlane a.P x (Cosets.vertex (centralizer z) 1)})
    (he : (u = x ↔ v = x) ∧ (Adj a.L x.val u.val ↔ Adj a.L x.val v.val)) :
    ∃ c : centralizer z, (c : G) • x.val = x.val ∧ (c : G) • u.val = v.val := by
  have hc : ((a.planePoints u).val ∩ (a.planePoints x).val).card =
      ((a.planePoints v).val ∩ (a.planePoints x).val).card := by
    by_cases hu : u = x
    · rw [hu,he.1.mp hu]
    · have hv : v ≠ x := fun hh => hu (he.1.mpr hh)
      by_cases hxu : Adj a.L x.val u.val
      · rw [(a.plane_adj_two x u).mp hxu,(a.plane_adj_two x v).mp (he.2.mp hxu)]
      · have hxv : ¬ Adj a.L x.val v.val := fun hh => hxu (he.2.mpr hh)
        rw [(a.plane_nonneighbor_iff x u).mp ⟨fun hh => hu (Subtype.ext hh),hxu⟩,
          (a.plane_nonneighbor_iff x v).mp ⟨fun hh => hv (Subtype.ext hh),hxv⟩]
  obtain ⟨g,hgx,hgu⟩ := NativeHexads.transitive (a.planePoints x) (a.planePoints u) (a.planePoints v) hc
  obtain ⟨c,hc⟩ := a.designProjection_surjective (M22ValueBound.Concrete.inclusion g)
  refine ⟨c,a.plane_point_eq_of_image c x x ?_,a.plane_point_eq_of_image c u v ?_⟩
  · rw [hc]; exact hgx
  · rw [hc]; exact hgu

/-- The unchanged rank-three field on every ambient plane, through the original
cubic projection and literal left action. -/
theorem plane_rank_three (π : Plane z) (x u v : Point a.P)
    (hx : OnPlane a.P x π) (hu : OnPlane a.P u π) (hv : OnPlane a.P v π)
    (he : (u = x ↔ v = x) ∧ (Adj a.L x u ↔ Adj a.L x v)) :
    ∃ g : G, g • π = π ∧ g • x = x ∧ g • u = v := by
  let x' := a.planeTransport π ⟨x,hx⟩
  let u' := a.planeTransport π ⟨u,hu⟩
  let v' := a.planeTransport π ⟨v,hv⟩
  have he' : (u' = x' ↔ v' = x') ∧ (Adj a.L x'.val u'.val ↔ Adj a.L x'.val v'.val) := by
    constructor
    · have hu' : u' = x' ↔ u = x := by
        rw [(a.planeTransport π).injective.eq_iff,Subtype.ext_iff]
      have hv' : v' = x' ↔ v = x := by
        rw [(a.planeTransport π).injective.eq_iff,Subtype.ext_iff]
      rw [hu',hv']; exact he.1
    · change Adj a.L ((representative π)⁻¹ • x) ((representative π)⁻¹ • u) ↔
        Adj a.L ((representative π)⁻¹ • x) ((representative π)⁻¹ • v)
      rw [a.adj_smul_iff,a.adj_smul_iff]; exact he.2
  obtain ⟨c,hcx,hcu⟩ := a.plane_rank_three_base x' u' v' he'
  refine ⟨representative π * (c : G) * (representative π)⁻¹,?_,?_,?_⟩
  · have hπ : (representative π)⁻¹ • π = Cosets.vertex (centralizer z) 1 :=
      inv_smul_eq_iff.mpr (plane_base_smul π).symm
    rw [mul_smul,mul_smul,hπ,centralizer_fixes_plane c,plane_base_smul]
  · change (c : G) • ((representative π)⁻¹ • x) = (representative π)⁻¹ • x at hcx
    rw [mul_smul,mul_smul,hcx,smul_inv_smul]
  · change (c : G) • ((representative π)⁻¹ • u) = (representative π)⁻¹ • v at hcu
    rw [mul_smul,mul_smul,hcu,smul_inv_smul]
end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence

namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open Subgroup LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu
open scoped Pointwise
namespace LocalData
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

private theorem pairType_smul (g : G) (i : Fin 3) (x : Point a.P) (l : Line a.L) :
    PlanePairType a.L i (g • x) (g • l) ↔ PlanePairType a.L i x l := by
  have hi (y) : OnLine a.L (g • y) (g • l) ↔ OnLine a.L y l := incident_smul_iff _ _ g
  have ha (y) : Adj a.L (g • x) (g • y) ↔ Adj a.L x y := a.adj_smul_iff g x y
  fin_cases i
  · exact hi x
  · change (∀ y, OnLine a.L y (g • l) → Adj a.L (g • x) y) ↔
      (∀ y, OnLine a.L y l → Adj a.L x y)
    constructor
    · intro hh y hy
      exact (ha y).mp (hh (g • y) ((hi y).mpr hy))
    · intro hh y hy
      have hh' : OnLine a.L (g⁻¹ • y) l := by
        simpa only [OnLine,inv_smul_smul] using incident_smul g⁻¹ hy
      have h := adj_smul g (hh (g⁻¹ • y) hh')
      simpa only [smul_inv_smul] using h
  · change {y | OnLine a.L y (g • l) ∧ Adj a.L (g • x) y}.ncard = 3 ↔
      {y | OnLine a.L y l ∧ Adj a.L x y}.ncard = 3
    have he := (MulAction.toPerm g).subtypeEquiv
      (p := fun y => OnLine a.L y l ∧ Adj a.L x y)
      (q := fun y => OnLine a.L y (g • l) ∧ Adj a.L (g • x) y)
      (fun y => (and_congr (hi y) (ha y)).symm)
    have hc := Nat.card_congr he
    rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq]
    exact (congrArg (· = 3) hc.symm).to_iff

private theorem base_pair_count
    (x : {x : Point a.P // OnPlane a.P x (Cosets.vertex (centralizer z) 1)})
    (l : {l : Line a.L // LineOnPlane a.L l (Cosets.vertex (centralizer z) 1)}) :
    {y | OnLine a.L y l.val ∧ Adj a.L x.val y}.ncard =
      NativePairs.count (a.planePoints x).val (a.planeLines l).val := by
  let e : {y : Point a.P // OnLine a.L y l.val ∧ Adj a.L x.val y} ≃
      {y : {y : Point a.P // OnPlane a.P y (Cosets.vertex (centralizer z) 1)} //
        OnLine a.L y.val l.val ∧ Adj a.L x.val y.val} := {
    toFun y := ⟨⟨y.val,a.string y.val l.val _ y.property.1 l.property⟩,y.property⟩
    invFun y := ⟨y.val.val,y.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [←Nat.card_coe_set_eq]
  change Nat.card {y : Point a.P // OnLine a.L y l.val ∧ Adj a.L x.val y} = _
  rw [Nat.card_congr e]
  exact Nat.card_congr (a.planePoints.subtypeEquiv
    (p := fun y => OnLine a.L y.val l.val ∧ Adj a.L x.val y.val)
    (q := fun B => (a.planeLines l).val ⊆ B.val ∧ (B.val ∩ (a.planePoints x).val).card = 2)
    (fun y => and_congr (a.plane_incidence y l) (a.plane_adj_two x y)))

private theorem base_pair_pattern (i : Fin 3)
    (x : {x : Point a.P // OnPlane a.P x (Cosets.vertex (centralizer z) 1)})
    (l : {l : Line a.L // LineOnPlane a.L l (Cosets.vertex (centralizer z) 1)}) :
    PlanePairType a.L i x.val l.val ↔ NativePairs.Pattern i (a.planePoints x).val (a.planeLines l).val := by
  fin_cases i
  · exact a.plane_incidence x l
  · change (∀ y, OnLine a.L y l.val → Adj a.L x.val y) ↔
      (∀ B : Hexad, (a.planeLines l).val ⊆ B.val → (B.val ∩ (a.planePoints x).val).card = 2)
    constructor
    · intro hh B hB
      let y := a.planePoints.symm B
      have hy : (a.planePoints y) = B := a.planePoints.apply_symm_apply B
      rw [←hy] at hB ⊢
      exact (a.plane_adj_two x y).mp (hh y.val ((a.plane_incidence y l).mpr hB))
    · intro hh y hy
      let y' : {y : Point a.P // OnPlane a.P y (Cosets.vertex (centralizer z) 1)} :=
        ⟨y,a.string y l.val _ hy l.property⟩
      exact (a.plane_adj_two x y').mpr (hh (a.planePoints y') ((a.plane_incidence y' l).mp hy))
  · exact congrArg (· = 3) (a.base_pair_count x l) |>.to_iff

private theorem plane_line_eq_of_image (c : centralizer z)
    (l m : {l : Line a.L // LineOnPlane a.L l (Cosets.vertex (centralizer z) 1)})
    (he : a.designProjection c • (a.planeLines l).val = (a.planeLines m).val) :
    (c : G) • l.val = m.val := by
  let l' : {l : Line a.L // LineOnPlane a.L l (Cosets.vertex (centralizer z) 1)} :=
    ⟨(c : G) • l.val,by
      have hh := incident_smul (c : G) l.property
      rw [centralizer_fixes_plane c] at hh
      exact hh⟩
  change l'.val = m.val
  apply congrArg Subtype.val (a.planeLines.injective (show a.planeLines l' = a.planeLines m from Subtype.ext ?_))
  rw [a.planeLines_equivariant c (a.designProjection c) (a.designProjection_marking c).symm l l' rfl]
  exact he

private noncomputable def planeLineTransport (π : Plane z) :
    {l : Line a.L // LineOnPlane a.L l π} ≃
      {l : Line a.L // LineOnPlane a.L l (Cosets.vertex (centralizer z) 1)} where
  toFun l := ⟨(representative π)⁻¹ • l.val,by
    have hh := incident_smul (representative π)⁻¹ l.property
    have he : (representative π)⁻¹ • π = Cosets.vertex (centralizer z) 1 :=
      inv_smul_eq_iff.mpr (plane_base_smul π).symm
    rw [he] at hh
    exact hh⟩
  invFun l := ⟨representative π • l.val,by
    have hh := incident_smul (representative π) l.property
    rw [plane_base_smul π] at hh
    exact hh⟩
  left_inv l := Subtype.ext (smul_inv_smul _ _)
  right_inv l := Subtype.ext (inv_smul_smul _ _)

theorem plane_pair_types (π : Plane z) (x : Point a.P) (l : Line a.L)
    (hx : OnPlane a.P x π) (hl : LineOnPlane a.L l π) :
    ∃ i : Fin 3, PlanePairType a.L i x l := by
  let x' := a.planeTransport π ⟨x,hx⟩
  let l' := a.planeLineTransport π ⟨l,hl⟩
  obtain ⟨i,hi⟩ := NativePairs.pattern_exists (a.planePoints x') (a.planeLines l')
  exact ⟨i,(a.pairType_smul (representative π)⁻¹ i x l).mp ((a.base_pair_pattern i x' l').mpr hi)⟩

theorem plane_pair_types_realized (π : Plane z) (x : Point a.P)
    (hx : OnPlane a.P x π) (i : Fin 3) :
    ∃ l, LineOnPlane a.L l π ∧ PlanePairType a.L i x l := by
  let x' := a.planeTransport π ⟨x,hx⟩
  obtain ⟨L,hL⟩ := NativePairs.pattern_realized (a.planePoints x') i
  let l' := a.planeLines.symm L
  have hi : PlanePairType a.L i x'.val l'.val := (a.base_pair_pattern i x' l').mpr (by
    rw [a.planeLines.apply_symm_apply]; exact hL)
  let l := (a.planeLineTransport π).symm l'
  refine ⟨l.val,l.property,?_⟩
  have he := (a.pairType_smul (representative π) i x'.val l'.val).mpr hi
  change PlanePairType a.L i (representative π • ((representative π)⁻¹ • x)) l.val at he
  simpa only [smul_inv_smul] using he

theorem plane_pair_orbits (π : Plane z) (x y : Point a.P) (l m : Line a.L) (i : Fin 3)
    (hx : OnPlane a.P x π) (hy : OnPlane a.P y π)
    (hl : LineOnPlane a.L l π) (hm : LineOnPlane a.L m π)
    (hi : PlanePairType a.L i x l) (hj : PlanePairType a.L i y m) :
    ∃ g : G, g • π = π ∧ g • x = y ∧ g • l = m := by
  let x' := a.planeTransport π ⟨x,hx⟩
  let y' := a.planeTransport π ⟨y,hy⟩
  let l' := a.planeLineTransport π ⟨l,hl⟩
  let m' := a.planeLineTransport π ⟨m,hm⟩
  have hi' := (a.base_pair_pattern i x' l').mp ((a.pairType_smul (representative π)⁻¹ i x l).mpr hi)
  have hj' := (a.base_pair_pattern i y' m').mp ((a.pairType_smul (representative π)⁻¹ i y m).mpr hj)
  obtain ⟨g,hgx,hgl⟩ := NativePairs.pattern_orbit_general
    (a.planePoints x') (a.planePoints y') (a.planeLines l') (a.planeLines m') i hi' hj'
  obtain ⟨c,hc⟩ := a.designProjection_surjective (M22ValueBound.Concrete.inclusion g)
  have hcx := a.plane_point_eq_of_image c x' y' (by rw [hc]; exact hgx)
  have hcl := a.plane_line_eq_of_image c l' m' (by rw [hc]; exact hgl)
  refine ⟨representative π * (c : G) * (representative π)⁻¹,?_,?_,?_⟩
  · have hπ : (representative π)⁻¹ • π = Cosets.vertex (centralizer z) 1 :=
      inv_smul_eq_iff.mpr (plane_base_smul π).symm
    rw [mul_smul,mul_smul,hπ,centralizer_fixes_plane c,plane_base_smul]
  · change (c : G) • ((representative π)⁻¹ • x) = (representative π)⁻¹ • y at hcx
    rw [mul_smul,mul_smul,hcx,smul_inv_smul]
  · change (c : G) • ((representative π)⁻¹ • l) = (representative π)⁻¹ • m at hcl
    rw [mul_smul,mul_smul,hcl,smul_inv_smul]
end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
