module

public import CFSG.Quasithin.ChapterI.Section04To05.A3SourceGeometry.Kernels
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PointConnectivity
public import Mathlib.Data.Fintype.Sigma

/-!
# The fifteen original A₃ points and their lines

The Fano residue at a point puts any two incident lines in a common plane.
The Fano residue at that plane makes collinearity transitive. Connectivity
therefore makes every pair of points collinear. Unique lines identify the
other points with seven choices of a line and two choices of a point on it,
giving fifteen points. The same local argument covers every line by a plane
through any specified point.

Source: Aschbacher–Smith I.5.9(1–2) and the covering used in I.5.10,
printed pp.421–422. All counts concern the literal D-system cosets.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .A3 G)

/-- Two actual lines through a point lie in an actual common plane. -/
theorem a3_coplanar_incident_lines {x : S.Point} {l m : S.Line}
    (hxl : S.Inc x l) (hxm : S.Inc x m) :
    ∃ π : S.Plane, S.Inc x π ∧ S.Inc l π ∧ S.Inc m π := by
  by_cases hlm : l = m
  · subst m
    have hn : Nonempty {π : S.Plane // S.Inc l π} :=
      (Nat.card_pos_iff.mp (by rw [S.line_planes_card l]; decide)).1
    obtain ⟨π⟩ := hn
    exact ⟨π.val, S.point_line_plane hxl π.property, π.property, π.property⟩
  obtain ⟨f⟩ := S.exists_a3_pointResidue x
  let a := f.lines.symm ⟨l, hxl⟩
  let b := f.lines.symm ⟨m, hxm⟩
  have hab : a ≠ b := by
    intro h
    apply hlm
    have hh := congrArg (fun p => (f.lines p).val) h
    simpa only [a, b, Equiv.apply_symm_apply] using hh
  obtain ⟨p, hp, _⟩ := Matrix.PSL3Two.Fano.unique_line a b hab
  refine ⟨(f.planes p).val, (f.planes p).property, ?_, ?_⟩
  · have hh := (f.incident a p).mpr hp.1
    simpa only [a, Equiv.apply_symm_apply] using hh
  · have hh := (f.incident b p).mpr hp.2
    simpa only [b, Equiv.apply_symm_apply] using hh

theorem a3_collinear_trans {x y z : S.Point}
    (hxy : S.Collinear x y) (hyz : S.Collinear y z) : S.Collinear x z := by
  obtain ⟨l, hxl, hyl⟩ := hxy
  obtain ⟨m, hym, hzm⟩ := hyz
  obtain ⟨π, _, hlπ, hmπ⟩ := S.a3_coplanar_incident_lines hyl hym
  exact S.collinear_of_common_plane (S.point_line_plane hxl hlπ)
    (S.point_line_plane hzm hmπ)

/-- I.5.9(2): every pair of original A₃ points is collinear. -/
theorem a3_collinear (x z : S.Point) : S.Collinear x z := by
  have ht := (SimpleGraph.reachable_iff_reflTransGen _ _).mp
    (S.pointGraph_connected.preconnected x z)
  induction ht with
  | refl => exact S.collinear_refl x
  | @tail y z hy hyz ih => exact S.a3_collinear_trans ih hyz.2

/-- Every actual line lies in a plane through the specified original point. -/
theorem a3_plane_cover (x : S.Point) (l : S.Line) :
    ∃ π : S.Plane, S.Inc x π ∧ S.Inc l π := by
  have hn : Nonempty {y : S.Point // S.Inc y l} :=
    (Nat.card_pos_iff.mp (by rw [S.line_points_card l]; decide)).1
  obtain ⟨y⟩ := hn
  obtain ⟨k, hxk, hyk⟩ := S.a3_collinear x y.val
  obtain ⟨π, _, hkπ, hlπ⟩ := S.a3_coplanar_incident_lines hyk y.property
  exact ⟨π, S.point_line_plane hxk hkπ, hlπ⟩

theorem a3_line_other_points_card {x : S.Point} {l : S.Line} (hx : S.Inc x l) :
    Nat.card {y : S.Point // S.Inc y l ∧ x ≠ y} = 2 := by
  classical
  let A := {y : S.Point // S.Inc y l}
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [S.line_points_card l]; decide)
  let := Fintype.ofFinite A
  let a : A := ⟨x, hx⟩
  let e : {y : S.Point // S.Inc y l ∧ x ≠ y} ≃ {y : A // ¬ y = a} := {
    toFun y := ⟨⟨y.val, y.property.1⟩, fun h => y.property.2 (congrArg Subtype.val h).symm⟩
    invFun y := ⟨y.val.val, y.val.property, fun h => y.property (Subtype.ext h.symm)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]
  have h : Fintype.card A = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact S.line_points_card l
  omega

def a3_NeighborFlag (x : S.Point) :=
  Σ l : {l : S.Line // S.Inc x l}, {y : S.Point // S.Inc y l.val ∧ x ≠ y}

def a3_neighborFlagEquiv (x : S.Point) :
    S.a3_NeighborFlag x ≃ {y : S.Point // x ≠ y ∧ S.Collinear x y} := by
  let f : S.a3_NeighborFlag x → {y : S.Point // x ≠ y ∧ S.Collinear x y} :=
    fun p => ⟨p.2.val, p.2.property.2, p.1.val, p.1.property, p.2.property.1⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨l, y⟩ ⟨m, z⟩ h
    have hyv : y.val = z.val := congrArg Subtype.val h
    have hlm : l = m := Subtype.ext (S.a3_unique_line y.property.2 l.property y.property.1
      m.property (hyv.symm ▸ z.property.1))
    subst m
    have hyz : y = z := Subtype.ext hyv
    exact congrArg (Sigma.mk l) hyz
  · rintro ⟨y, hxy, l, hxl, hyl⟩
    exact ⟨⟨⟨l, hxl⟩, ⟨y, hyl, hxy⟩⟩, rfl⟩

/-- I.5.9(1), in type A₃: the exact neighbor count in the original geometry. -/
theorem a3_neighbors_card (x : S.Point) :
    Nat.card {y : S.Point // x ≠ y ∧ S.Collinear x y} = 14 := by
  classical
  let A := {l : S.Line // S.Inc x l}
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [S.a3_point_lines_card x]; decide)
  let := Fintype.ofFinite A
  let (l : A) : Finite {y : S.Point // S.Inc y l.val ∧ x ≠ y} :=
    Nat.finite_of_card_ne_zero (by rw [S.a3_line_other_points_card l.property]; decide)
  rw [← Nat.card_congr (S.a3_neighborFlagEquiv x)]
  change Nat.card (Σ l : A, {y : S.Point // S.Inc y l.val ∧ x ≠ y}) = 14
  rw [Nat.card_sigma]
  have h : Fintype.card A = 7 := by
    rw [← Nat.card_eq_fintype_card]
    exact S.a3_point_lines_card x
  calc
    _ = ∑ _l : A, 2 := by
      apply Finset.sum_congr rfl
      intro l _
      exact S.a3_line_other_points_card l.property
    _ = Fintype.card A * 2 := by simp
    _ = 14 := by rw [h]

def a3_pointOptionNeighborEquiv (x : S.Point) :
    S.Point ≃ Option {y : S.Point // x ≠ y ∧ S.Collinear x y} := by
  classical
  refine {
    toFun := fun z => if h : x = z then none else some ⟨z, h, S.a3_collinear x z⟩
    invFun := fun z => match z with
      | none => x
      | some y => y.val
    left_inv := ?_
    right_inv := ?_ }
  · intro z
    dsimp only
    split_ifs with h
    · exact h
    · rfl
  · intro z
    cases z with
    | none => simp only [dite_true]
    | some y => simp only [y.property.1, dite_false]

theorem a3_points_card : Nat.card S.Point = 15 := by
  let A := {y : S.Point // S.basePoint ≠ y ∧ S.Collinear S.basePoint y}
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [S.a3_neighbors_card]; decide)
  rw [Nat.card_congr (S.a3_pointOptionNeighborEquiv S.basePoint),
    Finite.card_option, S.a3_neighbors_card]

theorem a3_exists_third_line_point {x y : S.Point} {l : S.Line}
    (hx : S.Inc x l) (hy : S.Inc y l) (hxy : x ≠ y) :
    ∃ z : S.Point, S.Inc z l ∧ x ≠ z ∧ y ≠ z ∧
      ∀ w : S.Point, S.Inc w l → w = x ∨ w = y ∨ w = z := by
  classical
  let A := {w : S.Point // S.Inc w l}
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [S.line_points_card l]; decide)
  let := Fintype.ofFinite A
  let e : A ≃ Fin 3 := Fintype.equivFinOfCardEq
    (by rw [← Nat.card_eq_fintype_card]; exact S.line_points_card l)
  let a : A := ⟨x, hx⟩
  let b : A := ⟨y, hy⟩
  obtain ⟨k, hka, hkb⟩ := Fin.exists_ne_and_ne_of_two_lt (e a) (e b) (by decide : 2 < 3)
  let z := e.symm k
  have haz : x ≠ z.val := fun h => hka (by
    simpa only [z, Equiv.apply_symm_apply] using congrArg e (show e.symm k = a from Subtype.ext h.symm))
  have hbz : y ≠ z.val := fun h => hkb (by
    simpa only [z, Equiv.apply_symm_apply] using congrArg e (show e.symm k = b from Subtype.ext h.symm))
  refine ⟨z.val, z.property, haz, hbz, fun w hw => ?_⟩
  let c : A := ⟨w, hw⟩
  have hab : e a ≠ e b := fun h => hxy (congrArg Subtype.val (e.injective h))
  have hc : e c = e a ∨ e c = e b ∨ e c = k := by
    have haa := (e a).isLt
    have hbb := (e b).isLt
    have hcc := (e c).isLt
    have hkk := k.isLt
    have h1 := (Fin.val_injective.ne hab)
    have h2 := (Fin.val_injective.ne hka)
    have h3 := (Fin.val_injective.ne hkb)
    simp only [Fin.ext_iff]
    omega
  rcases hc with h | h | h
  · exact Or.inl (congrArg Subtype.val (e.injective h))
  · exact Or.inr (Or.inl (congrArg Subtype.val (e.injective h)))
  · exact Or.inr (Or.inr (congrArg Subtype.val (e.eq_symm_apply.mpr h)))

/-- The three-point line needed in the A₃ permutation-module construction. -/
theorem a3_line_points (x y : S.Point) (hxy : x ≠ y) :
    ∃ l : S.Line, ∃ z : S.Point, z ≠ x ∧ z ≠ y ∧
      ∀ p : S.Point, S.Inc p l ↔ p = x ∨ p = y ∨ p = z := by
  obtain ⟨l, hx, hy⟩ := S.a3_collinear x y
  obtain ⟨z, hz, hxz, hyz, hh⟩ := S.a3_exists_third_line_point hx hy hxy
  refine ⟨l, z, Ne.symm hxz, Ne.symm hyz, fun p => ⟨hh p, ?_⟩⟩
  rintro (rfl | rfl | rfl)
  · exact hx
  · exact hy
  · exact hz

end Quasithin.I5.DSystem
