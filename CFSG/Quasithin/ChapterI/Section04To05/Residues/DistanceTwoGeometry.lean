module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.TwoLinePaths

/-!
# Global consequences of the literal local polar residues

The three local inputs below are the eight-object orbit, its stabilizer
transporter, and the point-line projection axiom of the actual A₆/S₆
quadrangle. The separate polar-residue producer supplies them through the
original quotient maps. The global argument retains the original cosets,
lines and planes throughout.

Source: I.5.9(3), printed pp.421–422.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

structure LocalPolarFacts : Prop where
  noncoplanar_card : ∀ (x : S.Point) (l : S.Line), S.Inc x l →
    Nat.card {m : S.Line // S.Inc x m ∧ ¬ S.CoplanarLines l m} = 8
  transporter : ∀ (x : S.Point) (l k m : S.Line), S.Inc x l → S.Inc x k → S.Inc x m →
    ¬ S.CoplanarLines l k → ¬ S.CoplanarLines l m →
    ∃ g : G, g • x = x ∧ g • l = l ∧ g • k = m
  projection : ∀ (x : S.Point) (k : S.Line) (π : S.Plane), S.Inc x k → S.Inc x π →
    ∃ n : S.Line, S.Inc x n ∧ S.Inc n π ∧ S.CoplanarLines k n

theorem twoLinePath_endpoint_noncollinear (d : S.LocalPolarFacts)
    {x : S.Point} (p : S.TwoLinePath x) : ¬ S.Collinear x p.endpoint := by
  obtain ⟨y, z, l, m, hxy, hyz, hxl, hyl, hym, hzm, hxz, hplane⟩ :=
    S.exists_noncoplanar_two_line_path x
  let q : S.TwoLinePath x := ⟨y, z, l, m, hxy, hyz, hxl, hyl, hym, hzm, hplane⟩
  obtain ⟨g, hgx, _, hgez, _, _⟩ := S.twoLinePaths_transitive d.transporter p q
  intro h
  exact hxz (by simpa only [hgx, hgez] using h.smul S g)

theorem collinear_iff_coplanar_at_middle (d : S.LocalPolarFacts)
    {x y z : S.Point} {l m : S.Line} (hxy : x ≠ y) (hxz : x ≠ z)
    (hxl : S.Inc x l) (hyl : S.Inc y l) (hxm : S.Inc x m) (hzm : S.Inc z m) :
    S.Collinear y z ↔ S.CoplanarLines l m := by
  constructor
  · intro h
    by_contra hn
    exact S.twoLinePath_endpoint_noncollinear d
      (⟨x, z, l, m, hxy.symm, hxz, hyl, hxl, hxm, hzm, hn⟩ : S.TwoLinePath y) h
  · exact S.collinear_of_coplanar_lines hyl hzm

theorem line_all_collinear_of_two (d : S.LocalPolarFacts)
    {z u v : S.Point} {l : S.Line} (hu : S.Inc u l) (hv : S.Inc v l)
    (huv : u ≠ v) (hzu : S.Collinear z u) (hzv : S.Collinear z v) :
    ∀ w : S.Point, S.Inc w l → S.Collinear z w := by
  by_cases huz : u = z
  · intro w hw
    exact ⟨l, huz ▸ hu, hw⟩
  obtain ⟨k, hzk, huk⟩ := hzu
  have hplane := (S.collinear_iff_coplanar_at_middle d huv huz hu hv huk hzk).mp
    (S.collinear_symm hzv)
  intro w hw
  exact S.collinear_symm (S.collinear_of_coplanar_lines hw hzk hplane)

theorem coplanar_lines_meet {l m : S.Line} (h : S.CoplanarLines l m) :
    ∃ y : S.Point, S.Inc y l ∧ S.Inc y m := by
  obtain ⟨π, hl, hm⟩ := h
  obtain ⟨f⟩ := S.exists_fanoPlaneResidue π
  let a := f.lines.symm ⟨l, hl⟩
  let b := f.lines.symm ⟨m, hm⟩
  by_cases hab : a = b
  · have hc := S.line_points_card l
    have hn : Nonempty {y : S.Point // S.Inc y l} := Nat.card_pos_iff.mp (by rw [hc]; decide) |>.1
    obtain ⟨y⟩ := hn
    have hlm : l = m := by
      have hh := congrArg (fun a => (f.lines a).val) hab
      simpa only [a, b, Equiv.apply_symm_apply] using hh
    exact ⟨y.val, y.property, hlm ▸ y.property⟩
  obtain ⟨p, hp, _⟩ := Matrix.PSL3Two.Fano.unique_point a b hab
  refine ⟨(f.points p).val, ?_, ?_⟩
  · have hh := (f.incident p a).mpr hp.1
    simpa only [a, Equiv.apply_symm_apply] using hh
  · have hh := (f.incident p b).mpr hp.2
    simpa only [b, Equiv.apply_symm_apply] using hh

theorem collinear_point_transfer (d : S.LocalPolarFacts)
    {z u : S.Point} {l m : S.Line} (hlm : S.CoplanarLines l m)
    (hul : S.Inc u l) (hzu : S.Collinear z u) :
    ∃ v : S.Point, S.Inc v m ∧ S.Collinear z v := by
  obtain ⟨π, hlπ, hmπ⟩ := hlm
  obtain ⟨k, hzk, huk⟩ := hzu
  obtain ⟨n, hun, hnπ, hkn⟩ := d.projection u k π huk (S.point_line_plane hul hlπ)
  obtain ⟨v, hvm, hvn⟩ := S.coplanar_lines_meet ⟨π, hmπ, hnπ⟩
  exact ⟨v, hvm, S.collinear_of_coplanar_lines hzk hvn hkn⟩

theorem coplanar_two_step_at_point (d : S.LocalPolarFacts)
    {x : S.Point} {l m : S.Line} (hxl : S.Inc x l) (hxm : S.Inc x m) :
    ∃ n : S.Line, S.Inc x n ∧ S.CoplanarLines l n ∧ S.CoplanarLines n m := by
  obtain ⟨π, hlπ, _⟩ := S.coplanarLines_refl l
  obtain ⟨n, hxn, hnπ, σ, hmσ, hnσ⟩ :=
    d.projection x m π hxm (S.point_line_plane hxl hlπ)
  exact ⟨n, hxn, ⟨π, hlπ, hnπ⟩, ⟨σ, hnσ, hmσ⟩⟩

theorem line_has_collinear_point_of_common_neighbor (d : S.LocalPolarFacts)
    {x z : S.Point} (h : ∃ y : S.Point, S.Collinear x y ∧ S.Collinear z y)
    {m : S.Line} (hxm : S.Inc x m) :
    ∃ u : S.Point, S.Inc u m ∧ S.Collinear z u := by
  obtain ⟨y, ⟨l, hxl, hyl⟩, hzy⟩ := h
  obtain ⟨n, _, hln, hnm⟩ := S.coplanar_two_step_at_point d hxl hxm
  obtain ⟨v, hvn, hzv⟩ := S.collinear_point_transfer d hln hyl hzy
  exact S.collinear_point_transfer d hnm hvn hzv

theorem unique_collinear_point_of_common_neighbor (d : S.LocalPolarFacts)
    {x z : S.Point} (hxz : ¬ S.Collinear x z)
    (h : ∃ y : S.Point, S.Collinear x y ∧ S.Collinear z y)
    {m : S.Line} (hxm : S.Inc x m) :
    ∃! u : S.Point, S.Inc u m ∧ S.Collinear z u := by
  obtain ⟨u, hum, hzu⟩ := S.line_has_collinear_point_of_common_neighbor d h hxm
  refine ⟨u, ⟨hum, hzu⟩, fun v hv => ?_⟩
  by_contra hne
  exact hxz (S.collinear_symm (S.line_all_collinear_of_two d hv.1 hum hne hv.2 hzu x hxm))

theorem pointGraph_diameter_two (d : S.LocalPolarFacts) (x z : S.Point) :
    ∃ y : S.Point, S.Collinear x y ∧ S.Collinear y z := by
  have hr := S.pointGraph_connected.preconnected x z
  have ht := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hr
  clear hr
  induction ht with
  | refl => exact ⟨x, S.collinear_refl x, S.collinear_refl x⟩
  | @tail y z hy hyz ih =>
    obtain ⟨m, hym, hzm⟩ := hyz.2
    obtain ⟨v, hvm, hxv⟩ := S.line_has_collinear_point_of_common_neighbor d
      (by obtain ⟨u, hxu, huy⟩ := ih; exact ⟨u, S.collinear_symm huy, hxu⟩) hym
    exact ⟨v, hxv, m, hvm, hzm⟩

theorem line_has_collinear_point (d : S.LocalPolarFacts) (z : S.Point) (l : S.Line) :
    ∃ u : S.Point, S.Inc u l ∧ S.Collinear z u := by
  have hn : Nonempty {x : S.Point // S.Inc x l} :=
    (Nat.card_pos_iff.mp (by rw [S.line_points_card l]; decide)).1
  obtain ⟨x⟩ := hn
  obtain ⟨y, hxy, hyz⟩ := S.pointGraph_diameter_two d x.val z
  exact S.line_has_collinear_point_of_common_neighbor d
    ⟨y, hxy, S.collinear_symm hyz⟩ x.property

theorem unique_collinear_point_on_line (d : S.LocalPolarFacts)
    {x z : S.Point} (hxz : ¬ S.Collinear x z) {l : S.Line} (hxl : S.Inc x l) :
    ∃! u : S.Point, S.Inc u l ∧ S.Collinear z u := by
  obtain ⟨y, hxy, hyz⟩ := S.pointGraph_diameter_two d x z
  exact S.unique_collinear_point_of_common_neighbor d hxz
    ⟨y, hxy, S.collinear_symm hyz⟩ hxl

end Quasithin.I5.DSystem
