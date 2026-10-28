module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.DistanceTwoGeometry

/-!
# The sixty-three original points

Count the noncoplanar two-line paths from a point in two ways. There are
15 choices for the first line, two for the intermediate point, eight for
the second line, and two for the endpoint. Each distant endpoint occurs
once for every first line, by the unique nearest point property. Thus
there are 32 distant points, in addition to the point and its 30 neighbors.

Source: I.5.9(3iii–iv), printed p.422.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

def TwoLinePathFlags (x : S.Point) :=
  Σ l : {l : S.Line // S.Inc x l},
    Σ y : {y : S.Point // S.Inc y l.val ∧ x ≠ y},
      Σ m : {m : S.Line // S.Inc y.val m ∧ ¬ S.CoplanarLines l.val m},
        {z : S.Point // S.Inc z m.val ∧ y.val ≠ z}

def twoLinePathFlagsEquiv (x : S.Point) : S.TwoLinePathFlags x ≃ S.TwoLinePath x where
  toFun p := ⟨p.2.1.val, p.2.2.2.val, p.1.val, p.2.2.1.val,
    p.2.1.property.2, p.2.2.2.property.2, p.1.property, p.2.1.property.1,
    p.2.2.1.property.1, p.2.2.2.property.1, p.2.2.1.property.2⟩
  invFun p := ⟨⟨p.first, p.left_inc⟩, ⟨p.middle, p.middle_first, p.left_ne⟩,
    ⟨p.second, p.middle_second, p.noncoplanar⟩, ⟨p.endpoint, p.right_inc, p.right_ne⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem twoLinePaths_card (d : S.LocalPolarFacts) (x : S.Point) :
    Nat.card (S.TwoLinePath x) = 480 := by
  classical
  let L := {l : S.Line // S.Inc x l}
  let Y (l : L) := {y : S.Point // S.Inc y l.val ∧ x ≠ y}
  let M (l : L) (y : Y l) := {m : S.Line // S.Inc y.val m ∧ ¬ S.CoplanarLines l.val m}
  let Z (l : L) (y : Y l) (m : M l y) := {z : S.Point // S.Inc z m.val ∧ y.val ≠ z}
  let : Finite L := Nat.finite_of_card_ne_zero (by rw [S.c3_point_lines_card x]; decide)
  let := Fintype.ofFinite L
  let (l : L) : Finite (Y l) := Nat.finite_of_card_ne_zero
    (by rw [S.line_other_points_card l.property]; decide)
  let (l : L) := Fintype.ofFinite (Y l)
  let (l : L) (y : Y l) : Finite (M l y) := Nat.finite_of_card_ne_zero
    (by rw [d.noncoplanar_card y.val l.val y.property.1]; decide)
  let (l : L) (y : Y l) := Fintype.ofFinite (M l y)
  let (l : L) (y : Y l) (m : M l y) : Finite (Z l y m) := Nat.finite_of_card_ne_zero
    (by rw [S.line_other_points_card m.property.1]; decide)
  rw [← Nat.card_congr (S.twoLinePathFlagsEquiv x)]
  change Nat.card (Σ l : L, Σ y : Y l, Σ m : M l y, Z l y m) = 480
  rw [Nat.card_sigma]
  calc
    _ = ∑ _l : L, 32 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Nat.card_sigma]
      calc
        _ = ∑ _y : Y l, 16 := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Nat.card_sigma]
          calc
            _ = ∑ _m : M l y, 2 := by
              apply Finset.sum_congr rfl
              intro m _
              exact S.line_other_points_card m.property.1
            _ = 16 := by
              simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
              rw [← Nat.card_eq_fintype_card, d.noncoplanar_card y.val l.val y.property.1]
        _ = 32 := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          rw [← Nat.card_eq_fintype_card, S.line_other_points_card l.property]
    _ = 480 := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      rw [← Nat.card_eq_fintype_card, S.c3_point_lines_card x]

def twoLinePathEndpointLineEquiv (d : S.LocalPolarFacts) (x : S.Point) :
    S.TwoLinePath x ≃ {z : S.Point // ¬ S.Collinear x z} × {l : S.Line // S.Inc x l} := by
  let f : S.TwoLinePath x →
      {z : S.Point // ¬ S.Collinear x z} × {l : S.Line // S.Inc x l} := fun p =>
    (⟨p.endpoint, S.twoLinePath_endpoint_noncollinear d p⟩,
      ⟨p.first, p.left_inc⟩)
  apply Equiv.ofBijective f
  constructor
  · intro p q h
    have hz : p.endpoint = q.endpoint := congrArg (fun a => a.1.val) h
    have hl : p.first = q.first := congrArg (fun a => a.2.val) h
    obtain ⟨u, _, hu⟩ := S.unique_collinear_point_on_line d
      (S.twoLinePath_endpoint_noncollinear d p) p.left_inc
    have hp : p.middle = u := hu p.middle ⟨p.middle_first, p.second, p.right_inc, p.middle_second⟩
    have hq : q.middle = u := hu q.middle
      ⟨hl.symm ▸ q.middle_first, q.second, hz.symm ▸ q.right_inc, q.middle_second⟩
    have hy : p.middle = q.middle := hp.trans hq.symm
    have hm : p.second = q.second := S.unique_line p.right_ne p.middle_second p.right_inc
      (hy.symm ▸ q.middle_second) (hz.symm ▸ q.right_inc)
    cases p
    cases q
    dsimp only at hz hl hy hm
    cases hz
    cases hl
    cases hy
    cases hm
    rfl
  · rintro ⟨⟨z, hxz⟩, ⟨l, hxl⟩⟩
    obtain ⟨y, ⟨hyl, m, hzm, hym⟩, _⟩ := S.unique_collinear_point_on_line d hxz hxl
    have hxy : x ≠ y := fun h => hxz (h.symm ▸ (S.collinear_symm ⟨m, hzm, hym⟩))
    have hyz : y ≠ z := fun h => hxz ⟨l, hxl, h ▸ hyl⟩
    have hn : ¬ S.CoplanarLines l m := fun h => hxz (S.collinear_of_coplanar_lines hxl hzm h)
    exact ⟨⟨y, z, l, m, hxy, hyz, hxl, hyl, hym, hzm, hn⟩, rfl⟩

theorem c3_noncollinear_card (d : S.LocalPolarFacts) (x : S.Point) :
    Nat.card {z : S.Point // ¬ S.Collinear x z} = 32 := by
  have h := S.twoLinePaths_card d x
  rw [Nat.card_congr (S.twoLinePathEndpointLineEquiv d x), Nat.card_prod,
    S.c3_point_lines_card x] at h
  omega

def collinearOptionNeighborEquiv (x : S.Point) :
    {z : S.Point // S.Collinear x z} ≃ Option {y : S.Point // x ≠ y ∧ S.Collinear x y} := by
  classical
  refine {
    toFun := fun z => if h : x = z.val then none else some ⟨z.val, h, z.property⟩
    invFun := fun z => match z with
      | none => ⟨x, S.collinear_refl x⟩
      | some y => ⟨y.val, y.property.2⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro z
    dsimp only
    split_ifs with h
    · exact Subtype.ext h
    · rfl
  · intro z
    cases z with
    | none => simp only [dite_true]
    | some y => simp only [y.property.1, dite_false]

theorem c3_points_card (d : S.LocalPolarFacts) : Nat.card S.Point = 63 := by
  classical
  let x := S.basePoint
  let A := {y : S.Point // x ≠ y ∧ S.Collinear x y}
  let B := {z : S.Point // ¬ S.Collinear x z}
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [S.c3_neighbors_card x]; decide)
  let : Finite B := Nat.finite_of_card_ne_zero (by rw [S.c3_noncollinear_card d x]; decide)
  let : Finite {z : S.Point // S.Collinear x z} :=
    Finite.of_equiv (Option A) (S.collinearOptionNeighborEquiv x).symm
  rw [← Nat.card_congr (Equiv.sumCompl (S.Collinear x)), Nat.card_sum,
    Nat.card_congr (S.collinearOptionNeighborEquiv x), Finite.card_option,
    S.c3_neighbors_card x, S.c3_noncollinear_card d x]

end Quasithin.I5.DSystem
