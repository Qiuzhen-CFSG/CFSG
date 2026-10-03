module
public import Theory.Combinatorics.ProjectivePlaneThreeTable

/-!
# Extending a quadrangle frame in an order-three plane

The four vertices and three diagonal points form a seven-point frame.
Each side contains three of these points. Its fourth point lies on no other
side, since every two sides already intersect in the frame. Adding these six
points gives the thirteen-point side chart used for coordinatization.

This is the quadrangle proof of the uniqueness of the plane of order three;
see Wong, Theorem 6(b), printed p.111 (10.1017/S1446788700022771).
-/

@[expose] public section

namespace Configuration.Three

/-- The first seven points of the quadrangle labeling: four vertices and
three intersections of opposite sides. -/
structure Frame (P L : Type*) [Membership P L] where
  point : Fin 7 → P
  side : Fin 6 → L
  incident : ∀ i j, point i ∈ side j ↔
    i.castLE (by decide) ∈ line (j.castLE (by decide))

private theorem frame_points_distinguished : ∀ i k : Fin 7,
    (∀ j : Fin 6, i.castLE (by decide) ∈ line (j.castLE (by decide)) ↔
      k.castLE (by decide) ∈ line (j.castLE (by decide))) → i = k := by
  decide +kernel

private theorem frame_sides_distinguished : ∀ j k : Fin 6,
    (∀ i : Fin 7, i.castLE (by decide) ∈ line (j.castLE (by decide)) ↔
      i.castLE (by decide) ∈ line (k.castLE (by decide))) → j = k := by
  decide +kernel

private theorem frame_sides_meet : ∀ j k : Fin 6, ∃ i : Fin 7,
    i.castLE (by decide) ∈ line (j.castLE (by decide)) ∧
      i.castLE (by decide) ∈ line (k.castLE (by decide)) := by
  decide +kernel

private theorem frame_side_card : ∀ j : Fin 6,
    (Finset.univ.filter (fun i : Fin 7 =>
      i.castLE (by decide) ∈ line (j.castLE (by decide)))).card = 3 := by
  decide +kernel

private theorem extra_incidence : ∀ (i : Fin 13) (j : Fin 6), 7 ≤ i.val →
    (i ∈ line (j.castLE (by decide)) ↔ i.val - 7 = j.val) := by
  decide +kernel

namespace Frame

variable {P L : Type*} [Membership P L] (f : Frame P L)

theorem point_injective : Function.Injective f.point := by
  intro i k hik
  apply frame_points_distinguished i k
  intro j
  rw [← f.incident, ← f.incident, hik]

theorem side_injective : Function.Injective f.side := by
  intro j k hjk
  apply frame_sides_distinguished j k
  intro i
  rw [← f.incident, ← f.incident, hjk]

theorem sides_meet (j k : Fin 6) : ∃ i, f.point i ∈ f.side j ∧ f.point i ∈ f.side k := by
  simpa only [f.incident] using frame_sides_meet j k

variable [Finite P] [Nondegenerate P L] (h : ∀ l : L, pointCount P l = 4)

include h in
omit [Nondegenerate P L] in
theorem exists_fourth (j : Fin 6) : ∃ p : P, p ∈ f.side j ∧ ∀ i, p ≠ f.point i := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let s := Finset.univ.filter (fun i : Fin 7 => f.point i ∈ f.side j)
  let t := Finset.univ.filter (fun p : P => p ∈ f.side j)
  have hs : s.card = 3 := by
    simpa only [s, f.incident] using frame_side_card j
  have ht : t.card = 4 := by
    simpa only [pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype] using h (f.side j)
  have hc : (s.image f.point).card < t.card := by
    rw [Finset.card_image_of_injective _ f.point_injective, hs, ht]
    decide
  obtain ⟨p, hp, hps⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨p, (Finset.mem_filter.mp hp).2, ?_⟩
  intro i hi
  apply hps
  apply Finset.mem_image.mpr
  refine ⟨i, ?_, hi.symm⟩
  simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, ← hi] using
    (Finset.mem_filter.mp hp).2

/-- The remaining point on a side, outside the seven-point frame. -/
noncomputable def fourth (j : Fin 6) : P := (f.exists_fourth h j).choose

theorem fourth_mem_iff (j k : Fin 6) : f.fourth h j ∈ f.side k ↔ j = k := by
  have hj := (f.exists_fourth h j).choose_spec
  change f.fourth h j ∈ f.side j ∧ ∀ i, f.fourth h j ≠ f.point i at hj
  constructor
  · intro hk
    obtain ⟨i, hij, hik⟩ := f.sides_meet j k
    exact f.side_injective ((Nondegenerate.eq_or_eq hj.1 hij hk hik).resolve_left (hj.2 i))
  · rintro rfl
    exact hj.1

/-- Complete the seven-point frame by the fourth point of each side. -/
noncomputable def toSideChart : SideChart P L where
  point i := if hi : i.val < 7 then f.point ⟨i.val, hi⟩
    else f.fourth h ⟨i.val - 7, by omega⟩
  side := f.side
  incident i j := by
    split_ifs with hi
    · exact f.incident ⟨i.val, hi⟩ j
    · rw [f.fourth_mem_iff, extra_incidence i j (by omega)]
      exact Fin.ext_iff

end Frame

end Configuration.Three
