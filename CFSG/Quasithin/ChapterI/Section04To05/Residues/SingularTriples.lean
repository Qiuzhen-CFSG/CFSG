module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.CommonNeighbors
public import Theory.LinearAlgebra.BinaryPolarGeometry

/-!
# One-or-all triples on the original singular lines

Every original line has three points. The nearest-point theorem gives at
least one point collinear with any given point, and two such points force
all three. This supplies the singular half of the triples used in I.5.15.

Source: I.5.9(3v) and I.5.15, printed pp.422 and 424.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup Theory.LinearAlgebra
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem exists_third_line_point {x y : S.Point} {l : S.Line}
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

theorem singular_one_or_all (d : S.LocalPolarFacts) {x y : S.Point}
    (hxy : x ≠ y) (hcol : S.Collinear x y) :
    ∃ z : S.Point, BinaryPolarGeometry.OneOrAll S.Collinear x y z := by
  obtain ⟨l, hxl, hyl⟩ := hcol
  obtain ⟨z, hzl, hxz, hyz, hall⟩ := S.exists_third_line_point hxl hyl hxy
  refine ⟨z, fun w => ?_⟩
  have hab : S.Collinear w x → S.Collinear w y → S.Collinear w z :=
    fun ha hb => S.line_all_collinear_of_two d hxl hyl hxy ha hb z hzl
  have hac : S.Collinear w x → S.Collinear w z → S.Collinear w y :=
    fun ha hc => S.line_all_collinear_of_two d hxl hzl hxz ha hc y hyl
  have hbc : S.Collinear w y → S.Collinear w z → S.Collinear w x :=
    fun hb hc => S.line_all_collinear_of_two d hyl hzl hyz hb hc x hxl
  have hany : S.Collinear w x ∨ S.Collinear w y ∨ S.Collinear w z := by
    obtain ⟨u, hul, hwu⟩ := S.line_has_collinear_point d w l
    rcases hall u hul with h | h | h
    · exact Or.inl (h ▸ hwu)
    · exact Or.inr (Or.inl (h ▸ hwu))
    · exact Or.inr (Or.inr (h ▸ hwu))
  tauto

end Quasithin.I5.DSystem
