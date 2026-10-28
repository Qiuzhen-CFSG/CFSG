module
public import Theory.Representation.BinaryAlternatingFiveFlag.Borel

/-!
# The marked plane orbit in the binary five-point core

The A₄ point stabilizer is transitive on the six vectors of the standard
three-space outside its fixed line. Hence every subgroup strictly above
the line can be moved to contain the standard plane. The certificates use
only the twelve even permutations fixing the fifth letter and sixteen
vectors. This is the module transport needed in13.5.13.
-/
@[expose] public section
namespace BinaryPermutation.AlternatingFiveFlag
open Subgroup FiveCentralizerGeometry AlternatingFiveBorel

local instance : DecidablePred (· ∈ B) := fun g => inferInstanceAs (Decidable (g.val 4=4))
local instance : Fintype B := Subtype.fintype _

def coordinateMap (g : Perm) : Multiplicative Space →* Multiplicative Space :=
  AddMonoidHom.toMultiplicative (rho g).toAddMonoidHom

/-- The standard plane of the original flag. -/
def plane : Subgroup (Multiplicative Space) where
  carrier := {x | x = 1 ∨ x = Multiplicative.ofAdd z ∨
    x = Multiplicative.ofAdd v ∨ x = Multiplicative.ofAdd (z+v)}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl|rfl|rfl|rfl) (rfl|rfl|rfl|rfl) <;> decide +kernel
  inv_mem' := by
    rintro x (rfl|rfl|rfl|rfl) <;> decide +kernel
instance : DecidablePred (· ∈ plane) := fun _ => inferInstanceAs (Decidable (_∨_∨_∨_))
instance : Fintype plane := Subtype.fintype _

theorem plane_card : Nat.card plane = 4 := by rw [Nat.card_eq_fintype_card]; decide +kernel

theorem line_le_plane : line ≤ plane := by
  rintro x (rfl|rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

theorem plane_le_three : plane ≤ three := by
  rintro x (rfl|rfl|rfl|rfl) <;> rfl

/-- The actual Borel is transitive on vectors outside its fixed line. -/
theorem nonline_transitive (x y : Multiplicative Space)
    (hx : x ∈ three) (hxn : x ∉ line) (hy : y ∈ three) (hyn : y ∉ line) :
    ∃ g : B, Multiplicative.ofAdd (rho g.val.val x.toAdd) = y := by
  have hc : ∀ x y : Multiplicative Space,
      x ∈ three → x ∉ line → y ∈ three → y ∉ line →
      ∃ g : B, Multiplicative.ofAdd (rho g.val.val x.toAdd) = y := by decide +kernel
  exact hc x y hx hxn hy hyn

/-- One original Borel element moves a given larger subgroup onto the flag plane. -/
theorem plane_le_image (W : Subgroup (Multiplicative Space))
    (hline : line < W) (hthree : W ≤ three) :
    ∃ g : B, plane ≤ W.map (coordinateMap g.val.val) := by
  obtain ⟨x,hx,hxn⟩ := SetLike.not_le_iff_exists.mp hline.not_ge
  obtain ⟨g,hg⟩ := nonline_transitive x (Multiplicative.ofAdd v) (hthree hx) hxn
    (by rfl) (by decide +kernel)
  have hz : rho g.val.val z = z := (fixes_z_iff _).mpr g.property
  refine ⟨g,?_⟩
  have hmz : Multiplicative.ofAdd z ∈ W.map (coordinateMap g.val.val) := by
    refine ⟨_,hline.le (Or.inr rfl),?_⟩
    exact congrArg Multiplicative.ofAdd hz
  have hmv : Multiplicative.ofAdd v ∈ W.map (coordinateMap g.val.val) :=
    ⟨x,hx,hg⟩
  rintro y (rfl|rfl|rfl|rfl)
  · exact one_mem _
  · exact hmz
  · exact hmv
  · exact (W.map (coordinateMap g.val.val)).mul_mem hmz hmv

end BinaryPermutation.AlternatingFiveFlag
