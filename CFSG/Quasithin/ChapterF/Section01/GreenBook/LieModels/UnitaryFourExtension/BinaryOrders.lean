module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.BinaryOrders
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension

/-!
# Binary unitary graph-extension orders

The literal extended parabolics are products as sets of the original
parabolics with the specified graph involution. The original membership
formulas give these bijections and preserve the actual first coordinates.
Thus all three orders double. The endpoint groups generate the full graph
extension because they contain the generating ordinary parabolics and the
common outer involution.

Source: Aschbacher–Smith F.4.24, printed pp.287–288, for the graph extension
of the unitary-four amalgam. These are model facts, not recognition assumptions.
-/
@[expose] public section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.Extension
open Theory.SpecificGroups.ClassicalUnitary
noncomputable section
local notation "h1" => (Nat.le_refl 1)
local notation "C" => UnitaryFourOuter.C2

def binaryPointEquivProd : point 1 h1 ≃ pointParabolic 1 h1 × C where
  toFun a := (⟨a.val.left, (mem_point 1 h1 a.val).mp a.property⟩, a.val.right)
  invFun a := ⟨⟨a.1.val, a.2⟩, (mem_point 1 h1 _).mpr a.1.property⟩
  left_inv _ := Subtype.ext (SemidirectProduct.ext rfl rfl)
  right_inv _ := rfl

def binaryPlaneEquivProd : plane 1 h1 ≃ planeParabolic 1 h1 × C where
  toFun a := (⟨a.val.left, (mem_plane 1 h1 a.val).mp a.property⟩, a.val.right)
  invFun a := ⟨⟨a.1.val, a.2⟩, (mem_plane 1 h1 _).mpr a.1.property⟩
  left_inv _ := Subtype.ext (SemidirectProduct.ext rfl rfl)
  right_inv _ := rfl

theorem binary_mem_overlap (a : ProjectiveExtension 1 h1) :
    a ∈ overlap 1 h1 ↔ a.left ∈ UnitaryFour.overlap 1 h1 := by
  rw [← exact_overlap, ← UnitaryFour.exact_overlap]
  exact and_congr (mem_point 1 h1 a) (mem_plane 1 h1 a)

def binaryOverlapEquivProd : overlap 1 h1 ≃ UnitaryFour.overlap 1 h1 × C where
  toFun a := (⟨a.val.left, (binary_mem_overlap a.val).mp a.property⟩, a.val.right)
  invFun a := ⟨⟨a.1.val, a.2⟩, (binary_mem_overlap _).mpr a.1.property⟩
  left_inv _ := Subtype.ext (SemidirectProduct.ext rfl rfl)
  right_inv _ := rfl

theorem binary_extension_card : Nat.card (ProjectiveExtension 1 h1) = 51840 := by
  rw [SemidirectProduct.card, BinaryCompletion.projective_card]
  change 25920 * Nat.card (ZMod 2) = 51840
  norm_num

instance binaryExtensionFinite : Finite (ProjectiveExtension 1 h1) :=
  Nat.finite_of_card_ne_zero (by rw [binary_extension_card]; decide)

theorem binary_point_card : Nat.card (point 1 h1) = 1152 := by
  rw [Nat.card_congr binaryPointEquivProd, Nat.card_prod, BinaryCompletion.point_card]
  change 576 * Nat.card (ZMod 2) = 1152
  norm_num

theorem binary_plane_card : Nat.card (plane 1 h1) = 1920 := by
  rw [Nat.card_congr binaryPlaneEquivProd, Nat.card_prod, BinaryCompletion.plane_card]
  change 960 * Nat.card (ZMod 2) = 1920
  norm_num

theorem binary_overlap_card : Nat.card (overlap 1 h1) = 384 := by
  rw [Nat.card_congr binaryOverlapEquivProd, Nat.card_prod, BinaryCompletion.middle_card]
  change 192 * Nat.card (ZMod 2) = 384
  norm_num
theorem binary_parabolics_generate : point 1 h1 ⊔ plane 1 h1 = ⊤ := by
  let R := point 1 h1 ⊔ plane 1 h1
  let f : ProjectiveGroup 1 h1 →* ProjectiveExtension 1 h1 := SemidirectProduct.inl
  have hp : (pointParabolic 1 h1).map f ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact (show point 1 h1 ≤ R from le_sup_left) ((mem_point 1 h1 _).mpr hx)
  have hq : (planeParabolic 1 h1).map f ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact (show plane 1 h1 ≤ R from le_sup_right) ((mem_plane 1 h1 _).mpr hx)
  have hi : (⊤ : Subgroup (ProjectiveGroup 1 h1)).map f ≤ R := by
    rw [← UnitaryFour.parabolics_generate 1 h1, Subgroup.map_sup]
    exact sup_le hp hq
  apply top_unique
  intro x _
  have hl : SemidirectProduct.inl x.left ∈ R := hi ⟨x.left, trivial, rfl⟩
  have hr : SemidirectProduct.inr x.right ∈ R :=
    (show point 1 h1 ≤ R from le_sup_left) ((mem_point 1 h1 _).mpr (pointParabolic 1 h1).one_mem)
  simpa only [SemidirectProduct.inl_left_mul_inr_right] using R.mul_mem hl hr

end
end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.Extension
