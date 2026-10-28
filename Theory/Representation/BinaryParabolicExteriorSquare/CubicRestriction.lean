module
public import Theory.Representation.BinaryParabolicExteriorSquare.CubicSpan
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Cubic fixed indices on binary natural and exterior modules

A marked cubic rotating one natural plane fixes the complementary plane.
On the exterior square it fixes only the two exterior plane lines, and so
has fixed index sixteen. Contragredient duality gives fixed index four on
the dual natural module. The paired rotation on two radical planes has
no nonzero fixed vector. Each computation uses only the displayed generator;
no irreducible or chief multiplicities are assumed.

These are the four local module calculations in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 13.8.31(3), printed p.965.
The exterior action uses the existing attributed ATLAS bivector model.
-/

public section
open Representation
open Atlas.Order20160A8.Bivectors
namespace Representation.BinaryParabolicExteriorSquare.PlaneSpan

variable {A : Type*} [Group A]

private theorem invariants_card_of_generator {W : Type*} [AddCommGroup W]
    [Module Bit W] (ρ : Representation Bit A W) (a : A)
    (ha : ∀ b, b ∈ Subgroup.zpowers a) :
    Nat.card ρ.invariants = Nat.card {w : W // ρ a w = w} := by
  apply Nat.card_congr
  exact {
    toFun := fun w => ⟨w.val, w.property a⟩
    invFun := fun w => ⟨w.val, (ρ.mem_invariants_iff_of_forall_mem_zpowers a ha w.val).mpr w.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The marked cubic has a fixed plane on the binary natural four-space. -/
theorem natural_cubic_fixedIndex
    (ρ : Representation Bit A (Fin 4 → Bit)) (a : A)
    (ha : ∀ b, b ∈ Subgroup.zpowers a)
    (hact : ∀ v, ρ a v = Matrix.mulVec planeCubic v) :
    BinaryFixedPoints.fixedIndex ρ = 4 := by
  have hc : Nat.card ρ.invariants = 4 := by
    rw [invariants_card_of_generator ρ a ha]
    simp_rw [hact]
    rw [Nat.card_eq_fintype_card]
    decide
  have hm := BinaryFixedPoints.fixedIndex_mul_card ρ
  rw [hc] at hm
  have hv : Nat.card (Fin 4 → Bit) = 16 := by simp [Bit]
  rw [hv] at hm
  omega

/-- The same cubic moves four dimensions on the exterior six-space. -/
theorem exterior_cubic_fixedIndex
    (ρ : Representation Bit A Six) (a : A)
    (ha : ∀ b, b ∈ Subgroup.zpowers a)
    (hact : ∀ v, ρ a v = exteriorMap planeCubic v) :
    BinaryFixedPoints.fixedIndex ρ = 16 := by
  have hc : Nat.card ρ.invariants = 4 := by
    rw [invariants_card_of_generator ρ a ha]
    simp_rw [hact, exterior_planeCubic]
    rw [Nat.card_eq_fintype_card]
    decide
  have hm := BinaryFixedPoints.fixedIndex_mul_card ρ
  rw [hc] at hm
  have hv : Nat.card Six = 64 := by simp [Six, Bit]
  rw [hv] at hm
  omega

/-- Contragredient duality retains the literal generator and fixed index. -/
theorem dual_natural_cubic_fixedIndex
    (ρ : Representation Bit A (Fin 4 → Bit)) (a : A)
    (ha : ∀ b, b ∈ Subgroup.zpowers a)
    (hact : ∀ v, ρ a v = Matrix.mulVec planeCubic v) :
    BinaryFixedPoints.fixedIndex ρ.dual = 4 :=
  (BinaryFixedPoints.fixedIndex_dual ρ a ha).trans
    (natural_cubic_fixedIndex ρ a ha hact)

/-- The same irreducible binary cubic on each of two radical planes. -/
@[expose] def pairedCubic : Matrix (Fin 4) (Fin 4) Bit :=
  !![0,1,0,0; 1,1,0,0; 0,0,0,1; 0,0,1,1]

/-- The two radical planes are both fully moved by the marked cubic. -/
theorem paired_cubic_fixedIndex
    (ρ : Representation Bit A (Fin 4 → Bit)) (a : A)
    (ha : ∀ b, b ∈ Subgroup.zpowers a)
    (hact : ∀ v, ρ a v = Matrix.mulVec pairedCubic v) :
    BinaryFixedPoints.fixedIndex ρ = 16 := by
  have hc : Nat.card ρ.invariants = 1 := by
    rw [invariants_card_of_generator ρ a ha]
    simp_rw [hact]
    rw [Nat.card_eq_fintype_card]
    decide
  have hm := BinaryFixedPoints.fixedIndex_mul_card ρ
  rw [hc, mul_one] at hm
  exact hm.trans (by simp [Bit])

end Representation.BinaryParabolicExteriorSquare.PlaneSpan
