module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.WreathedSylow
public import Theory.GroupTheory.WreathedThirtyTwo
public import ABG.ChapterII.Section1.WreathedRegularModel

/-!
# Binary G₂ Sylow invariants for the full marked amalgam

Three squarings of the six binary positive-root coordinates are zero,
so the full common Sylow has exponent dividing eight. The actual derived
Sylow is the established wreathed group of order 32; it is noncommutative
and contains an element of order eight. These are the model invariants
used through the literal source embedding in Aschbacher–Smith F.6.18(11).
-/

public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.BinaryParabolicPair
open Explicit
private def squareParameters (a : Fin 6 → ZMod 2) := unipotentProductParameters a a
private theorem parameters_eight : ∀ a : Fin 6 → ZMod 2,
    squareParameters (squareParameters (squareParameters a)) = 0 := by decide +kernel
private theorem product_square (a : Fin 6 → ZMod 2) :
    unipotentProduct a ^ 2 = unipotentProduct (squareParameters a) := by
  rw [pow_two,unipotentProduct_mul]
  rfl

theorem commonSylow_pow_eight (x : commonSylow) : x ^ 8 = 1 := by
  have hx : (x : Model (ZMod 2)) ∈ unipotent := x.property
  rw [unipotent_eq_range] at hx
  obtain ⟨a,ha⟩ := hx
  apply Subtype.ext
  change (x : Model (ZMod 2)) ^ 8 = 1
  rw [← ha]
  calc
    _ = ((unipotentProduct a ^ 2) ^ 2) ^ 2 := by simp only [← pow_mul]
    _ = 1 := by rw [product_square,product_square,product_square,
      parameters_eight,unipotentProduct_zero]

theorem derivedSylow_equiv_wreathed : Nonempty (derivedSylow ≃* WreathedThirtyTwo) :=
  derivedSylow_isWreathedOfHeight.nonempty_mulEquiv_regularWreath

private def w : WreathedThirtyTwo :=
  ⟨fun q => if q = 1 then Multiplicative.ofAdd 1 else 1, Multiplicative.ofAdd 1⟩
private theorem order_w : orderOf w = 8 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 2)
  · intro h
    have hh := congrArg (fun g : WreathedThirtyTwo => g.left 1) h
    change (2 : ZMod 4) = 0 at hh
    exact (by decide : (2 : ZMod 4) ≠ 0) hh
  · exact wreathedThirtyTwo_pow_eight w

theorem derivedSylow_order_eight : ∃ x : derivedSylow, orderOf x = 8 := by
  obtain ⟨e⟩ := derivedSylow_equiv_wreathed
  exact ⟨e.symm w,(e.symm.orderOf_eq w).trans order_w⟩

theorem derivedSylow_not_commutative : ¬ IsMulCommutative derivedSylow := by
  obtain ⟨e⟩ := derivedSylow_equiv_wreathed
  intro h
  apply wreathedThirtyTwo_not_commutative
  exact isMulCommutative_iff.mpr fun x y => e.symm.injective (by
    simpa only [map_mul] using (isMulCommutative_iff.mp h) (e.symm x) (e.symm y))
end Atlas.G2.BinaryParabolicPair
