module

public import Theory.Representation.BinaryAlternatingFiveBorel
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five
public import Theory.Representation.BinaryPermutation.FiveAction
/-!
# Moved hyperplanes in the binary alternating-five core

The regular Klein four fixes precisely the weight-four point. Its two
standard generators span the hyperplane of vectors vanishing at the fifth
coordinate, and preservation of that hyperplane detects the point stabilizer.
The certificates range only over the 32 binary words. Coordinate conjugation
allows these calculations to be used with any Sylow marking.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of G.2.4, printed pp.334--335.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace BinaryPermutation.FiveMovedHyperplanes
open CubicFixedSpace.Five
abbrev Space := core (Fin 5)
abbrev Actor := alternatingGroup (Fin 5)
abbrev act (a : Actor) := coreRepresentation (Fin 5) a.val

def coordinateAut (a : Actor) : Multiplicative Space ≃* Multiplicative Space where
  toFun x := Multiplicative.ofAdd (act a x.toAdd)
  invFun x := Multiplicative.ofAdd (act a⁻¹ x.toAdd)
  left_inv x := by
    change act a⁻¹ (act a x.toAdd) = x.toAdd
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  right_inv x := by
    change act a (act a⁻¹ x.toAdd) = x.toAdd
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  map_mul' x y := map_add (act a) x.toAdd y.toAdd

def moved : Subgroup (Multiplicative Space) :=
  AlternatingFiveBorel.moved.toAddSubgroup.toSubgroup

@[simp] theorem mem_moved (x : Multiplicative Space) : x ∈ moved ↔ x.toAdd.val 4 = 0 := AlternatingFiveBorel.mem_moved x.toAdd

theorem card_moved : Nat.card moved = 8 := by
  change Nat.card AlternatingFiveBorel.moved = 8
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    AlternatingFiveBorel.finrank_moved]
  rfl

theorem fixed_generators (x : Space) (hx : x ≠ 0)
    (ha : act first x = x) (hb : act second x = x) :
    x = AlternatingFiveBorel.fixedVector := by
  have h : ∀ v : Full (Fin 5), (∑ i, v i) = 0 → v ≠ 0 →
      representation (Fin 5) first.val v = v →
      representation (Fin 5) second.val v = v → v = ![1,1,1,1,0] := by decide
  apply Subtype.ext
  rw [AlternatingFiveBorel.fixedVector_coordinates]
  exact (h x.val x.property (fun he => hx (Subtype.ext he))
    (congrArg Subtype.val ha) (congrArg Subtype.val hb))

theorem fixes_point_iff (a : Actor) :
    act a AlternatingFiveBorel.fixedVector = AlternatingFiveBorel.fixedVector ↔
      a.val 4 = 4 := by
  constructor
  · intro he
    have hz := congrArg (fun v : Space => v.val (a.val 4)) he
    change AlternatingFiveBorel.fixedVector.val (a.val.symm (a.val 4)) = _ at hz
    rw [Equiv.symm_apply_apply] at hz
    have h : ∀ i : Fin 5, (![1,1,1,1,0] : Full (Fin 5)) i = 0 → i = 4 := by decide
    rw [AlternatingFiveBorel.fixedVector_coordinates] at hz
    exact h _ hz.symm
  · intro h
    exact AlternatingFiveBorel.fixedVector_fixed ⟨a, h⟩

private def root : Space := ⟨![1,0,0,0,1], by rw [mem_core]; decide⟩
private def delta (a : Actor) : Space := act a root - root

private theorem moved_expansion (x : Space) (hx : x.val 4 = 0) :
    x = (if x.val 1 = 0 then 0 else delta first) +
      (if x.val 2 = 0 then 0 else delta second) +
      (if x.val 3 = 0 then 0 else delta (first * second)) := by
  have h : ∀ v : Full (Fin 5), (∑ i, v i) = 0 → v 4 = 0 →
      v = (if v 1 = 0 then 0 else (delta first).val) +
        (if v 2 = 0 then 0 else (delta second).val) +
        (if v 3 = 0 then 0 else (delta (first * second)).val) := by decide
  apply Subtype.ext
  simpa only [Submodule.coe_add, Submodule.coe_zero, apply_ite Subtype.val] using h x.val x.property hx

/-- Two regular double transpositions generate the moved hyperplane. -/
theorem moved_le_of_differences (F : Subgroup (Multiplicative Space))
    (hF : ∀ a ∈ ({first, second, first * second} : Set Actor), ∀ x : Space,
      Multiplicative.ofAdd (act a x - x) ∈ F) : moved ≤ F := by
  intro x hx
  have hd (a : Actor) (ha : a ∈ ({first, second, first * second} : Set Actor)) :
      Multiplicative.ofAdd (delta a) ∈ F := hF a ha root
  have hi (c : ZMod 2) (v : Space) (hv : Multiplicative.ofAdd v ∈ F) :
      Multiplicative.ofAdd (if c = 0 then 0 else v) ∈ F := by
    split_ifs
    · exact F.one_mem
    · exact hv
  change Multiplicative.ofAdd x.toAdd ∈ F
  rw [moved_expansion x.toAdd ((mem_moved x).mp hx)]
  exact F.mul_mem (F.mul_mem (hi _ _ (hd first (by simp)))
    (hi _ _ (hd second (by simp)))) (hi _ _ (hd (first * second) (by simp)))

theorem difference_mem_moved (a : Actor) (ha : a.val 4 = 4) (x : Space) :
    Multiplicative.ofAdd (act a x - x) ∈ moved := by
  rw [mem_moved]
  change x.val (a.val.symm 4) - x.val 4 = 0
  rw [a.val.symm_apply_eq.mpr ha.symm, sub_self]

theorem moved_stabilizer (a : Actor)
    (ha : ∀ x ∈ moved, coordinateAut a x ∈ moved) : a.val 4 = 4 := by
  have h : ∀ i : Fin 5, (∀ v : Full (Fin 5), (∑ j, v j) = 0 → v 4 = 0 → v i = 0) → i = 4 := by decide
  have hi := h (a.val.symm 4) (fun v hv hv4 => (mem_moved _).mp
    (ha (Multiplicative.ofAdd ⟨v,hv⟩) ((mem_moved _).mpr hv4)))
  exact a.val.eq_symm_apply.mp hi.symm

theorem coordinateAut_conj (a b : Actor) (x : Space) :
    act a (act b x) = act (a * b * a⁻¹) (act a x) := by
  change (coreRepresentation (Fin 5) a.val)
      (coreRepresentation (Fin 5) b.val x) =
    (coreRepresentation (Fin 5) (a.val * b.val * a.val⁻¹))
      (coreRepresentation (Fin 5) a.val x)
  simp only [← Module.End.mul_apply, ← map_mul]
  simp only [inv_mul_cancel_right]

end BinaryPermutation.FiveMovedHyperplanes
