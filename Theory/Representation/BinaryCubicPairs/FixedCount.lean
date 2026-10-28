module

public import Theory.Representation.BinaryCubicPairs.Certificate
public import Mathlib.Data.BitVec
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

/-!
# Fixed-space cardinality and the finite cubic predicate

The Boolean fixed-vector count is exactly the cardinality of the ordinary
linear kernel. Rank-nullity therefore supplies the certificate's rank-two
predicate from a genuine four-dimensional representation. This is a
coordinate conversion, not an added module hypothesis.

Source application: Aschbacher--Smith E.6.24, printed p.255.
-/

public section
namespace BinaryCubicPairs
open Packed

local instance : Fintype (BitVec 4) :=
  Fintype.ofEquiv (Fin 16) (BitVec.equivFin (m := 4)).toEquiv.symm

private def vectors : List (BitVec 4) := (List.range 16).map (BitVec.ofNat 4)

private theorem vectors_nodup : vectors.Nodup := by decide +kernel

private theorem vectors_toFinset : vectors.toFinset = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨x.toNat, List.mem_range.mpr x.isLt, by simp⟩

private theorem count_eq_card (f : BitVec 4 → Bool) :
    (List.range 16).countP (fun n => f (BitVec.ofNat 4 n)) =
      Nat.card {x : BitVec 4 // f x = true} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← vectors_toFinset, vectors_nodup.card_eq_countP]
  simp only [vectors, List.countP_map, Bool.decide_coe]
  rfl

@[expose] def fixedKernel (M : CoordinateMatrix) : Submodule (ZMod 2) CoordinateVector :=
  (M.mulVecLin - LinearMap.id).ker

/-- The packed fixed-vector count is the cardinality of the actual kernel. -/
theorem fixed_count_eq (m : BitVec 16) :
    (List.range 16).countP (fun z => mv m (BitVec.ofNat 4 z) == BitVec.ofNat 4 z) =
      Nat.card (fixedKernel (toMat m)) := by
  rw [count_eq_card (fun x => mv m x == x)]
  let f : {x : BitVec 4 // (mv m x == x) = true} → fixedKernel (toMat m) := fun x =>
    ⟨toVec x, by
      change (toMat m).mulVec (toVec x) - toVec x = 0
      rw [← toVec_mv, beq_iff_eq.mp x.property, sub_self]⟩
  apply Nat.card_congr (Equiv.ofBijective f ?_)
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact toVec_injective (congrArg Subtype.val hxy)
  · intro x
    obtain ⟨z, hz⟩ := toVec_surjective x.val
    have hfix : mv m z = z := by
      apply toVec_injective
      rw [toVec_mv, hz]
      exact sub_eq_zero.mp x.property
    exact ⟨⟨z, beq_iff_eq.mpr hfix⟩, Subtype.ext hz⟩

/-- A two-dimensional fixed kernel gives the literal four-vector count. -/
theorem fixed_count_four (m : BitVec 16)
    (h : Module.finrank (ZMod 2) (fixedKernel (toMat m)) = 2) :
    (List.range 16).countP (fun z => mv m (BitVec.ofNat 4 z) == BitVec.ofNat 4 z) = 4 := by
  rw [fixed_count_eq, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, h]
  norm_num

end BinaryCubicPairs
