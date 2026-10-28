module
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationContracts

/-!
# Repacking and unit identities for the ATLAS local program

Base-five source rows are repacked in base 2048 without changing their
matrices over `ZMod 5`. Multiplication and a one-sided inverse identity
identify candidate rows with values of existing units.
Source: `../Atlas111Source/` and `../Atlas111OrderSource/`.
-/

namespace Lyons.RelationCertificate.Seed

@[expose] public def repackSource (a : Rows) : Rows :=
  fun i => pack 111 (fun j => a i / 5 ^ j.val % 5)

public theorem decode_repackSource (a : Rows) :
    decode (repackSource a) = fun i j => ((a i / 5 ^ j.val : ℕ) : ZMod 5) := by
  funext i j
  unfold decode repackSource
  rw [digit_pack]
  · simp only [ZMod.natCast_mod]
  · intro k
    exact (Nat.mod_lt _ (by decide : 0 < 5)).trans (by decide)

@[expose] public def identityRows : Rows :=
  fun i => pack 111 (fun j => if i = j then 1 else 0)

public theorem decode_identityRows : decode identityRows = 1 := by
  funext i j
  unfold decode identityRows
  rw [digit_pack]
  · by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · intro k
    split <;> decide

@[expose] public def checkRowsEq (a b : Rows) : Bool :=
  Atlas111Certificate.allBelow 111 fun i => a (Fin.ofNat 111 i) == b (Fin.ofNat 111 i)

public theorem rows_eq_of_check (a b : Rows) (h : checkRowsEq a b = true) : a = b := by
  funext i
  have hi := Atlas111Certificate.allBelow_sound h i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [he, beq_iff_eq] using hi

public theorem mul_value (u v : AtlasMatrixˣ) {x y z : Rows}
    (hx : decode x = ↑u) (hy : decode y = ↑v)
    (hm : decode x * decode y = decode z) : decode z = ↑(u * v) := by
  rw [← hm, hx, hy]
  rfl

public theorem inv_value (u : AtlasMatrixˣ) {x y : Rows}
    (hx : decode x = ↑u) (hm : decode x * decode y = 1) : decode y = ↑u⁻¹ := by
  rw [hx] at hm
  have h := congrArg (fun t : AtlasMatrix => (↑u⁻¹ : AtlasMatrix) * t) hm
  simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_one] using h

end Lyons.RelationCertificate.Seed
