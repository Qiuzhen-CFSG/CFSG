module

public import Theory.SpecificGroups.ONan.E9A4.Data

/-!
# Scalar-aware GF(7) multiplication certificates

The E₉ × A₄ transitions hold up to the scalar on their right-hand side.
This extension of the seven-subgroup checker identifies natural-number dot
products with those matrix identities. Each later certificate is reduced
by the kernel. Matrix data and attribution: `../source/README.md`.
-/

open ONan.Simplicity.Seven.Certificate
namespace ONan.E9A4.MatrixTable

@[expose] public def checkScaled (a b c s : ℕ) : Bool :=
  checkAll (fun i => checkAll (fun j =>
    dotNat (entryNat a i) (fun k => entryNat b k j) 45 % 7 ==
      (s * entryNat c i j) % 7) 45) 45

public theorem checkScaled_sound (a b c s : ℕ) (h : checkScaled a b c s = true) :
    decodeMatrix a * decodeMatrix b = (s : ZMod 7) • decodeMatrix c := by
  apply Matrix.ext
  intro i j
  have hij := (checkAll_spec _ _).mp ((checkAll_spec _ _).mp h i.val i.isLt) j.val j.isLt
  have hn := beq_iff_eq.mp hij
  have hc := congrArg (fun n : ℕ => (n : ZMod 7)) hn
  simp only [ZMod.natCast_mod, Nat.cast_mul] at hc
  change (∑ k : Fin 45, (entryNat a i.val k.val : ZMod 7) *
    (entryNat b k.val j.val : ZMod 7)) = _
  rw [← dotNat_cast (entryNat a i.val) (fun k => entryNat b k j.val) 45]
  exact hc

end ONan.E9A4.MatrixTable
