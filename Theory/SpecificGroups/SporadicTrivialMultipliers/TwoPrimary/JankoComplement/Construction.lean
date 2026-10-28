module
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoComplement.CoreCoordinates
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoComplement.Transport
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoComplement.Linear

/-!
# Conjugation matrices in the constructed core-preimage coordinates

Conjugation acts additively on the elementary preimage and fixes its central
kernel pointwise. The quotient part is exactly the certified right-conjugation
matrix on the literal core. Thus the constructed coordinates produce the two
arbitrary lower rows covered by the finite certificate. This discharges the
coordinate-data premise of the normal-complement transport.

Source: ATLAS `J4G1-max1W1` through the certified core action;
Aschbacher–Smith I.1.5, printed p.408, and GLS3 Section 6.1.
-/

@[expose] public section
namespace Janko4.TwoPrimary.InvariantComplement
open Subgroup Cardinality
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup

/-- Conjugation in arbitrary precoordinates fixes the central line and has the
certified quotient blocks. Its remaining entries are precisely two lower rows. -/
theorem exists_liftCoordinates {L : Type*} [Group L]
    (q : L →* Local) (hc : q.ker ≤ center L)
    (a b : L) (ha : q a = x) (hb : q b = y) (z : q.ker)
    (c : PreCoordinates q z) :
    ∃ d : Fin 22 → Bool, Nonempty (LiftCoordinates q a b z d) := by
  let N := Core.comap q
  let α (s : Bool) : MulAut N := MulAut.conjNormal (if s then b else a)⁻¹
  let F (s : Bool) (w : V × Bool) : V × Bool := c.equiv (α s (c.equiv.symm w))
  have h0 (s : Bool) : F s (0, false) = (0, false) := by
    change c.equiv (α s (c.equiv.symm (0, false))) = _
    rw [← c.map_one, c.equiv.symm_apply_apply, _root_.map_one]
  have hadd (s : Bool) (u v : V × Bool) :
      F s (u.1 ^^^ v.1, u.2 + v.2) =
        ((F s u).1 ^^^ (F s v).1, (F s u).2 + (F s v).2) := by
    obtain ⟨n, rfl⟩ := c.equiv.surjective u
    obtain ⟨m, rfl⟩ := c.equiv.surjective v
    simp only [F, ← c.map_mul, c.equiv.symm_apply_apply, _root_.map_mul]
  let zN : N := ⟨z.val, by change q z.val ∈ Core; rw [z.property]; exact Core.one_mem⟩
  have hz (s : Bool) : F s (0, true) = (0, true) := by
    have hfix : α s zN = zN := by
      apply Subtype.ext
      change (if s then b else a)⁻¹ * z.val * ((if s then b else a)⁻¹)⁻¹ = z.val
      rw [mem_center_iff.mp (hc z.property) (if s then b else a)⁻¹,
        mul_inv_cancel_right]
    change c.equiv (α s (c.equiv.symm (0, true))) = _
    rw [← c.map_central, c.equiv.symm_apply_apply]
    change c.equiv (α s zN) = c.equiv zN
    rw [hfix]
  have hquot (s : Bool) (w : V × Bool) : (F s w).1 = quotientStep s w.1 := by
    obtain ⟨n, rfl⟩ := c.equiv.surjective w
    simp only [F, c.equiv.symm_apply_apply]
    apply coreEval_injective
    apply Subtype.ext
    rw [c.map_projection, coreEval_step, c.map_projection]
    change q ((if s then b else a)⁻¹ * n.val * ((if s then b else a)⁻¹)⁻¹) = _
    simp only [_root_.map_mul, _root_.map_inv, inv_inv]
    cases s <;> simp [ha, hb]
  obtain ⟨d, hd⟩ := exists_lowerRows F h0 hadd hz hquot
  refine ⟨d, ⟨{
    equiv := c.equiv
    map_one := c.map_one
    map_mul := c.map_mul
    map_central := c.map_central
    map_conj_x := ?_
    map_conj_y := ?_ }⟩⟩
  · intro n
    simpa [F, α] using hd false (c.equiv n)
  · intro n
    simpa [F, α] using hd true (c.equiv n)

end Janko4.TwoPrimary.InvariantComplement
