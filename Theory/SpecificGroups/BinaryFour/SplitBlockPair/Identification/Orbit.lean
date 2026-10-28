module

public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Identification.Locals
public import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.NormNum

/-!
# The marked orbit of the compatible binary pair

Fifteen short words in the two cubics carry the marked vector to every
nonzero vector. Each word is an element of the literal joined subgroup;
only its action on the sixteen-vector space is checked by finite reduction.
The resulting orbit–stabilizer identity is used to count the marked
stabilizer once the independent A₇ identification has been established.
An order of 168 is not used as a substitute for a PSL₃(2) equivalence.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 14.4.4, printed p.1007.
-/

namespace BinaryFourSplitPair

private def b : joined := ⟨columnCubic, columnCubic_mem_joined⟩
private def c : joined := ⟨normalizingCubic, normalizingCubic_mem_joined⟩

private def pointMover : Fin 15 → joined := ![
  1, b, b*b, c*b, c*b*b, b*c*b, c*c*b, b*c*b*b,
  c*c*b*b, b*b*c*b, b*c*c*b, b*b*c*b*b, b*c*c*b*b,
  b*b*c*c*b, b*b*c*c*b*b]

public theorem point_ne_one : point ≠ (1 : E) := by decide +kernel

/-- The generated group is transitive on the fifteen nonzero vectors. -/
public theorem point_orbit : MulAction.orbit joined point = {v : E | v ≠ 1} := by
  ext v
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g,rfl⟩
    change g.val point ≠ 1
    simpa only [map_one] using (g.val.injective.ne_iff.mpr point_ne_one)
  · intro hv
    have h : ∀ v : E, v ≠ 1 → ∃ i : Fin 15, (pointMover i).val point = v := by
      decide +kernel
    obtain ⟨i, hi⟩ := h v hv
    exact ⟨pointMover i, hi⟩

public theorem point_orbit_card : Nat.card (MulAction.orbit joined point) = 15 := by
  rw [Nat.card_congr (Equiv.setCongr point_orbit), Nat.card_eq_fintype_card]
  decide +kernel

/-- The orbit–stabilizer identity for the literal marked evaluation action. -/
public theorem pointStabilizer_card_relation :
    15 * Nat.card (MulAction.stabilizer joined point) = Nat.card joined := by
  rw [← point_orbit_card, ← Nat.card_prod,
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup joined point)]

/-- The A₇ identification, once supplied, forces the actual stabilizer to have order 168.
This cardinality consequence alone is not a PSL₃(2) identification. -/
public theorem pointStabilizer_card_of_alternating
    (e : joined ≃* alternatingGroup (Fin 7)) :
    Nat.card (MulAction.stabilizer joined point) = 168 := by
  have h := pointStabilizer_card_relation
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at h
  norm_num [Nat.card_fin, Nat.factorial] at h
  change 15 * Nat.card (MulAction.stabilizer joined point) = 2520 at h
  omega

end BinaryFourSplitPair
