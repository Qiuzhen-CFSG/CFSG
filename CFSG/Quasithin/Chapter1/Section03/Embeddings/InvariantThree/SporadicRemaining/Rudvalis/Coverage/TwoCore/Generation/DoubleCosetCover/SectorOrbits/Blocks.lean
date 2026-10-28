module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.DoubleCosetCover.SectorOrbits.Certificate

/-!
# Bounded checks for the Rudvalis finite-family certificate

A block checks 256 row addresses, ignoring addresses beyond the finite family.
The final seven unused blocks therefore assert nothing. The soundness lemma
extracts the two required checks for every actual row from 52 groups of 32 blocks.
The tables and mathematical meaning of each check are in `Certificate`.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover.SectorOrbitCertificate

/-- Check both required identities at every valid address in one block. -/
@[expose] public def checkBlock (block : Nat) : Bool :=
  OrderCertificate.checkFin (fun offset : Fin 256 =>
    let i := block * 256 + offset.val
    if i < 424125 then closureCheck i && forestCheck i else true)

/-- The block boundaries exhaust the finite witness table. -/
public theorem checks_of_blocks
    (h : ∀ g : Fin 52, ∀ b : Fin 32, checkBlock (32 * g.val + b.val) = true) :
    (∀ i : Fin 424125, closureCheck i.val = true) ∧
      (∀ i : Fin 424125, forestCheck i.val = true) := by
  have each (i : Fin 424125) : closureCheck i.val = true ∧ forestCheck i.val = true := by
    let k := i.val / 256
    let g : Fin 52 := ⟨k / 32, by dsimp [k]; omega⟩
    let b : Fin 32 := ⟨k % 32, Nat.mod_lt _ (by decide)⟩
    let r : Fin 256 := ⟨i.val % 256, Nat.mod_lt _ (by decide)⟩
    have hk : 32 * g.val + b.val = k := by dsimp [g, b]; omega
    have hi : k * 256 + r.val = i.val := by dsimp [k, r]; omega
    have hh := h g b
    rw [hk, checkBlock] at hh
    have hr := (OrderCertificate.checkFin_spec _).mp hh r
    dsimp only at hr
    rw [hi, if_pos i.isLt, Bool.and_eq_true] at hr
    exact hr
  exact ⟨fun i => (each i).1, fun i => (each i).2⟩

end Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover.SectorOrbitCertificate
