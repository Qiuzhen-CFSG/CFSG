module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.ThirdExclusion.Model
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.ThirdExclusion.SquareRootFusion

/-!
# Characteristic involutions in the third model's involution centralizers

The center of the certified order-128 group consists of the identity and
`modelZ`. For each other involution `t`, square-root counts distinguish
`modelZ` from every other nonidentity central involution of `C(t)`.

The calculation is exhaustive over the certified indices, using only their
checked multiplication table. In particular it also handles the abelian
order-sixteen centralizer and the order-64 centralizer whose derived center
has order four. These are the two cases not covered by a derived-center line.
The general automorphism and ambient-fusion implications are proved in
`SquareRootFusion`.

Source of the exclusion problem: Huppert--Blackburn III, XII.1.18(b), p.314.
The finite coordinates are independently generated in `source/generate.py`.
-/

namespace Theory.GroupTheory.HeldM22A10.ThirdExclusion
open Subgroup

set_option maxRecDepth 100000

@[expose] public def modelZ : Model := Tables.z

public theorem modelZ_ne_one : modelZ ≠ 1 := by decide +kernel

public theorem modelZ_square : modelZ * modelZ = 1 := by decide +kernel

public theorem modelZ_mem_center : modelZ ∈ center Model := by
  apply mem_center_iff.mpr
  exact (show ∀ x, Tables.product x Tables.z = Tables.product Tables.z x by decide +kernel)

public theorem model_center (w : Model) (hw : w ∈ center Model) : w = 1 ∨ w = modelZ := by
  have h : ∀ w : Fin 128, (∀ x : Fin 128, Tables.product x w = Tables.product w x) →
      w = 0 ∨ w = Tables.z := by decide +kernel
  exact h w (mem_center_iff.mp hw)

private def count (t w : Fin 128) : ℕ :=
  (Finset.univ.filter (fun x : Fin 128 =>
    Tables.product x t = Tables.product t x ∧ Tables.product x x = w)).card

private theorem squareRootCount_model (t w : Model) : squareRootCount t w = count t w := by
  unfold squareRootCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 1000000 in
private theorem rigid_table : ∀ t w : Fin 128,
    Tables.product t t = 0 → t ≠ 0 → t ≠ Tables.z →
    w ≠ 0 → Tables.product w w = 0 →
    (∀ x : Fin 128, Tables.product x t = Tables.product t x →
      Tables.product w x = Tables.product x w) →
    count t w = count t Tables.z → w = Tables.z := by
  decide +kernel

/-- Among the central involutions of each noncentral involution centralizer,
its number of square roots singles out `modelZ`. -/
public theorem model_rigidity (t : Model) (ht : t * t = 1) (ht1 : t ≠ 1) (htz : t ≠ modelZ)
    (w : Model) (hw1 : w ≠ 1) (hw : w * w = 1)
    (hc : ∀ x : Model, x * t = t * x → w * x = x * w)
    (hn : squareRootCount t w = squareRootCount t modelZ) : w = modelZ := by
  rw [squareRootCount_model, squareRootCount_model] at hn
  exact rigid_table t w ht ht1 htz hw1 hw hc hn

end Theory.GroupTheory.HeldM22A10.ThirdExclusion
