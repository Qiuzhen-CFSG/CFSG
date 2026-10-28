module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.BinaryModels.Comparison
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Quotient
/-!
# The J₂ order obstruction in the binary comparison

A checked list of words in the actual degree-100 ATLAS generators sends
point zero to every point. Orbit–stabilizer therefore makes 100 divide
the carrier's order, which is impossible for either binary PSL model.
This proves only the needed separation; no J₂ order or simplicity
classification is assumed.

The words are reconstructed by the adjacent generator script from the
already checked tables in `J2.GeneratorPair`. Their action on every point
is checked by Lean's kernel. The actual generators and their attribution
are inherited from ATLAS representation J2G1-p100B0, with the established
conversion from right to left actions.

Source use: Aschbacher–Smith, combined manuscript (1 March 2004),
1.1.5(3)(f), printed pp.501–503; proof of 15.4.20, printed p.1164.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.BinaryModels
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair

private def orbitWords : Fin 100 → List Bool :=
  ![[],
    [true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, false, true, true],
    [false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, true, false, true, true],
    [false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, true, false, true, true, false, true, false, true],
    [true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, true, false, true, false, true, true, false, true, false, true],
    [false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true],
    [false, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, true, false, true, false, true],
    [false, true, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, true, false, true, true],
    [false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, true, false, true, true],
    [true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, false, true, true],
    [false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, false, true, false, true, true],
    [false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true],
    [false, true, true, false, true],
    [true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true],
    [true, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, true, false, true, false, true, true, false, true, true],
    [true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [true, true, false, true, false, true, true, false, true, true],
    [false, true, false, true, false, true, true, false, true, false, true, true, false, true, true],
    [false, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, true],
    [true, false, true, false, true, true, false, true, false, true, true, false, true, true],
    [true, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, false, true],
    [false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, false, true],
    [false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, true, false, true, false, true, true, false, true, false, true, true, false, true, true],
    [true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, true, false, true, false, true, true, false, true, true],
    [true, true, false, true, false, true],
    [false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, true, false, true, false, true],
    [true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, true],
    [true, true],
    [false, true, false, true],
    [true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, true],
    [false],
    [false, true],
    [false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [true, true, false, true],
    [true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, false, true, false, true, true],
    [true, false, true, false, true, true, false, true, false, true],
    [true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, false, true, true, false, true, true],
    [false, true, true, false, true, false, true, true, false, true, true],
    [true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true],
    [true, false, true, true, false, true, false, true],
    [false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [true, true, false, true, true]]

private def evalTable : List Bool → Equiv.Perm (Fin 100)
  | [] => 1
  | x :: xs => (if x then tableB else tableA) * evalTable xs

private def evalCarrier : List Bool → Carrier
  | [] => 1
  | x :: xs => (if x then b else a) * evalCarrier xs

private theorem evalCarrier_coe (w : List Bool) :
    (evalCarrier w : Equiv.Perm (Fin 100)) = evalTable w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    cases x
    · change generatorA * (evalCarrier xs : Equiv.Perm (Fin 100)) = tableA * evalTable xs
      rw [generatorA_eq_table, ih]
    · change generatorB * (evalCarrier xs : Equiv.Perm (Fin 100)) = tableB * evalTable xs
      rw [generatorB_eq_table, ih]

set_option maxRecDepth 100000 in
private theorem orbitWords_checked : ∀ i : Fin 100, evalTable (orbitWords i) 0 = i := by
  decide +kernel

/-- The actual degree-100 carrier has a transitive orbit, so 100 divides its order. -/
private theorem j2_hundred_dvd_card : 100 ∣ Nat.card Carrier := by
  have he : MulAction.orbit Carrier (0 : Fin 100) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    refine ⟨evalCarrier (orbitWords i), ?_⟩
    change (evalCarrier (orbitWords i) : Equiv.Perm (Fin 100)) 0 = i
    rw [evalCarrier_coe]
    exact orbitWords_checked i
  have hd := (MulAction.stabilizer Carrier (0 : Fin 100)).index_dvd_card
  rw [MulAction.index_stabilizer, he, Set.ncard_univ, Nat.card_fin] at hd
  exact hd

/-- The concrete J₂ carrier is neither binary PSL model. -/
theorem j2_separation {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL Carrier n 2) : False := by
  have hd := j2_hundred_dvd_card
  rw [binary_card hn hm] at hd
  rcases hn with rfl | rfl <;> norm_num at hd

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.BinaryModels
