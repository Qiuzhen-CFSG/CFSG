module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.LocalData
public import Theory.Representation.BinaryLinearRecognition.OrthogonalEight
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# The elementary lower bound for faithful binary SL₄ modules

The actual matrix group has 20160 elements. A binary endomorphism algebra
in dimension at most three has at most 512 elements, so it cannot contain
the image of a faithful representation. This proves dimension at least four
without using irreducibility or a module classification.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
G.9.3(11)--(12), printed pp.354,356--357. The elementary root proofs adapt
the binary SL₅ highest-vector development in this repository to rank three.
-/

@[expose] public section

open Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

/-- Faithfulness alone excludes dimensions below four: the entire endomorphism
algebra of a binary space of dimension at most three has at most 512 elements. -/
theorem four_le_finrank_of_faithful
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) (hf : Function.Injective ρ) :
    4 ≤ Module.finrank (ZMod 2) V := by
  classical
  let e := (Module.finBasis (ZMod 2) (V →ₗ[ZMod 2] V)).equivFun
  let : Finite (V →ₗ[ZMod 2] V) := Finite.of_equiv _ e.symm.toEquiv
  have hc : Nat.card (V →ₗ[ZMod 2] V) =
      2 ^ (Module.finrank (ZMod 2) V * Module.finrank (ZMod 2) V) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin,
      Module.finrank_linearMap]
  have hle := Nat.card_le_card_of_injective ρ hf
  rw [Atlas.Order20160A8.sl4Two_card, hc] at hle
  by_contra h
  have hd : Module.finrank (ZMod 2) V ≤ 3 := by omega
  have hsq : Module.finrank (ZMod 2) V * Module.finrank (ZMod 2) V ≤ 9 :=
    Nat.mul_self_le_mul_self hd
  have hp : 2 ^ (Module.finrank (ZMod 2) V * Module.finrank (ZMod 2) V) ≤ 2 ^ 9 :=
    Nat.pow_le_pow_right (by decide) hsq
  norm_num at hp
  omega

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
