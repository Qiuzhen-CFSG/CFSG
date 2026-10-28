module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.HeckeAction.Basic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.HeckeAction.Relations
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.HeckeAction.FixedSpace

/-!
# The type-A₃ zero-Hecke action on binary upper-fixed vectors

Restricting the three root operators gives idempotent endomorphisms satisfying
the type-A₃ commutation and braid relations. The upper-fixed subspace is
nonzero. These facts supply the input to the common-eigenvector construction.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
G.9.3(11)--(12), printed pp.354,356--357. The elementary root proofs adapt
the binary SL₅ highest-vector development in this repository to rank three.
-/

@[expose] public section

open Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.HeckeAction

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The simple zero-Hecke endomorphism of the upper-fixed subspace. -/
def restrictedOperator (ρ : Representation (ZMod 2) Group V) (i : Fin 3) :
    Module.End (ZMod 2) (upperFixedSubmodule ρ) where
  toFun v := ⟨operator ρ i v, operator_upperFixed ρ i v.property⟩
  map_add' v w := Subtype.ext ((operator ρ i).map_add v w)
  map_smul' c v := Subtype.ext ((operator ρ i).map_smul c v)

/-- Restriction agrees with the original root operator in the ambient module. -/
@[simp] theorem restrictedOperator_coe_apply (ρ : Representation (ZMod 2) Group V)
    (i : Fin 3) (v : upperFixedSubmodule ρ) :
    (restrictedOperator ρ i v : V) = operator ρ i v := rfl

/-- Each restricted simple operator is idempotent. -/
theorem restrictedOperator_idempotent (ρ : Representation (ZMod 2) Group V)
    (i : Fin 3) (v : upperFixedSubmodule ρ) :
    restrictedOperator ρ i (restrictedOperator ρ i v) = restrictedOperator ρ i v := by
  exact Subtype.ext (operator_idempotent ρ i v.property)

/-- The quadratic zero-Hecke relation, as an identity of endomorphisms. -/
theorem restrictedOperator_sq (ρ : Representation (ZMod 2) Group V)
    (i : Fin 3) : restrictedOperator ρ i * restrictedOperator ρ i =
      restrictedOperator ρ i := by
  ext v
  exact congrArg Subtype.val (restrictedOperator_idempotent ρ i v)

/-- Simple operators at nonadjacent roots commute on the upper-fixed subspace. -/
theorem restrictedOperator_commute (ρ : Representation (ZMod 2) Group V)
    (i j : Fin 3) (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Commute (restrictedOperator ρ i) (restrictedOperator ρ j) := by
  apply LinearMap.ext
  intro v
  exact Subtype.ext (congrArg (fun f : Module.End (ZMod 2) V => f v)
    (operator_commute ρ i j hij).eq)

/-- The adjacent braid relation, as an identity of endomorphisms. -/
theorem restrictedOperator_braid (ρ : Representation (ZMod 2) Group V)
    (i j : Fin 3) (hij : i.val + 1 = j.val) :
    restrictedOperator ρ i * restrictedOperator ρ j * restrictedOperator ρ i =
      restrictedOperator ρ j * restrictedOperator ρ i * restrictedOperator ρ j := by
  apply LinearMap.ext
  intro v
  exact Subtype.ext (operator_braid ρ i j hij v)

/-- Eigenvalue zero on the fixed subspace is the inactive-root alternative. -/
theorem restrictedOperator_eq_zero_iff (ρ : Representation (ZMod 2) Group V)
    (i : Fin 3) (v : upperFixedSubmodule ρ) :
    restrictedOperator ρ i v = 0 ↔ ρ (simpleSwap i) (v : V) = v := by
  rw [← operator_eq_zero_iff ρ i v.property]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- Eigenvalue one on the fixed subspace is the active-root alternative. -/
theorem restrictedOperator_eq_self_iff (ρ : Representation (ZMod 2) Group V)
    (i : Fin 3) (v : upperFixedSubmodule ρ) :
    restrictedOperator ρ i v = v ↔
      (v : V) + ρ (simpleSwap i) v + ρ (simpleLower i) v = 0 := by
  rw [← operator_eq_self_iff ρ i v.property]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- Nontriviality needed to apply a common-eigenvector theorem to the action. -/
theorem upperFixedSubmodule_nontrivial [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (ρ : Representation (ZMod 2) Group V) : Nontrivial (upperFixedSubmodule ρ) := by
  obtain ⟨v, hv, hfix⟩ := exists_nonzero_upperFixed ρ
  exact ⟨⟨⟨v, hfix⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.HeckeAction
