module

import Mathlib.Tactic.FinCases
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarData
public import Theory.Mathieu.M24.Properties.Order

/-!
# Embedding the star group into the Witt-design automorphism group

The relabeling comes from the saved star exploration in workspace
`987246d9ba5a4fa9b3c370d659f2837b/Scratch/J4LocalOrder/README.md`.
ATLAS label 24 is Lean point zero. GAP supplies words only; Lean checks the
permutation identities and derives membership using the proved standard
generator membership theorems. This gives a concrete representation embedding,
without assuming that those standard generators generate all of M24.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

@[expose] public section
namespace Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
open Theory.GroupTheory

open Sporadic.Mathieu

def atlas0 : Equiv.Perm (Fin 24) where
  toFun := ![20, 4, 7, 17, 1, 13, 9, 2, 15, 6, 19, 18, 21, 5, 16, 8, 14, 3, 11, 10, 0, 12, 23, 22]
  invFun := ![20, 4, 7, 17, 1, 13, 9, 2, 15, 6, 19, 18, 21, 5, 16, 8, 14, 3, 11, 10, 0, 12, 23, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def atlas1 : Equiv.Perm (Fin 24) where
  toFun := ![23, 4, 21, 9, 6, 18, 1, 7, 8, 15, 5, 11, 12, 17, 2, 3, 13, 16, 10, 0, 20, 14, 22, 19]
  invFun := ![19, 6, 14, 15, 1, 10, 4, 7, 8, 3, 18, 11, 12, 16, 21, 9, 17, 13, 5, 23, 20, 2, 22, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def atlasGen : Fin 4 → Equiv.Perm (Fin 24) :=
  ![atlas0, atlas1, atlas0⁻¹, atlas1⁻¹]

theorem atlasGen_eq : atlasGen =
    ![m24GeneratorA, m24GeneratorB, m24GeneratorA⁻¹, m24GeneratorB⁻¹] := by
  decide +kernel

theorem atlasGen_mem : ∀ i, atlasGen i ∈ M24 := by
  intro i
  rw [atlasGen_eq]
  fin_cases i
  · exact m24GeneratorA_mem
  · exact m24GeneratorB_mem
  · exact M24.inv_mem m24GeneratorA_mem
  · exact M24.inv_mem m24GeneratorB_mem

def relabel : Equiv.Perm (Fin 24) where
  toFun := ![1, 14, 13, 7, 17, 23, 18, 9, 12, 21, 10, 19, 8, 0, 6, 4, 22, 15, 3, 2, 20, 5, 16, 11]
  invFun := ![13, 0, 19, 18, 15, 21, 14, 3, 12, 7, 10, 23, 8, 2, 1, 17, 22, 4, 6, 11, 20, 9, 16, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def atlasWordX : List (Fin 4) :=
  [3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3]

theorem relabel_starX : MulAut.conj relabel starX = Theory.GroupTheory.evalWord atlasGen atlasWordX := by
  decide +kernel

def atlasWordY : List (Fin 4) :=
  [2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 1, 0, 3, 0, 1]

theorem relabel_starY : MulAut.conj relabel starY = Theory.GroupTheory.evalWord atlasGen atlasWordY := by
  decide +kernel

theorem conjugate_mem (g : StarGroup) : MulAut.conj relabel g.val ∈ M24 := by
  have hle : StarGroup ≤ M24.comap (MulAut.conj relabel).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases (show x = starX ∨ x = starY from by simpa using hx) with rfl | rfl
    · change MulAut.conj relabel starX ∈ M24
      rw [relabel_starX]
      exact word_mem _ _ atlasGen_mem _
    · change MulAut.conj relabel starY ∈ M24
      rw [relabel_starY]
      exact word_mem _ _ atlasGen_mem _
  exact hle g.property

/-- The explicit relabeling embeds the concrete star permutation group in M24. -/
def starToM24 : StarGroup →* M24 where
  toFun g := ⟨MulAut.conj relabel g.val, conjugate_mem g⟩
  map_one' := Subtype.ext (map_one (MulAut.conj relabel))
  map_mul' g h := Subtype.ext (map_mul (MulAut.conj relabel) g.val h.val)

theorem starToM24_injective : Function.Injective starToM24 := by
  intro g h heq
  apply Subtype.ext
  exact (MulAut.conj relabel).injective (congrArg Subtype.val heq)

theorem starGroup_card_le : Nat.card StarGroup ≤ 244823040 := by
  rw [← m24_order]
  exact Nat.card_le_card_of_injective starToM24 starToM24_injective

end Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
