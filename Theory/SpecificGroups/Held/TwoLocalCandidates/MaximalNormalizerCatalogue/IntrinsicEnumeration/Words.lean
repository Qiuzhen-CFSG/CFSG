module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords

/-!
# Binary word candidates for the intrinsic Held enumeration

The ten words below are the polycyclic sequence discovered for the fixed
four-generator representative. A binary index evaluates their product in the
original order, with the first word corresponding to the least significant bit.
All evaluations belong to the actual representative by construction. Surjectivity
and the finite extension checks are separate proof obligations; these definitions
do not assert that the words form a polycyclic sequence.

The enumeration starts at the trivial subgroup and uses the unchanged 22 literal
entries. Adjoining a binary word therefore gives a finite family of concrete
subgroups, suitable for the normal-index-two induction in `NormalSteps`.

Source: the retained `pc.g` discovery data for
`Held.LocalPairs.SylowGeometry.Calculations.representative`, reproduced in
`source/pc_words.json`. The ATLAS permutations are already inverted in Lean;
the order of the letters and of the ten factors is preserved.
-/

@[expose] public section

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
open LocalPairs.SylowGeometry.Calculations

/-- Literal words in the four published representative generators. -/
def pcWord : Fin 10 → List ℤ
  | 0 => [4]
  | 1 => [-3]
  | 2 => [-4, 2, 4]
  | 3 => [-2]
  | 4 => [-3, -4, -1, 2, 1, 2, -4, -2, -1, -3, -2]
  | 5 => [-4, 2, 1, 2, 4]
  | 6 => [-2, -1, -2]
  | 7 => [-4, -4, -1]
  | 8 => [-1]
  | _ => [-3, 2, 1, 2, 3, -2, -1, -2]

/-- A product of the ten actual words, in their published order. -/
def normalForm (n : Fin 1024) : representative :=
  ((List.finRange 10).map (fun i => word (pcWord i) ^ (n.val / 2 ^ i.val % 2))).prod

/-- The 22 entries with the trivial subgroup added as the initial state. -/
def node : Option (Fin 22) → Subgroup representative
  | none => ⊥
  | some j => entry j

/-- The actual subgroup obtained by adjoining one specified word. -/
def extension (i : Option (Fin 22)) (n : Fin 1024) : Subgroup representative :=
  node i ⊔ Subgroup.zpowers (normalForm n)

@[simp] theorem node_none : node none = ⊥ := rfl

@[simp] theorem node_some (j : Fin 22) : node (some j) = entry j := rfl

/-- Every finite extension contains its new element. -/
theorem normalForm_mem_extension (i : Option (Fin 22)) (n : Fin 1024) :
    normalForm n ∈ extension i n :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

/-- Every finite extension contains its starting subgroup. -/
theorem node_le_extension (i : Option (Fin 22)) (n : Fin 1024) :
    node i ≤ extension i n := le_sup_left

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
