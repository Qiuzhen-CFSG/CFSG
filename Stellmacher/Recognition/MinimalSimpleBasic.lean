module

public import Theory.GroupTheory.MinimalSimple
public import Stellmacher.Recognition.NGroup
public import Stellmacher.Recognition.SimpleInputs

/-!
# Local inputs for minimal simple groups

Every finite minimal simple group satisfies Thompson's all-prime N condition.
A nontrivial p-subgroup is nilpotent and solvable. Its normalizer is proper:
otherwise it is normal, and simplicity makes it the whole nonsolvable group.
The defining proper-subgroup condition now makes the normalizer solvable.

Specialization to the prime two gives Stellmacher's N2 condition. The existing
simple-group input theorem supplies even order and trivial two-core and odd
core, using the proved Feit--Thompson odd-order theorem. These are inputs to
local classification, without any claim of global recognition.

Source: GLS1 §28, definition of minimal simple and the N condition, and the
simple-group reductions in Stellmacher.Recognition.SimpleInputs.
-/

namespace IsMinimalSimple

variable {G : Type*} [Group G] [Finite G]

/-- Minimal simple groups have solvable normalizers of nontrivial p-subgroups. -/
public theorem isNGroup (hG : IsMinimalSimple G) : Stellmacher.IsNGroup G := by
  intro p hp Q hQ hQp
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Group.IsNilpotent Q := hQp.isNilpotent
  exact hG.solvable_of_lt _ (hG.normalizer_lt_top Q hQ inferInstance)

/-- In particular, every two-local subgroup is solvable. -/
public theorem isNTwoGroup (hG : IsMinimalSimple G) : Stellmacher.IsNTwoGroup G :=
  Stellmacher.isNTwoGroup_of_isNGroup hG.isNGroup

/-- Minimal simplicity supplies the order and core assumptions of the local theorem. -/
public theorem local_inputs (hG : IsMinimalSimple G) :
    Even (Nat.card G) ∧ pCore 2 G = ⊥ ∧ pPrimeCore 2 G = ⊥ := by
  let _ := hG.isSimpleGroup
  exact Stellmacher.Recognition.simple_nonsolvable_inputs hG.not_isSolvable

end IsMinimalSimple
