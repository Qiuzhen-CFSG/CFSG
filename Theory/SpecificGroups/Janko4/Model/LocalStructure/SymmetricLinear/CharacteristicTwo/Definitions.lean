module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# A normal-closure route to characteristic two in the literal max4 subgroup

Write `x,y` for the two outputs of `max4Program`. The subgroup used here is
the normal closure, inside the literal max4 carrier, of `(x*y²)^6`.
The eleven successive right conjugates belong to this normal closure by
construction. Its two-group property and the matrix centralizer calculation
are separate certificate obligations; these definitions assert neither.

The source application is Aschbacher–Smith, Theorem 0.1.2(5), printed p.4,
with condition E on pp.3–4 and 481–482. The actual word program and provenance
are retained in `SymmetricLinear/Model/source/J4G1-max4W1`.
-/

@[expose] public section

namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo

/-- The first literal ATLAS output, as an element of its generated subgroup. -/
def first : max4Subgroup :=
  ⟨(max4Program a b).1, Subgroup.subset_closure (Set.mem_insert _ _)⟩

/-- The second literal ATLAS output, in the same carrier. -/
def second : max4Subgroup :=
  ⟨(max4Program a b).2, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

/-- The word whose relative normal closure supplies the candidate two-subgroup. -/
def seed : max4Subgroup := (first * second ^ 2) ^ 6

/-- Normality is relative to max4, not to the ambient J₄ carrier. -/
def seedNormalClosure : Subgroup max4Subgroup := Subgroup.normalClosure {seed}

instance seedNormalClosure_normal : seedNormalClosure.Normal :=
  Subgroup.normalClosure_normal

theorem seed_mem_normalClosure : seed ∈ seedNormalClosure :=
  Subgroup.subset_normalClosure rfl

/-- The alternating right-conjugation sequence, beginning with the seed. -/
def seedConjugate : ℕ → max4Subgroup
  | 0 => seed
  | k + 1 =>
    let g := if k % 2 = 0 then first else second
    g⁻¹ * seedConjugate k * g

/-- Every term lies in the actual intrinsic normal closure. -/
theorem seedConjugate_mem_normalClosure (k : ℕ) : seedConjugate k ∈ seedNormalClosure := by
  induction k with
  | zero => exact seed_mem_normalClosure
  | succ k ih => exact seedNormalClosure_normal.conj_mem' _ ih _

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo
