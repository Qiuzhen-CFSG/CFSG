module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.Enumeration

/-!
# Candidate fixed-mask bounds in stabilizer-chain coordinates

The table `weight` is data, not a theorem about fixed masks. Its intended value
is the number of row-coordinate masks fixed by the normal closure of an element,
unless that closure is not elementary abelian, when the value is zero. The
identity is assigned 2048. The separate normality certificate must prove that
these values bound the common fixed masks of each normal elementary subgroup
containing the element; no property of the discovery program is assumed.

The literal permutations and pair labels come from the ATLAS-derived tables
re-exported by `Enumeration`. `source/discover_weights.py` regenerates these
candidate values using those tables and the exact row-coordinate convention.
-/

@[expose] public section
namespace Janko4.LocalStructure.SylowCore.FiniteBoundCertificate

/-- Candidate upper bounds; their mathematical validity is a separate obligation. -/
def weightTable : Fin 16 → Fin 8 → Fin 8 → ℕ :=
  ![![![2048, 0, 0, 0, 0, 8, 2, 2],
      ![16, 0, 8, 0, 0, 0, 0, 0],
      ![2, 0, 0, 0, 0, 2, 32, 8],
      ![0, 0, 0, 8, 0, 0, 16, 0],
      ![0, 16, 0, 0, 0, 8, 0, 0],
      ![2, 0, 0, 0, 0, 2, 16, 8],
      ![0, 0, 0, 0, 16, 0, 0, 8],
      ![16, 0, 0, 0, 0, 8, 2, 2]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 64, 0],
      ![0, 8, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 8, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 64, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 64, 0, 0, 0, 0],
      ![8, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![16, 0, 8, 0, 0, 0, 0, 0],
      ![128, 0, 0, 0, 0, 8, 2, 2],
      ![0, 0, 0, 0, 8, 0, 16, 0],
      ![2, 0, 0, 0, 0, 2, 16, 8],
      ![0, 32, 8, 2, 2, 0, 0, 0],
      ![0, 0, 0, 8, 0, 0, 16, 0],
      ![0, 2, 2, 8, 16, 0, 0, 0],
      ![16, 8, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 8, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 64, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 64, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 8, 0, 0],
      ![0, 0, 0, 16, 0, 0, 0, 0],
      ![0, 0, 0, 16, 0, 0, 8, 0],
      ![0, 0, 8, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 8, 0, 0, 0],
      ![0, 0, 0, 0, 8, 0, 0, 16],
      ![0, 0, 8, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 8, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 64, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 8, 0, 0],
      ![0, 64, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 8],
      ![0, 0, 0, 0, 8, 0, 0, 0],
      ![16, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 16, 0, 0, 8, 0],
      ![0, 0, 0, 0, 0, 0, 8, 0],
      ![8, 16, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 8, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 64, 0, 0, 0]],
    ![![0, 0, 0, 0, 16, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 8],
      ![0, 0, 64, 0, 0, 0, 0, 0],
      ![8, 0, 16, 0, 0, 0, 0, 0],
      ![0, 0, 0, 8, 0, 0, 0, 0],
      ![0, 8, 0, 0, 0, 0, 0, 0],
      ![0, 8, 0, 0, 0, 16, 0, 0],
      ![0, 0, 0, 8, 0, 0, 0, 0]],
    ![![0, 0, 0, 8, 0, 0, 0, 0],
      ![0, 0, 0, 0, 16, 0, 8, 0],
      ![0, 8, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 8, 0, 0],
      ![0, 0, 0, 0, 8, 0, 16, 0],
      ![0, 0, 16, 0, 0, 0, 0, 0],
      ![0, 0, 8, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 64, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 8],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 64, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 8],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 64]],
    ![![2, 0, 0, 0, 0, 2, 8, 16],
      ![0, 0, 0, 8, 0, 0, 0, 0],
      ![8, 0, 0, 0, 0, 16, 2, 2],
      ![0, 0, 8, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 8],
      ![8, 0, 0, 0, 0, 32, 2, 2],
      ![0, 0, 0, 0, 0, 8, 0, 0],
      ![2, 0, 0, 0, 0, 2, 8, 64]],
    ![![0, 0, 0, 8, 0, 0, 0, 0],
      ![2, 0, 0, 0, 0, 2, 8, 16],
      ![0, 8, 0, 0, 0, 0, 0, 0],
      ![8, 0, 0, 0, 0, 32, 2, 2],
      ![0, 2, 2, 16, 8, 0, 0, 0],
      ![0, 0, 8, 0, 0, 0, 0, 0],
      ![0, 8, 64, 2, 2, 0, 0, 0],
      ![0, 0, 0, 0, 8, 0, 0, 0]]]

/-- The candidate bound assigned to an actual enumerated element. -/
def weight (i : Index) : ℕ := weightTable i.1 i.2.1 i.2.2

@[simp] theorem weight_identityIndex : weight identityIndex = 2048 := rfl

theorem weight_le_identityIndex (i : Index) : weight i ≤ weight identityIndex := by
  have h : ∀ a b c, weightTable a b c ≤ 2048 := by decide +kernel
  exact h i.1 i.2.1 i.2.2

end Janko4.LocalStructure.SylowCore.FiniteBoundCertificate
