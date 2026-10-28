module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FixedTorus

/-!
# Assembly of the Ree block-parameter calculation

An automorphism preserving the unipotent pair and each signed simple block
has one entrywise coefficient-field action after an inner adjustment.
`FieldRecovery` derives the additive parameter maps, scaled multiplication,
and compatibility of the type VI and nonabelian type V blocks from their
group relations. Its resulting torus characters respect the exact unequal
root powers in `LocalBlockInput.twist_root`. `FixedTorus` realizes the inverse
diagonal matrix by an actual element of the fixed group using coroot words.
The theorem `exists_simpleBlock_entries` combines these results with the
same torus parameters and cancels the inner adjustment.

Simple-block preservation remains an explicit hypothesis. Its recognition
from the unipotent pair, and generation by the fixed blocks, belong to the
pair-rigidity assembly; no field-action or torus-realization premise remains.

Source: GLS3, Table 2.4, §2.4, 2.5.1(b,c), and 2.5.12, in
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters

open Theory.AlgebraicGroup
variable {m : ℕ}

/-- Combine a recovered torus–field action with actual fixed-group realization.
The block-parameter theorem's owner must discharge both inputs. -/
theorem exists_simpleBlock_entries_of_torus_inputs (d : LocalBlockInput m)
    (a : MulAut d.fixedGroup)
    (hfield : ∃ (u : TorusParameters m)
      (σ : CoefficientField m ≃+* CoefficientField m),
      TwistCompatible u ∧ HasTorusFieldAction d a u σ)
    (hrealize : ∀ u : TorusParameters m, TwistCompatible u →
      ∃ g : d.fixedGroup, g.val.val = (torusMatrix u)⁻¹) :
    ∃ (g : d.fixedGroup) (σ : CoefficientField m ≃+* CoefficientField m),
      ∀ s positive, ∀ x ∈ simpleBlock d s positive,
        ∀ i j : F4Chevalley.BasisIndex,
          ((((MulAut.conj g)⁻¹ * a) x).val.val : MatrixCarrier m) i j =
            σ ((x.val.val : MatrixCarrier m) i j) := by
  obtain ⟨u, σ, hu, ha⟩ := hfield
  obtain ⟨g, hg⟩ := hrealize u hu
  exact ⟨g, σ, entries_of_torus_realization d a u σ ha g hg⟩

/-- A pair- and block-preserving automorphism has a common entrywise field
action on all four signed simple blocks after conjugation by an actual
fixed-group element. Both parameter recovery and torus realization are
discharged; block preservation remains the caller's explicit input. -/
theorem exists_simpleBlock_entries (hm : 1 ≤ m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (hindex : Odd (LargeLocalSeeds.standardUnipotent d).index)
    (a : MulAut d.fixedGroup) (hp : d.PreservesUnipotentPair a)
    (hb : PreservesSimpleBlocks d a) :
    ∃ (g : d.fixedGroup) (σ : CoefficientField m ≃+* CoefficientField m),
      ∀ s positive, ∀ x ∈ simpleBlock d s positive,
        ∀ i j : F4Chevalley.BasisIndex,
          ((((MulAut.conj g)⁻¹ * a) x).val.val : MatrixCarrier m) i j =
            σ ((x.val.val : MatrixCarrier m) i j) := by
  exact exists_simpleBlock_entries_of_torus_inputs d a
    (exists_torusFieldAction hm d hindex a hp hb)
    (exists_fixedGroup_torusMatrix_inv d)

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters
end
