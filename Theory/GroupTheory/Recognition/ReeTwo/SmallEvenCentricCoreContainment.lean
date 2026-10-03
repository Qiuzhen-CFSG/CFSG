module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates
public import Theory.GroupTheory.Recognition.ReeTwo.SmallCentricCharacterKernels
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenFrattiniCensus
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutWitnesses
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCharacteristicWitnesses
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenExceptionalWitness

/-!
# Assembly for small even centric Ree two subgroups

A checked census of the Frattini survivors and normalizer p-core witnesses
for all 59 representatives prove containment in the core-character kernel.
The representatives split into 34 with two-group automorphism groups, 24 with
characteristic-series witnesses, and one exceptional representative. Centricity
and intrinsic radicality exclude every such witness. The conditional assembly
interface is retained alongside the theorem discharging all census and witness
premises.

The roots and candidate words follow Shinoda (1975), (2.3), pp. 81–82;
the local analysis is motivated by van Beek (2024), Proposition 3.1.
-/

namespace ReeTwo.SylowModel

/-- Coverage and local p-core witnesses imply the desired even containment. -/
public theorem smallEven_le_coreCharacter_ker_of_census_of_witnesses
    (hcensus : SmallEvenFrattiniCensus)
    (hwitness : ∀ i : Fin 59, (smallEvenCandidate i).HasPCoreNormalizerWitness 2)
    (U : Subgroup SylowModel)
    (hcent : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hcard : Nat.card U < 1024) (hpar : U ≤ character.ker) :
    U ≤ coreCharacter.ker := by
  by_contra hnot
  have hU : IsPGroup 2 U := (IsPGroup.of_card (n := 12) card).to_subgroup U
  obtain ⟨i, g, heq⟩ := hcensus U hcent hcard hpar hnot
    (fun g hg => Subgroup.mem_of_intrinsic_radical_of_frattini_action_eq_one
      U hU hcent hrad g hg)
  apply Subgroup.not_hasPCoreNormalizerWitness_of_intrinsic_radical U hcent hrad
  rw [heq]
  exact Subgroup.HasPCoreNormalizerWitness.map 2 _ (MulAut.conj g) (hwitness i)

/-- All 59 small even Frattini survivors admit an outside normalizer element
acting in the two-core of their full automorphism group. -/
public theorem smallEvenCandidate_hasPCoreNormalizerWitness (i : Fin 59) :
    (smallEvenCandidate i).HasPCoreNormalizerWitness 2 := by
  have hcover : ∀ j : Fin 59, j ∈ smallEvenTwoAutIndices ∨
      j ∈ smallEvenCharacteristicIndices ∨ j = 3 := by decide +kernel
  rcases hcover i with hi | hi | rfl
  · exact smallEvenTwoAut_witnesses i hi
  · exact smallEvenCharacteristic_hasPCoreNormalizerWitness i hi
  · exact smallEvenExceptional_hasPCoreNormalizerWitness

/-- A small centric intrinsic radical subgroup contained in the parity kernel
is also contained in the core-character kernel. -/
public theorem smallEven_le_coreCharacter_ker
    (U : Subgroup SylowModel)
    (hcent : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hcard : Nat.card U < 1024) (hpar : U ≤ character.ker) :
    U ≤ coreCharacter.ker :=
  smallEven_le_coreCharacter_ker_of_census_of_witnesses
    smallEvenFrattiniCensus smallEvenCandidate_hasPCoreNormalizerWitness
    U hcent hrad hcard hpar

end ReeTwo.SylowModel
