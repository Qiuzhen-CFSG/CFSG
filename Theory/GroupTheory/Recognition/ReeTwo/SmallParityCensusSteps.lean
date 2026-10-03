module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusNodes
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusStepsUpper
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusStepsOrder256
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusStepsOrder128
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusStepsLower
public import Theory.GroupTheory.SubgroupEnumerationBinary
public import Theory.GroupTheory.SubgroupEnumeration
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Maximal steps for the Ree two parity census

Binary Schreier generators reduce each maximal step to an explicit finite
check. The two terminal nodes are cyclic: their displayed generators are the
first, second, fourth and eighth powers of one element. Every maximal subgroup
of either node is therefore contained in the parity kernel.

The four imported range certificates cover nodes 0 through 128. Together with
the terminal calculation, they prove `smallParityCensusStep` for every centric
maximal subgroup outside parity, including below nodes later excluded by
Frattini witnesses. No Frattini or size hypothesis is used in this module.

Source: the Shinoda root model and fixed words in `SmallParityCensusNodes`;
Schreier's lemma as specialized in `SubgroupEnumerationBinary`.
-/

namespace ReeTwo.SylowModel
open Theory.GroupTheory.SubgroupEnumeration
private def terminalGenerator129 : SylowModel :=
  rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9
private def terminalGenerator130 : SylowModel :=
  rootOne * root 0 * root 1 * root 6 * root 7 * root 9
private theorem terminal129_powers :
    terminalGenerator129 ^ 2 = rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9 ∧
    terminalGenerator129 ^ 4 = root 4 * root 5 * root 7 * root 9 ∧
    terminalGenerator129 ^ 8 = root 9 := by decide +kernel
private theorem terminal130_powers :
    terminalGenerator130 ^ 2 = rootOne ^ 2 * root 1 * root 3 * root 5 * root 7 ∧
    terminalGenerator130 ^ 4 = root 4 * root 5 ∧
    terminalGenerator130 ^ 8 = root 9 := by decide +kernel

private theorem closure_powers (t : SylowModel) :
    Subgroup.closure ({t, t ^ 2, t ^ 4, t ^ 8} : Set SylowModel) = Subgroup.closure {t} := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    all_goals exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  · exact Subgroup.closure_mono (by simp)

private theorem terminal129_cyclic : smallParityCensusNode 129 =
    Subgroup.closure {terminalGenerator129} := by
  change Subgroup.closure ({terminalGenerator129,
    rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9,
    root 4 * root 5 * root 7 * root 9, root 9} : Set SylowModel) = _
  rw [← terminal129_powers.1, ← terminal129_powers.2.1, ← terminal129_powers.2.2]
  exact closure_powers _
private theorem terminal130_cyclic : smallParityCensusNode 130 =
    Subgroup.closure {terminalGenerator130} := by
  change Subgroup.closure ({terminalGenerator130,
    rootOne ^ 2 * root 1 * root 3 * root 5 * root 7,
    root 4 * root 5, root 9} : Set SylowModel) = _
  rw [← terminal130_powers.1, ← terminal130_powers.2.1, ← terminal130_powers.2.2]
  exact closure_powers _

/-- Every maximal subgroup of census node 129 is in parity. -/
public theorem smallParityCensusStep_terminal129 (H : Subgroup SylowModel)
    (h : H ⋖ smallParityCensusNode 129) : H ≤ character.ker := by
  rw [terminal129_cyclic] at h
  exact le_of_covBy_cyclic (IsPGroup.of_card (p := 2) (n := 12) card)
    terminalGenerator129 h (by decide +kernel)

/-- Every maximal subgroup of census node 130 is in parity. -/
public theorem smallParityCensusStep_terminal130 (H : Subgroup SylowModel)
    (h : H ⋖ smallParityCensusNode 130) : H ≤ character.ker := by
  rw [terminal130_cyclic] at h
  exact le_of_covBy_cyclic (IsPGroup.of_card (p := 2) (n := 12) card)
    terminalGenerator130 h (by decide +kernel)

/-- Finite binary Schreier checks suffice for the exact census step at one node.
The alternatives are parity containment, an outside centralizer witness, or
conjugacy to a census node. There is no Frattini pruning. -/
public theorem smallParityCensusStep_of_binary_checks {n : ℕ}
    (i : Fin 131) (s : Fin n → SylowModel)
    (hs : Subgroup.closure (Set.range s) = smallParityCensusNode i)
    (hcheck : ∀ (σ : Fin n → Bool) (j : Fin n), σ j = true →
      let L := Subgroup.closure (Set.range (binarySchreierGenerator s (s j) σ))
      L ≤ character.ker ∨
        (∃ g, g ∈ Subgroup.centralizer (L : Set SylowModel) ∧ g ∉ L) ∨
        Represented smallParityCensusNode L)
    (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode i)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H)
    (hparity : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  exact represented_of_binary_checks (IsPGroup.of_card (p := 2) (n := 12) card)
    smallParityCensusNode character.ker i s hs hcheck H hmax hcent hparity

/-- Every centric maximal subgroup outside parity of any of the 131 census
nodes is conjugate to a census node. No nodes are pruned from this descent. -/
public theorem smallParityCensusStep (i : Fin 131) (H : Subgroup SylowModel)
    (hmax : H ⋖ smallParityCensusNode i)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H)
    (hparity : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  by_cases h29 : i.val < 29
  · exact smallParityCensusStep_upper i h29 H hmax hcent hparity
  by_cases h61 : i.val < 61
  · exact smallParityCensusStep_order256 i (by omega) h61 H hmax hcent hparity
  by_cases h97 : i.val < 97
  · exact smallParityCensusStep_order128 i (by omega) h97 H hmax hcent hparity
  by_cases h129 : i.val < 129
  · exact smallParityCensusStep_lower i (by omega) h129 H hmax hcent hparity
  have hi : i = 129 ∨ i = 130 := by omega
  rcases hi with rfl | rfl
  · exact (hparity (smallParityCensusStep_terminal129 H hmax)).elim
  · exact (hparity (smallParityCensusStep_terminal130 H hmax)).elim

end ReeTwo.SylowModel
