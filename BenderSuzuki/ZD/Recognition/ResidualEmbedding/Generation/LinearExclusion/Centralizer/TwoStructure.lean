module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.TwoStructure.ModelConsequences
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.TwoStructure.Reduction

/-!+# Assembly of the earlier linear two-core structure

The actual embedding J → L makes every two-subgroup of J elementary
abelian and, once O₂(J) is nontrivial, makes that core Sylow. The earlier
involution-centralizer result puts all pair-stabilizer involutions in it.
An odd supplement C₀=VY then identifies D∩V with the embedded O₂(J).

The theorem below assembles these proved consequences while retaining
nontriviality and the odd supplement as explicit source premises. It does
not assert the full result from the model interface alone. The remaining
source arguments are Lemmas 15.3, 15.4 and the first assertion of 15.5;
their final discharge belongs in this module. In particular the quotient
in the proof of 15.4 is M/A, not M.

Source: refs/KGroup/GLS4/Chapter2.tex, Lemmas 15.3–15.5.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)

/-- Conditional assembly: the model consequences and the literal pair-core
equality discharge all remaining fields once source 15.4 and the odd
supplement of 15.5 have been supplied. -/
public theorem Context.centralizerLocalTwoData_of_nontrivial_of_odd_supplement
    (hm : CentralizerLocalModelData d)
    (hne : pCore 2 (centralizer (residualGenerated M z t : Set G)) ≠ ⊥)
    (hsupp : ∃ Y : Subgroup G,
      Y ≤ centralizer (residualGenerated M z t : Set G) ∧ Odd (Nat.card Y) ∧
        ((M ⊓ centralizer (closure (Z ∩ (M : Set G)) : Set G) : Subgroup G) : Set G) =
          ((pCore 2 M).map M.subtype : Set G) * (Y : Set G)) :
    CentralizerLocalTwoData d := by
  obtain ⟨Y, hYJ, hodd, hprod⟩ := hsupp
  exact {
    twoCore_ne_bot := hne
    twoCore_sylow := d.centralizer_twoCore_sylow hm hne
    twoCore_elementary := d.centralizer_twoCore_elementary hm
    pair_core_eq := d.pair_core_eq_of_odd_supplement hYJ hodd hprod
    pair_involutions := fun _ hvD hv => d.pair_involutions_mem_twoCore hm hne hvD hv
    centralizer_odd_supplement := ⟨Y, hYJ, hodd, hprod⟩ }

end BenderSuzuki.ZD.LinearExclusion
