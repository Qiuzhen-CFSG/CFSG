module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Uniqueness
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Characteristic two in M ∩ I

Since S ≤ M ∩ I and [T:S]=2, the intersection of M ∩ I with a Sylow
subgroup of M has index at most two. The proved characteristic-two
inheritance theorem then gives a self-centralizing two-core. The component
argument identifies the full generalized Fitting subgroup with that core.
No normality of M ∩ I in M is required.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.11(7),
p.1124, using 1.1.4(7), pp.500–501.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
variable {G : Type*} [Group G] [Finite G]

/-- Clause (7), with the self-centralizing-core form and the literal generalized
Fitting equality. The index-two input comes from the natural plane stabilizer. -/
theorem lemma_15_3_11_7_of_index_two (T : Sylow 2 G) (M S I : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hST : S ≤ (T : Subgroup G)) (hSI : S ≤ I)
    (hindex : (S.subgroupOf (T : Subgroup G)).index = 2)
    (hM : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :
    centralizer (pCore 2 ↥(M ⊓ I) : Set ↥(M ⊓ I)) ≤ pCore 2 ↥(M ⊓ I) ∧
      Theory.GroupTheory.generalizedFitting ↥(M ⊓ I) = pCore 2 ↥(M ⊓ I) := by
  have hi : ((M ⊓ I).subgroupOf M).relIndex (T.subtype hTM : Subgroup M) ≤ 2 := by
    rw [Sylow.coe_subtype, relIndex_subgroupOf hTM]
    calc
      (M ⊓ I).relIndex (T : Subgroup G) ≤ S.relIndex (T : Subgroup G) :=
        relIndex_le_of_le_left (le_inf (hST.trans hTM) hSI) index_ne_zero_of_finite
      _ = 2 := hindex
  have hMI := (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe (show M ⊓ I ≤ M from inf_le_left))).mp
    (centralizer_pCore_le_of_sylow_relIndex_le_two hM (T.subtype hTM) _ hi)
  exact ⟨hMI, Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2 hMI⟩
end CFSG.Quasithin.Chapter15.Section03.OutsideStructure

end
