module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute01
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute02
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute03
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute04
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute05
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute12
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute13
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute14
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute15
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute23
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute24
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute25
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute34
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute35
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Commute45
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Relations.Candidate
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Tail
import Mathlib.Tactic.FinCases

/-!
# Certified terminal relations for the Fi23 suffix chain

The six literal permutations commute, and generator 1 followed on the right
by generator 3 is the exact candidate map. Fifteen full table checks suffice:
the other ordered pairs follow by symmetry or reflexivity. Every table check
uses 32 kernel-checked blocks of 1024 inputs; no external evaluator is trusted.

`afterFour_tail_bound` discharges both numerical premises of the existing
binary collection argument, identifying its remaining product with the literal
ATLAS candidate. Earlier suffix stabilizer containments remain with
`KernelLower` and are not asserted here.

Source application: GLS3 Table 5.3u; ATLAS F23G1-p31671B0. The permutation
tables and action convention are documented in `KernelLower/source/README.md`.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerData

/-- All six literal suffix generators commute as permutations. -/
theorem afterFourGenerator_commute (i j : Fin 6) :
    afterFourGenerator i * afterFourGenerator j =
      afterFourGenerator j * afterFourGenerator i := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact commute_of_checked 0 1 Relations.Commute01.checked
  · exact commute_of_checked 0 2 Relations.Commute02.checked
  · exact commute_of_checked 0 3 Relations.Commute03.checked
  · exact commute_of_checked 0 4 Relations.Commute04.checked
  · exact commute_of_checked 0 5 Relations.Commute05.checked
  · exact (commute_of_checked 0 1 Relations.Commute01.checked).symm
  · rfl
  · exact commute_of_checked 1 2 Relations.Commute12.checked
  · exact commute_of_checked 1 3 Relations.Commute13.checked
  · exact commute_of_checked 1 4 Relations.Commute14.checked
  · exact commute_of_checked 1 5 Relations.Commute15.checked
  · exact (commute_of_checked 0 2 Relations.Commute02.checked).symm
  · exact (commute_of_checked 1 2 Relations.Commute12.checked).symm
  · rfl
  · exact commute_of_checked 2 3 Relations.Commute23.checked
  · exact commute_of_checked 2 4 Relations.Commute24.checked
  · exact commute_of_checked 2 5 Relations.Commute25.checked
  · exact (commute_of_checked 0 3 Relations.Commute03.checked).symm
  · exact (commute_of_checked 1 3 Relations.Commute13.checked).symm
  · exact (commute_of_checked 2 3 Relations.Commute23.checked).symm
  · rfl
  · exact commute_of_checked 3 4 Relations.Commute34.checked
  · exact commute_of_checked 3 5 Relations.Commute35.checked
  · exact (commute_of_checked 0 4 Relations.Commute04.checked).symm
  · exact (commute_of_checked 1 4 Relations.Commute14.checked).symm
  · exact (commute_of_checked 2 4 Relations.Commute24.checked).symm
  · exact (commute_of_checked 3 4 Relations.Commute34.checked).symm
  · rfl
  · exact commute_of_checked 4 5 Relations.Commute45.checked
  · exact (commute_of_checked 0 5 Relations.Commute05.checked).symm
  · exact (commute_of_checked 1 5 Relations.Commute15.checked).symm
  · exact (commute_of_checked 2 5 Relations.Commute25.checked).symm
  · exact (commute_of_checked 3 5 Relations.Commute35.checked).symm
  · exact (commute_of_checked 4 5 Relations.Commute45.checked).symm
  · rfl

/-- Product 10 in the binary collection is the exact checked candidate map. -/
theorem afterFourGenerator_one_three_eq_candidateMap (x : Fin 31671) :
    afterFourGenerator 1 (afterFourGenerator 3 x) =
      GeneratorLiftCertificate.candidateMap x :=
  candidate_eq_of_checked Relations.Candidate.checked x

/-- Fixing the final three suffix points leaves the identity or the literal
ATLAS candidate; both numerical premises of the collection argument are proved. -/
theorem afterFour_tail_bound
    (p : Equiv.Perm (Fin 31671)) (hp : p ∈ afterFour)
    (h78 : p 78 = 78) (h86 : p 86 = 86) (h108 : p 108 = 108) :
    p = 1 ∨ p = inclusion candidate :=
  afterFour_tail_bound_of_relations afterFourGenerator_commute
    afterFourGenerator_one_three_eq_candidateMap p hp h78 h86 h108

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerData
