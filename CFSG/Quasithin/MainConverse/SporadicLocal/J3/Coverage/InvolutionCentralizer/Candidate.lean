module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.FinCases

/-!
# The fixed local candidate centralizes the standard involution

Every generator of `localFamily 0` commutes with a. The five equalities are
checked by the kernel on all 6156 letters, using the previously certified
copies of the unchanged generators. Closure then gives the subgroup inclusion.
No cardinality or ambient-centralizer identification enters this proof.

Source: the fixed ATLAS J3G1-p6156B0 words and GLS3 Table 5.3h, p.269.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage
open Sporadic.Janko3 Sporadic.Janko3.TwoLocal
open Sporadic.Janko3.OrderCertificate Sporadic.Janko3.TwoLocal.CentralizerCertificate
set_option maxRecDepth 40000
set_option Elab.async false

private theorem comm0 : C0G0 * fastA = fastA * C0G0 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel
private theorem comm1 : C0G1 * fastA = fastA * C0G1 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel
private theorem comm2 : C0G2 * fastA = fastA * C0G2 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel
private theorem comm3 : C0G3 * fastA = fastA * C0G3 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel
private theorem comm4 : C0G4 * fastA = fastA * C0G4 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

/-- Each of the unchanged candidate generators commutes with a. -/
public theorem centralizerGenerator_commutes (i : Fin 5) :
    centralizerGenerator i * a = a * centralizerGenerator i := by
  apply embedding_injective
  simp only [map_mul]
  have ha : embedding a = fastA := fastA_eq_atlas.symm
  rw [ha]
  fin_cases i
  · change (centralizerGenerator 0 : Equiv.Perm (Fin 6156)) * fastA =
      fastA * (centralizerGenerator 0 : Equiv.Perm (Fin 6156))
    rw [← C0G0_eq_generator]
    exact comm0
  · change (centralizerGenerator 1 : Equiv.Perm (Fin 6156)) * fastA =
      fastA * (centralizerGenerator 1 : Equiv.Perm (Fin 6156))
    rw [← C0G1_eq_generator]
    exact comm1
  · change (centralizerGenerator 2 : Equiv.Perm (Fin 6156)) * fastA =
      fastA * (centralizerGenerator 2 : Equiv.Perm (Fin 6156))
    rw [← C0G2_eq_generator]
    exact comm2
  · change (centralizerGenerator 3 : Equiv.Perm (Fin 6156)) * fastA =
      fastA * (centralizerGenerator 3 : Equiv.Perm (Fin 6156))
    rw [← C0G3_eq_generator]
    exact comm3
  · change (centralizerGenerator 4 : Equiv.Perm (Fin 6156)) * fastA =
      fastA * (centralizerGenerator 4 : Equiv.Perm (Fin 6156))
    rw [← C0G4_eq_generator]
    exact comm4

/-- The candidate is contained in the ordinary ambient element centralizer. -/
public theorem localFamily_zero_le_involution_centralizer :
    localFamily 0 ≤ Subgroup.centralizer ({a} : Set Model) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (centralizerGenerator_commutes i)

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage
