module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Pair00
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Pair01
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Pair10
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Pair11
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup
import Mathlib.Tactic.FinCases

/-!
# Transport of the fixed Held normalizer to the four candidate two-groups

Both generator inclusions give genuine conjugacies with the fixed subgroup P.
Consequently N(P)=P implies N(S)=S for each literal candidate S, and the
already proved two-group property transfers without any order assumption.
The marked sign-change actors lie in S and normalize the literal odd subgroup.
Source: GLS3 Table 5.3p; the checked ATLAS words in the four Pair modules.
-/

public section
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages
open Subgroup

private theorem forward (i : Bool) (j : Fin 2) (k : Fin 4) :
    transporter i j * SylowGeometry.Calculations.generator k * (transporter i j)⁻¹ =
      evalPowers (twoGenerator i j) (forwardWord i j k) := by
  cases i <;> fin_cases j
  · exact Pair00.forward k
  · exact Pair01.forward k
  · exact Pair10.forward k
  · exact Pair11.forward k

private theorem backward (i : Bool) (j : Fin 2) (k : Fin 4) :
    (transporter i j)⁻¹ * twoGenerator i j k * transporter i j =
      evalPowers SylowGeometry.Calculations.generator (backwardWord i j k) := by
  cases i <;> fin_cases j
  · exact Pair00.backward k
  · exact Pair01.backward k
  · exact Pair10.backward k
  · exact Pair11.backward k

theorem representative_map (i : Bool) (j : Fin 2) :
    SylowGeometry.Calculations.representative.map
      (MulAut.conj (transporter i j)).toMonoidHom = candidateTwo i j := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    change transporter i j * _ * (transporter i j)⁻¹ ∈ candidateTwo i j
    rw [forward]
    exact evalPowers_mem _ _ (twoGenerator_mem i j) _
  · apply (closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨(transporter i j)⁻¹ * twoGenerator i j k * transporter i j, ?_, ?_⟩
    · rw [backward]
      exact evalPowers_mem _ _ SylowGeometry.Calculations.generator_mem _
    · change transporter i j * ((transporter i j)⁻¹ * twoGenerator i j k * transporter i j) *
        (transporter i j)⁻¹ = twoGenerator i j k
      simp [mul_assoc]

theorem candidateTwo_isPGroup (i : Bool) (j : Fin 2) : IsPGroup 2 (candidateTwo i j) := by
  rw [← representative_map i j]
  exact SylowGeometry.Calculations.representative_isPGroup.map _

theorem candidateTwo_normalizer
    (hP : normalizer (SylowGeometry.Calculations.representative : Set He) =
      SylowGeometry.Calculations.representative) (i : Bool) (j : Fin 2) :
    normalizer (candidateTwo i j : Set He) = candidateTwo i j := by
  rw [← representative_map i j, ← map_equiv_normalizer_eq, hP]

theorem actor_action (i : Bool) (j k l : Fin 2) :
    actor i j k * basisGenerator i j l * (actor i j k)⁻¹ =
      if l = k then (basisGenerator i j l)⁻¹ else basisGenerator i j l := by
  cases i <;> fin_cases j
  · exact Pair00.actor_action k l
  · exact Pair01.actor_action k l
  · exact Pair10.actor_action k l
  · exact Pair11.actor_action k l

theorem basisGenerator_closure (i : Bool) (j : Fin 2) :
    closure (Set.range (basisGenerator i j)) = candidateOdd i j := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    exact basisGenerator_mem i j k
  · apply (closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    have hm (l : Fin 2) : basisGenerator i j l ∈ closure (Set.range (basisGenerator i j)) :=
      subset_closure ⟨l, rfl⟩
    change oddGenerator i j k ∈ _
    by_cases he : i = true ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := he
      fin_cases k
      · have hh := (closure (Set.range (basisGenerator true 0))).mul_mem (hm 1)
          ((closure (Set.range (basisGenerator true 0))).inv_mem (hm 0))
        simpa [basisGenerator, mul_assoc] using hh
      · simpa [basisGenerator] using hm 0
    · simpa [basisGenerator, he] using hm k

theorem actor_normalizes_odd (i : Bool) (j k : Fin 2) :
    actor i j k ∈ normalizer (candidateOdd i j : Set He) := by
  rw [← basisGenerator_closure]
  apply mem_normalizer_closure_of_conjugates
  rintro _ ⟨l, rfl⟩
  rw [actor_action]
  have hm : basisGenerator i j l ∈ closure (Set.range (basisGenerator i j)) :=
    subset_closure ⟨l, rfl⟩
  split
  · exact inv_mem hm
  · exact hm

end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages
