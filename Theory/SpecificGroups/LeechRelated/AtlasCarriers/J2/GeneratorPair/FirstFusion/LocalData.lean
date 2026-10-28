module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.Orbit
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.CentralizerWords
import Mathlib.Tactic.FinCases

/-!
# Shared finite words for the remaining J₂ first-generator checks

The word `c` is a proved member of the odd-index centralizer. Every listed
`centralizerElement` is a word in `a, c, c⁻¹`, hence belongs to it. Combining
coverage by these words with the already proved 315-coset cover enumerates
the whole carrier by `pairRepresentative`.

Coverage by the 1920 centralizer words, their involution fusion, and the
commutator test on the product representatives remain separate finite checks.
No coverage is inferred from the number of entries in a generated table.
Source: ATLAS `J2G1-p100B0`; GLS3, Table 5.3g motivates this local calculation.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion
open Theory.GroupTheory

def c : Carrier := schreier (263, 1)
def centralizerLetter : Fin 3 → Carrier := ![a, c, c⁻¹]
def centralizerElement (i : Fin 1920) : Carrier :=
  evalWord centralizerLetter (CentralizerData.words i)

theorem a_mem_centralizer : a ∈ centralizer := by
  have h := step_mem 0 0
  have hn : OrbitData.next 0 0 = 0 := by decide +kernel
  simpa [hn, rep_zero, letter] using h

theorem c_mem_centralizer : c ∈ centralizer := step_mem 263 1

theorem centralizerLetter_mem (i : Fin 3) : centralizerLetter i ∈ centralizer := by
  fin_cases i
  · exact a_mem_centralizer
  · exact c_mem_centralizer
  · exact centralizer.inv_mem c_mem_centralizer

theorem centralizerElement_mem (i : Fin 1920) : centralizerElement i ∈ centralizer := by
  have hw (w : List (Fin 3)) : evalWord centralizerLetter w ∈ centralizer := by
    induction w with
    | nil => exact centralizer.one_mem
    | cons j w ih => exact centralizer.mul_mem (centralizerLetter_mem j) ih
  exact hw _

def pairRepresentative (i : Fin 1920) (j : Fin 315) : Carrier :=
  centralizerElement i * rep j

theorem pairRepresentative_cover
    (hcover : ∀ z ∈ centralizer, ∃ i : Fin 1920, z = centralizerElement i)
    (y : Carrier) : ∃ i : Fin 1920, ∃ j : Fin 315, y = pairRepresentative i j := by
  obtain ⟨z, j, hy⟩ := cosetCover.covers letter_generates y
  change y = z.val * rep j at hy
  obtain ⟨i, hi⟩ := hcover z z.property
  exact ⟨i, j, by simpa only [pairRepresentative, hi] using hy⟩

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion
