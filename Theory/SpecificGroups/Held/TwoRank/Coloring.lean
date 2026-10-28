module

public import Theory.SpecificGroups.Held.TwoRank.Coloring.Checks
public import Theory.GroupTheory.ElementaryAbelianColorBound

/-!+# Two-rank of the concrete Held Sylow extension

The sixty-four certified classes cover every element of square one in the
actual two-coset extension. No class contains distinct commuting elements.
An elementary abelian subgroup therefore has at most sixty-four elements,
even when it meets the outer coset. This proves the sharp upper bound needed
by G.7 without assuming any abstract automorphism realization.

Source: Aschbacher--Smith, Lemma G.7.3(2), printed p.348; the ATLAS
degree-2058 Held permutations used in the checked word certificates.
-/

public section
namespace Held.TwoRank
open Theory.GroupTheory Coloring

/-- The actual extension, including its outside coset, has two-rank at most six. -/
theorem extendedSylow_twoRank_le_six : primeRank 2 extendedSylow ≤ 6 := by
  apply (primeRank_le_iff_elementary_card_le extendedSylow).mpr
  intro E hE
  let := hE
  have hcover (x : extendedSylow) (hs : x ^ 2 = 1) :
      ∃ c i, extensionWord (classIndex c i) = x := by
    obtain ⟨n, rfl⟩ := extensionWord_surjective x
    refine ⟨(position n).1, (position n).2, ?_⟩
    rw [index_eq_of_coverCheck n (coverChecks n) hs]
  have hsep (c : Fin 64) (i j : Fin 12)
      (h : Commute (extensionWord (classIndex c i)) (extensionWord (classIndex c j))) :
      extensionWord (classIndex c i) = extensionWord (classIndex c j) :=
    eq_of_separationCheck c i j (separationChecks c i j) h
  simpa using elementary_card_le_of_commuting_colors
    (fun c i => extensionWord (classIndex c i)) hcover hsep E

end Held.TwoRank
