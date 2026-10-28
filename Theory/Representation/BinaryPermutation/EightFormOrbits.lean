module
public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer
public import Theory.Representation.BinaryPermutation.OrbitSizeSeparation

/-!
# The two nonzero orbits of the binary A8 six-space

Nonzero singular vectors have weight-four lifts in the augmentation core.
Nonsingular vectors have weight-two lifts. Even permutations carry any two
core words of the same weight to one another, so equality of the original
half-weight form gives an actual alternating-group conjugator on the natural
quotient. The proof retains the literal core-to-natural projection.

Source: Aschbacher--Smith, 12.6.1(1) and 12.6.19(1), combined manuscript
of 1 March 2004, printed pp.823 and 828.
-/

public section
namespace BinaryPermutation.EightGeometry
open BinaryPermutation.TerminalOrthogonal.Eight

private theorem pair_weight (i j : Fin 8) (hij : i ≠ j) :
    hammingNorm (EightNonsingular.pair i j).val = 2 := by
  have h : ∀ i j : Fin 8, i ≠ j → hammingNorm (EightNonsingular.pair i j).val = 2 := by
    decide +kernel
  exact h i j hij

/-- Equal form values distinguish precisely the two nonzero A8 orbits. -/
theorem exists_alternating_of_form_eq (v w : natural (Fin 8))
    (hv : v ≠ 0) (hw : w ≠ 0) (hform : form v = form w) :
    ∃ g : alternatingGroup (Fin 8), alternatingNaturalRepresentation (Fin 8) g v = w := by
  have hlift : ∃ a b : core (Fin 8), coreToNatural (Fin 8) a = v ∧
      coreToNatural (Fin 8) b = w ∧ hammingNorm a.val = hammingNorm b.val := by
    by_cases hs : form v = 0
    · obtain ⟨a,ha,hac⟩ := (singular_iff_weight_four v hv).mp hs
      obtain ⟨b,hb,hbc⟩ := (singular_iff_weight_four w hw).mp (hform.symm.trans hs)
      exact ⟨a,b,ha,hb,hac.trans hbc.symm⟩
    · obtain ⟨i,j,hij,ha⟩ := EightNonsingular.nonsingular_pair v hs
      obtain ⟨k,l,hkl,hb⟩ := EightNonsingular.nonsingular_pair w (hform ▸ hs)
      exact ⟨EightNonsingular.pair i j,EightNonsingular.pair k l,ha,hb,
        (pair_weight i j hij).trans (pair_weight k l hkl).symm⟩
  obtain ⟨a,b,ha,hb,hab⟩ := hlift
  obtain ⟨g,hg⟩ := exists_even_permutation_of_weight
    (by decide : 3 ≤ Fintype.card (Fin 8)) a.val b.val hab
  refine ⟨g,?_⟩
  rw [←ha,←hb]
  exact (coreToNatural_equivariant g.val a).symm.trans
    (congrArg (coreToNatural (Fin 8)) (Subtype.ext hg))
end BinaryPermutation.EightGeometry
