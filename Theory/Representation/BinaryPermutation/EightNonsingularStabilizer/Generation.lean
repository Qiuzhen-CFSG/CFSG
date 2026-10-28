module

public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer.MovedCore

/-!
# Generating A₈ from the pair fixers on six complementary letters

Every three-cycle fixes at least two of the six letters complementary to a
chosen pair. Hence the pointwise two-letter fixers on those six letters
generate A₈. The six-letter pair words have weight two, and extension by
zero takes them to the corresponding original eight-letter pair words.

This is the permutation calculation in Aschbacher--Smith, combined
manuscript (1 March 2004), Lemma 12.6.10, printed p.825. The application
must still lift generation through the original two-core; equality only
in the action quotient does not give equality of the ambient subgroups.
-/

@[expose] public section
open Subgroup
namespace BinaryPermutation.EightNonsingular

/-- Pointwise fixers of pairs in any six complementary letters generate A₈. -/
theorem complementary_pairFixers_generate (i j : Fin 8) (B : Subgroup A)
    (hB : ∀ a b : Fin 8, a ≠ i → a ≠ j → b ≠ i → b ≠ j → a ≠ b →
      pointFixer a b ≤ B) : B = ⊤ := by
  classical
  apply top_unique
  rw [← alternatingGroup.closure_isThreeCycles_eq_top]
  apply (closure_le _).mpr
  intro g hg
  let F := (g.val.support ∪ {i,j})ᶜ
  have hcard : 1 < F.card := by
    have hb := Finset.card_union_le g.val.support {i,j}
    have hc := Finset.card_le_two (a := i) (b := j)
    have he := hg.card_support
    dsimp only [F]
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hcard
  simp only [F, Finset.mem_compl, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, not_or] at ha hb
  apply hB a b ha.2.1 ha.2.2 hb.2.1 hb.2.2 hab
  intro x
  rcases x.property with hx | hx
  · have he : x.val = a := hx
    change g.val x.val = x.val
    rw [he]
    exact Equiv.Perm.notMem_support.mp ha.1
  · have he : x.val = b := hx
    change g.val x.val = x.val
    rw [he]
    exact Equiv.Perm.notMem_support.mp hb.1

/-- The pair word in the six-letter augmentation core. -/
def sixPair (a b : Fin 6) : core (Fin 6) :=
  ⟨Pi.single a 1 + Pi.single b 1, by simp [mem_core, Finset.sum_add_distrib]⟩

/-- Extension by zero retains the two actual marked letters. -/
theorem extendSix_pair (i j : Fin 8) (hij : i ≠ j) (a b : Fin 6) :
    extendSix i j hij (sixPair a b) =
      pair (complementLetters i j hij a) (complementLetters i j hij b) := by
  apply Subtype.ext
  change extendSixFull i j hij (Pi.single a 1 + Pi.single b 1) = _
  rw [map_add]
  simp [extendSixFull, pair, Pi.single_apply, apply_ite]


/-- Distinct complementary letters give a word of weight two. -/
theorem sixPair_weight (a b : Fin 6) (hab : a ≠ b) :
    hammingNorm (sixPair a b).val = 2 := by
  classical
  have hs : (Finset.univ.filter fun k => (sixPair a b).val k ≠ 0) = {a,b} := by
    ext k
    by_cases hka : k = a
    · subst k; simp [sixPair,hab,Finset.mem_filter,Pi.single_apply]
    by_cases hkb : k = b
    · subst k; simp [sixPair,hab.symm,Finset.mem_filter,Pi.single_apply]
    simp [sixPair, Pi.single_apply, hka, hkb]
  change (Finset.univ.filter _).card = 2
  rw [hs]
  simp [hab]

end BinaryPermutation.EightNonsingular
