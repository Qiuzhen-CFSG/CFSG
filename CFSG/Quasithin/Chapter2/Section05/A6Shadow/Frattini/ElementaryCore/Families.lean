module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.InvolutionLine

/-!
# From elementary subgroup families to the required core orbit

Source: Aschbacher–Smith, proof of 2.5.24, printed p.568. Conjugation
preserves elementary abelianness and order. If the largest elementary
subgroups form the two indicated local cores and S interchanges them,
the original crossing x has the required orbit. The family and its
transitivity must still be constructed in each extension branch.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore
universe u
variable {G : Type u} [Group G]

theorem rightConjugate_card (a : G) (E : Subgroup G) :
    Nat.card (rightConjugate a E) = Nat.card E :=
  card_map_of_injective (MulAut.conj a⁻¹).injective

theorem rightConjugate_elementary (a : G) (E : Subgroup G)
    (hE : IsElementaryAbelian 2 E) : IsElementaryAbelian 2 (rightConjugate a E) := by
  let := hE
  exact IsElementaryAbelian.map _

/-- An automorphism preserving S permutes its elementary subgroups of largest order. -/
theorem rightConjugate_mem_largest (a : G) (S E : Subgroup G)
    (hS : rightConjugate a S = S) (hE : E ∈ largestElementary S) :
    rightConjugate a E ∈ largestElementary S := by
  have hSi : rightConjugate a⁻¹ S = S := by
    calc
      rightConjugate a⁻¹ S = rightConjugate a⁻¹ (rightConjugate a S) :=
        congrArg (rightConjugate a⁻¹) hS.symm
      _ = S := rightConjugate_inv_cancel a S
  refine ⟨hS ▸ map_mono hE.1, rightConjugate_elementary a E hE.2.1, ?_⟩
  intro F hF hel
  have h := hE.2.2 (rightConjugate a⁻¹ F) (hSi ▸ map_mono hF)
    (rightConjugate_elementary a⁻¹ F hel)
  simpa only [rightConjugate_card] using h

variable [Finite G] {κ : GroupClass.{u}}

/-- A transitive two-element largest-elementary family gives the required
orbit, while keeping the original crossing element x. -/
theorem hasNormalizerOrbit_of_largest_pair (d : EarlierSetup κ G)
    (hfamily : largestElementary d.S = {localCore d (fourZero d), localCore d (fourOne d)})
    (hconj : ∃ s ∈ d.S,
      rightConjugate s (localCore d (fourZero d)) = localCore d (fourOne d)) :
    HasNormalizerOrbit d := by
  have hzero : localCore d (fourZero d) ∈ largestElementary d.S := by rw [hfamily]; simp
  have him := rightConjugate_mem_largest d.x d.S _ d.rightConjugate_s hzero
  rw [hfamily, Set.mem_insert_iff, Set.mem_singleton_iff] at him
  refine ⟨fourZero d, fourZero_le d, inferInstance, ?_⟩
  rcases him with h | h
  · exact ⟨1, d.S.one_mem, h.trans (rightConjugate_one _).symm⟩
  · obtain ⟨s, hs, he⟩ := hconj
    exact ⟨s, hs, h.trans he.symm⟩

omit [Finite G] in
/-- If the conjugate stays in the same overgroup, maximal elementary order
is preserved; the conjugating element need not normalize the overgroup. -/
theorem rightConjugate_mem_largest_of_le (a : G) (B A : Subgroup G)
    (hA : A ∈ largestElementary B) (himage : rightConjugate a A ≤ B) :
    rightConjugate a A ∈ largestElementary B := by
  refine ⟨himage, rightConjugate_elementary a A hA.2.1, ?_⟩
  intro F hF hel
  rw [rightConjugate_card]
  exact hA.2.2 F hF hel

/-- The contained branch can use a family in a smaller overgroup B.
Only the image of A must stay in B: there is no extra assumption that x
normalizes B or that x² normalizes A. The centralizer orbit is then the
orbit of the genuine local core. -/
theorem hasNormalizerOrbit_of_centralizer_family (d : EarlierSetup κ G)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) [IsKleinFour E]
    (A B F : Subgroup G)
    (hcore : localCore d E = d.S ⊓ centralizer (A : Set G))
    (hfamily : largestElementary B = {A, F})
    (himage : rightConjugate d.x A ≤ B)
    (htrans : ∃ s ∈ d.S, rightConjugate s A = F) : HasNormalizerOrbit d := by
  have hA : A ∈ largestElementary B := by rw [hfamily]; simp
  have him := rightConjugate_mem_largest_of_le d.x B A hA himage
  rw [hfamily, Set.mem_insert_iff, Set.mem_singleton_iff] at him
  have horbit : ∃ s ∈ d.S, rightConjugate d.x A = rightConjugate s A := by
    rcases him with h | h
    · exact ⟨1, d.S.one_mem, h.trans (rightConjugate_one A).symm⟩
    · obtain ⟨s, hs, he⟩ := htrans
      exact ⟨s, hs, h.trans he.symm⟩
  obtain ⟨s, hs, he⟩ := horbit
  refine ⟨E, hE, inferInstance, s, hs, ?_⟩
  rw [hcore]
  exact centralizer_orbit d A s hs he

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore
