module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification.Candidates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification.Enumeration.Certificates

/-!
# The four possibilities for Janko's normalized generator

The conjugation relation reconstructs the generator from four point images
and its action on the two fixed points of `m`. Kernel-checked finite
certificates filter that complete parametrization using consequences of the
order, fixed-point, square-normalization and product-profile hypotheses.
The four surviving tables equal the four actual source permutations.

This proves the finite enumeration on p.18 of Z. Janko,
*A characterization of the Mathieu simple groups, I*, J. Algebra 9 (1968),
Section 9, DOI 10.1016/0021-8693(68)90002-1. Choosing normalized coordinates
and excluding the first and third candidates are separate steps.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification
open JankoModel

/-- Janko's complete four-candidate enumeration for a normalized generator. -/
public theorem eq_one_of_four (n : Equiv.Perm (Fin 22))
    (n_order : orderOf n = 4)
    (n_fixed : (Finset.univ.filter (fun x => n x = x)).card = 2)
    (square_fixed : (Finset.univ.filter (fun x => (n ^ 2) x = x)).card = 6)
    (conjugates_m : n * m * n⁻¹ = m ^ 2)
    (square_normalized : SquareNormalized n)
    (profiles : ∀ i : Fin 11, HasAllowedProfile (ell ^ i.val * n)) :
    n = n1 ∨ n = n2 ∨ n = n3 ∨ n = n4 := by
  obtain ⟨a, b, c, d, s, hn⟩ := Enumeration.exists_candidateTable n conjugates_m
  have ht := Enumeration.passesTests_of_source n n_order n_fixed square_fixed
    square_normalized profiles
  rw [hn] at ht
  have h := Enumeration.exhaustive a b c d s ht
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact Or.inl (Equiv.ext (congrFun (hn.trans Enumeration.candidateTable_n1)))
  · exact Or.inr (Or.inl (Equiv.ext (congrFun (hn.trans Enumeration.candidateTable_n2))))
  · exact Or.inr (Or.inr (Or.inl
      (Equiv.ext (congrFun (hn.trans Enumeration.candidateTable_n3)))))
  · exact Or.inr (Or.inr (Or.inr
      (Equiv.ext (congrFun (hn.trans Enumeration.candidateTable_n4)))))

end Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification
