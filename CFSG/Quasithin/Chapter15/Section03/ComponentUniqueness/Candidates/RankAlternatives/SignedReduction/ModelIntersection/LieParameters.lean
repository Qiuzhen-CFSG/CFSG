module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.LieParameters.Orders
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.LieParameters.Ranks
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.GroupTheory.PrimeRankZero
/-!
# Even signed parameters in the complete simple Lie alternative

This proves the exact Lie comparison premise used by
`ModelIntersection.intersection_of_carrier_comparisons`. Every constructor of
the characteristic-two catalogue is retained. Large classical groups, the
actual triality carrier, and the Ree fixed group have two-rank at least three,
whereas an odd signed degree-three parameter has two-rank at most two.

For the small endpoints, the defining-parameter cube divides the actual group
order. Their checked orders divide 2¹¹ · 3³ · 5² · 7 · 13; the congruence
excludes defining characteristic three, leaving two. This includes the actual
derived groups Sp₄(2)′ and G₂(2)′ and Parrott's Tits presentation. Suzuki is
excluded because its order is prime to three and the supplied three-rank is two.
No parameter recognition, family disjointness, or exceptional isomorphism is
assumed. The parent retains the given signed isomorphism and final assembly.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.18(2),
printed pp.51--52; 1.1.5(3), pp.501--503; applications in 15.3.37 and
15.3.43, pp.1135 and 1139.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
open Chapter1.Section02.LocalModels ClassificationModels ComponentStructure
universe u

/-- The complete simple Lie alternative forces the supplied signed parameter to be even. -/
theorem lie_parameters (S : Type u) [Group S] [Finite S] [IsQuasisimple S]
    (_hs : IsSimpleGroup S) (hmodel : LieTypeTwoModel S) (hrank : primeRank 3 S = 2)
    (unitary : Bool) (q : ℕ) (hmod : q % 3 = (if unitary then 2 else 1))
    (hsigned : IsPSLSign S unitary 3 q) : Even q := by
  rcases hmodel with hm | hm | ⟨n, hn, hm⟩
  · cases hm with
    | linear f hf hm =>
      by_cases hf3 : 3 ≤ f
      · exact signed_even_of_linear_two hf3 hm hsigned
      have hf2 : f = 2 := by omega
      subst f
      obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
      apply signed_even_of_small_order hsigned hmod
      rw [Nat.card_congr e.toEquiv]
      have he := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
      rw [hc] at he
      norm_num [Fin.prod_univ_succ] at he
      have he' : Nat.card PSL(2,F) = 60 := by omega
      rw [he']
      norm_num
    | unitary f hf hm =>
      by_cases hf3 : 3 ≤ f
      · exact signed_even_of_unitary_three hf3 hm hsigned
      have hf2 : f = 2 := by omega
      subst f
      obtain ⟨F, hF, hfin, J, hc, hconj, ⟨e⟩⟩ := hm
      apply signed_even_of_small_order hsigned hmod
      rw [Nat.card_congr e.toEquiv]
      have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2
        (by decide) hc hconj
      rw [Representation.SU3.BinaryDegree.card_projective J hc hfixed]
      norm_num
    | suzuki m hm he =>
      obtain ⟨e⟩ := he
      have hd : ¬ 3 ∣ Nat.card S := by
        rw [Nat.card_congr e.toEquiv]
        exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega)
      have hz : primeRank 3 S = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
      omega
  · cases hm with
    | linear f hf hm =>
      by_cases hf2 : 2 ≤ f
      · exact signed_even_of_linear_three hf2 hm hsigned
      have hf1 : f = 1 := by omega
      subst f
      obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
      apply signed_even_of_small_order hsigned hmod
      rw [Nat.card_congr e.toEquiv]
      have he := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
      rw [hc] at he
      norm_num [Fin.prod_univ_succ] at he
      rw [he]
      norm_num
    | symplectic f hf hm => exact signed_even_of_symplectic (by omega) hm hsigned
    | g2 f hf hm => exact signed_even_of_g2 (by omega) hm hsigned
    | triality f hf hm => exact signed_even_of_triality hf hm hsigned
    | ree m hm he => exact signed_even_of_ree hm he hsigned
    | symplectic_derived he =>
      obtain ⟨e⟩ := he
      apply signed_even_of_small_order hsigned hmod
      rw [Nat.card_congr e.toEquiv,
        Nat.card_congr Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.toEquiv,
        nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    | g2_derived he =>
      obtain ⟨e⟩ := he
      apply signed_even_of_small_order hsigned hmod
      rw [Nat.card_congr e.toEquiv, Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
        Atlas.G2.BinaryException.card_H]
      norm_num
    | tits he =>
      obtain ⟨e⟩ := he
      apply signed_even_of_small_order hsigned hmod
      rw [Nat.card_congr e.toEquiv, Tits.parrottGroup_card]
      norm_num
  · rcases hn with rfl | rfl
    · obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
      apply signed_even_of_small_order hsigned hmod
      rw [Nat.card_congr e.toEquiv]
      have he := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
      rw [hc] at he
      norm_num [Fin.prod_univ_succ] at he
      rw [he]
      norm_num
    · exact signed_even_of_linear_five hm hsigned
end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
