module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.CubicClosureChoice
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Normalizer.Parabolic.Invariant
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.Source

/-!
# Complete cubic closure, normalizer and suitable-involution assembly

The normal-residual and exchanged-component branches are already checked.
The invariant PSL₄(2)/PSL₅(2) branches now follow from the original core
interval and the literal automorphism quotient. Thus the full original
setup at p=3 proves the closure alternatives, index two and N_Mc(N_T(H₁))=T.

The suitable-involution theorem applies these results to the original
first support. Its Fitting containment, strict central-line containment,
normalization, separation and absence of fixed vectors are all discharged
by their source producers. It retains the original inverse-conjugation
movement condition and every local and ambient Sylow conclusion.

For an arbitrary chosen maximal odd prime, the last two theorems combine
these proofs with original 14.6.15, keeping 14.6.14 explicit. The remaining
PSL₂(16) full-image branch must still discharge that premise; this module
does not claim the unrestricted source family is complete. Earlier 14.6.12
and 14.6.13 inputs retain their existing producers, and qt-e-suitable-existence
owns the final source choice.

Source: Aschbacher--Smith, original 14.6.14--17, printed pp.1033--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))


include hG hempty hM hunique hmany hcard e hab hH

/-- Original 14.6.14 in the cubic case, with every closure alternative established. -/
theorem source_cubic_closure_alternatives
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M 3) :
    SourceClosureAlternatives (T : Subgroup G) Mc H 3 := by
  rcases source_closure_alternatives_or_sixteen
      hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 hprim d hmax with hc | ⟨hp,_⟩
  · exact hc
  · norm_num at hp

/-- Original 14.6.16 at p=3, with every closure and parabolic premise discharged. -/
theorem source_normalizer_cubic
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M 3) :
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    S.relIndex (T : Subgroup G) = 2 ∧ Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) := by
  rcases source_normalizer_or_invariant_cubic_closure
      hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d hmax with
    hs | ⟨_,n,hn,⟨E⟩⟩
  · exact hs
  · exact source_normalizer_invariant_closure
      hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 d hn E

/-- The original first support contains a suitable involution in every cubic closure case. -/
theorem source_exists_suitable_cubic
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M 3) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    ∃ u ∈ firstSupport a H1, u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = S ∧
      ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G) ∧
      (∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (H ⊓ centralizer ({u} : Set G)) ∧
      normalizer (((T : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) = S ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (centralizer ({u} : Set G)) ∧
      ¬∃ S' : Sylow 2 G, (S' : Subgroup G) ≤ centralizer ({u} : Set G) := by
  have hnorm := source_normalizer_cubic
    hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d hmax
  obtain ⟨hWU,hZW,hKW,hSW,hi,hsep,hff⟩ := source_exchanged_support_premises
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 d
  have hK := source_residual_le_fittingPreimage
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 hprim d
  exact source_exists_suitable_of_fixed_free_support
    hG T hempty hM hunique hmany hcard e hab H hH (residual H) (firstSupport a H1)
      ((T : Subgroup G) ⊓ normalizer (H1 : Set G)) hK hWU hZW hKW hSW inf_le_left hi hnorm.2 hsep hff

/-- Original 14.6.15--16 assembled once the earlier closure classification is supplied.
The closure premise still requires the PSL₂(16) full-image branch. -/
theorem source_prime_and_normalizer_of_closure_alternatives
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hc : SourceClosureAlternatives (T : Subgroup G) Mc H p) :
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    p = 3 ∧ S.relIndex (T : Subgroup G) = 2 ∧
      Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) := by
  have hp := source_lemma_14_6_15
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim hmax d hc
  subst p
  exact ⟨rfl,source_normalizer_cubic
    hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d hmax⟩

/-- The literal suitable-involution consumer of the full 14.6.14 alternatives. -/
theorem source_exists_suitable_of_closure_alternatives
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hc : SourceClosureAlternatives (T : Subgroup G) Mc H p) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    ∃ u ∈ firstSupport a H1, u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = S ∧
      ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G) ∧
      (∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (H ⊓ centralizer ({u} : Set G)) ∧
      normalizer (((T : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) = S ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (centralizer ({u} : Set G)) ∧
      ¬∃ S' : Sylow 2 G, (S' : Subgroup G) ≤ centralizer ({u} : Set G) := by
  have hp := source_lemma_14_6_15
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim hmax d hc
  subst p
  exact source_exists_suitable_cubic
    hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d hmax

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
