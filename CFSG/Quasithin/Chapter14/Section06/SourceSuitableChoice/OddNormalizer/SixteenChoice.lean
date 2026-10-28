module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.SixteenSource
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.CubicChoice

/-!
# Suitable-involution assembly after the cubic-torus reduction

All previously proved closure branches yield p=3, the index-two subgroup
S=N_T(H₁), Mc ∩ N_G(S)=T, and a suitable involution in the original first
support. The full PSL₂(16) branch now follows from order eight of its actual
cubic torus action, so the only surviving alternative is the same marked
component square with cubic image of order at most four.

The actual first support, all centralizer/Sylow conclusions and movement
by the inverse conjugator are retained. No suitability premise is added.
The cubic Borel subgroup and its earlier 14.6.12 application must still
exclude the second alternative; this is checked progress, not completion
of original 14.6.14--16. The earlier 14.6.12 and 14.6.13 producers and final
suitable-choice owner retain their original obligations.

Source: Aschbacher--Smith 14.6.14--17, printed pp.1033--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
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

/-- All original normalizer and suitable-involution conclusions hold unless
the remaining PSL₂(16) action has cubic image of order at most four.
The earlier cubic Borel argument must still exclude that explicit branch. -/
theorem source_prime_normalizer_suitable_or_small_cubic_image
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    (p = 3 ∧ S.relIndex (T : Subgroup G) = 2 ∧
      Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) ∧
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
      ¬∃ S' : Sylow 2 G, (S' : Subgroup G) ≤ centralizer ({u} : Set G)) ∨
      (p = 5 ∧ ∃ (L : Subgroup G) (s : Mc), L ≤ Mc ∧
        (L.subgroupOf Mc).IsCComponent ∧ IsQuasisimple (XiQuotient L) ∧
        (s : G) ∈ (T : Subgroup G) ∧ (s : G) ∉ normalizer (L : Set G) ∧
        (residualClosure H Mc : Set G) = (L : Set G) *
          (L.map (MulAut.conj (s : G)⁻¹).toMonoidHom : Set G) ∧
        Mc = residualClosure H Mc ⊔ (T : Subgroup G) ∧
        residualClosure H Mc = (primeToResidual p Mc).map Mc.subtype ∧
        residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
        StrictClosureLayer Mc (residualClosure H Mc) ∧
        SmallSixteenCubicImage Mc (residualClosure H Mc) L s) := by
  rcases source_closure_alternatives_or_small_sixteen_cubic_image
      hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax with hc | hsmall
  · obtain ⟨hp,hi,hn⟩ := source_prime_and_normalizer_of_closure_alternatives
      hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax hc
    exact Or.inl ⟨hp,hi,hn,source_exists_suitable_of_closure_alternatives
      hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax hc⟩
  · exact Or.inr hsmall

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
