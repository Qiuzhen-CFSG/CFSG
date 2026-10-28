module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Normalizer.Solvable
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice

/-!
# Suitable involutions in the normal closure branch

Apply the normalizer equality for the first 14.6.14 case to the literal
exchanged support U_H,1. Fitting containment and the checked support
geometry discharge every premise of the fixed-free suitable-vector
construction, retaining conjugation by t⁻¹ and the original quotient map.

This is a complete application for this branch, conditional on p=3 and
the first closure alternative. It does not establish the full closure
classification. The primitive and exchanged-factor inputs retain the
qt-e-14612-singleton and qt-e-quintic-recognition producers. Their final
discharge, the other closure branches and source assembly remain with
qt-e-suitable-odd-normalizer and its parent qt-e-suitable-existence.

Source: Aschbacher--Smith 14.6.16 and the first paragraph of 14.6.17,
printed pp.1035--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
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

/-- The actual suitable-involution application in the normal closure branch.
The earlier primitive and exchanged-factor inputs retain their original
producers; p=3 and the first 14.6.14 case are explicit branch premises.
Fitting containment, all support premises and N_Mc(S)=T are discharged here. -/
theorem source_exists_suitable_first_closure_case
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hp : p = 3) (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hclosure : residualClosure H Mc = residual H)
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ Nat.card Mc → q = 2 ∨ q = 3) :
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
  obtain ⟨hWU,hZW,hKW,hSW,hi,hsep,hff⟩ := source_exchanged_support_premises
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 d
  have hK := source_residual_le_fittingPreimage
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d
  have hn := (source_normalizer_first_closure_case
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 d hp hmax hclosure hprimes).2
  exact source_exists_suitable_of_fixed_free_support
    hG T hempty hM hunique hmany hcard e hab H hH (residual H) (firstSupport a H1)
      ((T : Subgroup G) ⊓ normalizer (H1 : Set G)) hK hWU hZW hKW hSW inf_le_left hi hn hsep hff

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
