module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.NormalClosureBranch
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.Source

/-!
# Original normal-residual normalizer and suitable choice

In the normal-residual branch, the checked closure theorem supplies
14.6.14(1) on the same H and Mc. The independent source 14.6.15 then
proves p=3, so the solvable-closure normalizer and fixed-free support
construction apply without an extra prime-three premise. The resulting
involution lies in the actual first support and has the original local
and ambient Sylow conclusions, with conjugation by t⁻¹ retained.

The primitive input and the earlier exchanged factors (including their
factor-join index) retain qt-e-quintic-recognition and
qt-e-14612-singleton. The 14.6.15 theorem is the checked output of
qt-e-14615-quintic-exclusion. Strict closure and parabolic assembly remain
with qt-e-suitable-odd-normalizer; qt-e-suitable-existence retains final
suitable-choice assembly. No suitability or normalizer conclusion is
assumed.

Source: Aschbacher--Smith 14.6.14(1)--17, printed pp.1033--1036.
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

/-- Both source 14.6.16 conclusions in the normal-residual branch, with
the prime-three input discharged by original 14.6.15. -/
theorem source_normalizer_of_normal_residual_source
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hclosure : residualClosure H Mc = residual H) :
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    S.relIndex (T : Subgroup G) = 2 ∧ Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) := by
  have hc := source_closure_alternatives_of_normal_residual
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax hclosure
  have hp := source_lemma_14_6_15
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim hmax d hc
  exact source_normalizer_of_normal_residual
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hp hmax hclosure

/-- The actual suitable involution in the normal-residual branch, with
its source prime, normalizer and support premises all discharged. -/
theorem source_exists_suitable_of_normal_residual_source
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hclosure : residualClosure H Mc = residual H) :
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
  have hc := source_closure_alternatives_of_normal_residual
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax hclosure
  have hp := source_lemma_14_6_15
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim hmax d hc
  exact source_exists_suitable_of_normal_residual
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hp hmax hclosure

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
