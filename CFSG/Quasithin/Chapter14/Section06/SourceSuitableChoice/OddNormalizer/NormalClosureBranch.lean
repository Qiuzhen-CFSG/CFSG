module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.CubicNormal
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.SolvableBranch

/-!
# The normal-residual branch without a solvability assumption

If the original residual is Mc-normal, the cubic case is solvable by the
normal elementary nine argument and Suzuki exclusion. The global maximal
prime then gives the {2,3}-order assertion of 14.6.14(1). The established
exchanged-factor normalizer and literal support construction now supply
14.6.16 and the actual suitable involution in this entire branch.

Only the normal-residual branch condition is imposed; solvability, prime
support, normalizer equality and suitability are derived. The original
primitive and exchanged data remain with qt-e-quintic-recognition and
qt-e-14612-singleton; p=3 remains with qt-e-14615-quintic-exclusion.
The strict closure and parabolic branch remain with the same source owner,
qt-e-suitable-odd-normalizer, and final suitable-choice assembly remains
with qt-e-suitable-existence.

Source: Aschbacher--Smith 14.6.14(1), 14.6.16 and 14.6.17, pp.1033--1036.
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

/-- The complete first alternative follows from the normal-residual branch condition. -/
theorem source_first_closure_case_of_normal_residual
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hclosure : residualClosure H Mc = residual H) :
    residualClosure H Mc = residual H ∧
      (p = 3 → ∀ q : ℕ, q.Prime → q ∣ Nat.card Mc → q = 2 ∨ q = 3) := by
  refine ⟨hclosure,fun hp => ?_⟩
  have hs := source_solvable_of_normal_cubic_residual
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hp hmax hclosure
  exact (source_first_closure_case_of_solvable
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax hs).2 hp

/-- Original 14.6.14 in the complete normal-residual branch. -/
theorem source_closure_alternatives_of_normal_residual
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hclosure : residualClosure H Mc = residual H) :
    SourceClosureAlternatives (T : Subgroup G) Mc H p :=
  Or.inl (source_first_closure_case_of_normal_residual
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax hclosure)

/-- Both original 14.6.16 conclusions, with the first closure case derived. -/
theorem source_normalizer_of_normal_residual
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hp : p = 3) (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hclosure : residualClosure H Mc = residual H) :
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    S.relIndex (T : Subgroup G) = 2 ∧ Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) := by
  obtain ⟨he,hpr⟩ := source_first_closure_case_of_normal_residual
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax hclosure
  exact source_normalizer_first_closure_case
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 d hp hmax he (hpr hp)

/-- The actual support supplies a suitable involution in the normal-residual branch. -/
theorem source_exists_suitable_of_normal_residual
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hp : p = 3) (hmax : MaximalOddPrime (T : Subgroup G) M p)
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
  obtain ⟨he,hpr⟩ := source_first_closure_case_of_normal_residual
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax hclosure
  exact source_exists_suitable_first_closure_case
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hp hmax he (hpr hp)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
