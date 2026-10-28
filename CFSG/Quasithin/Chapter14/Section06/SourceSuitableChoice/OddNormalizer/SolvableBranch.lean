module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.PrimeBounds
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.Orbit
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.NormalBranch

/-!
# The complete suitable-involution application when Mc is solvable

Component detection would put a nontrivial perfect subgroup inside Mc if
the residual closure were strict. Solvability therefore forces Kz=O²(H).
The actual maximal-prime bound proves the first alternative of 14.6.14,
including its {2,3}-order conclusion at p=3. The established normalizer
argument and support construction then produce the literal suitable
involution without a closure, prime-support, or normalizer premise.

Solvability of Mc is the branch hypothesis, not a consequence asserted in
this module. The original normal-closure branch still needs its Suzuki
exclusion to derive solvability. The primitive/14.6.12 inputs remain with
qt-e-14612-singleton and qt-e-quintic-recognition; p=3 remains with
qt-e-14615-quintic-exclusion. The nonsolvable cases and unconditional
assembly remain with qt-e-suitable-odd-normalizer and its parent
qt-e-suitable-existence.

Source: Aschbacher--Smith 14.6.14, 14.6.16 and the first paragraph of
14.6.17, printed pp.1032--1036.
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

/-- Solvability rules out the detected relative component of a strict closure. -/
theorem source_closure_eq_residual_of_solvable
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hs : Group.IsSolvable Mc) : residualClosure H Mc = residual H := by
  by_contra hne
  obtain ⟨P,L,_hi,hL,_⟩ := source_strict_closure_component_orbit
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hne
  let := hs
  exact hL.mem.2.not_isSolvable inferInstance

/-- The first source alternative follows from solvability and the actual maximal prime. -/
theorem source_first_closure_case_of_solvable
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hs : Group.IsSolvable Mc) :
    residualClosure H Mc = residual H ∧
      (p = 3 → ∀ q : ℕ, q.Prime → q ∣ Nat.card Mc → q = 2 ∨ q = 3) := by
  refine ⟨source_closure_eq_residual_of_solvable
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hs,?_⟩
  intro hp q hq hd
  have hHMc : H ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hunique)
  rcases source_solvable_overgroup_prime_bound hG T hunique H hH d.prime hmax
    Mc hHMc le_rfl hs q hq hd with h | h | ⟨h,_⟩
  · exact Or.inl h
  · exact Or.inr h
  · omega

/-- The full four-way target holds in the solvable branch by its proved first case. -/
theorem source_closure_alternatives_of_solvable
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hs : Group.IsSolvable Mc) : SourceClosureAlternatives (T : Subgroup G) Mc H p :=
  Or.inl (source_first_closure_case_of_solvable
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax hs)

/-- Both original normalizer conclusions in the solvable Mc branch. -/
theorem source_normalizer_of_solvable
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hp : p = 3) (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hs : Group.IsSolvable Mc) :
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    S.relIndex (T : Subgroup G) = 2 ∧ Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) := by
  obtain ⟨he,hpr⟩ := source_first_closure_case_of_solvable
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax hs
  exact source_normalizer_first_closure_case
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 d hp hmax he (hpr hp)

/-- The actual support supplies a suitable involution in the solvable Mc branch. -/
theorem source_exists_suitable_of_solvable
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hp : p = 3) (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hs : Group.IsSolvable Mc) :
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
  obtain ⟨he,hpr⟩ := source_first_closure_case_of_solvable
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax hs
  exact source_exists_suitable_first_closure_case
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hp hmax he (hpr hp)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
