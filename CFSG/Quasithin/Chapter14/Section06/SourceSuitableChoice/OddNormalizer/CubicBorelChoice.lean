module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.CubicBorelSource
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.SixteenChoice

/-!
# The literal suitable-choice endpoint with a constructed cubic Borel

The existing endpoint supplies all normalizer and suitable-involution
conclusions outside the small PSL₂(16) cubic-image case. In that case,
construct the actual cubic Borel subgroup, retain its placement in the
same residual closure, and select a minimal outside subgroup with a
primitive cubic residual. The original M,Mc,H,T and maximal prime remain.

This discharges Borel existence and the primitive premise for a fresh
application of earlier 14.6.12. Its exchanged factors and index must still
come from qt-e-14612-singleton; comparing their action with the literal
cubic detector remains with qt-e-suitable-odd-normalizer. Original 14.6.15
is not used to establish those earlier premises. Final suitable-choice
assembly remains with qt-e-suitable-existence.

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
/-- Earlier 14.6.12 on the selected primitive subgroup gives the primitive
cubic Borel join and its actual quotient of order 72. This application uses
neither maximal-prime conclusions nor the later 14.6.15 implication. -/
theorem cubic_borel_primitive_quotient_of_exchanged_factors
    (T : Sylow 2 G) (M X J U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction J U Z) (J0 J1 J2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 J0 J1 J2)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hc : Nat.card (X ⧸ pCore 2 X) = 9)
    (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJC : J ≤ X ⊔ (T : Subgroup G)) (hprim : PrimitiveResidual J 3) :
    PrimitiveResidual (X ⊔ (T : Subgroup G)) 3 ∧
      Nat.card ((X ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G)) = 72 := by
  have hj := cubic_borel_eq_of_exchanged_factors T X J U Z a J0 J1 J2 d hn hc hJ hJC
  rw [←hj]
  exact ⟨hprim, by simpa using
    OddCriticalPair.exchanged_actor_card a (T : Subgroup G) 3 J0 J1 J2 d⟩

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

/-- The sole remaining suitable-choice branch now has a constructed
cubic Borel and primitive auxiliary subgroup for earlier 14.6.12. -/
theorem source_prime_normalizer_suitable_or_primitive_cubic_borel
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
        SmallSixteenCubicImage Mc (residualClosure H Mc) L s ∧
        CubicBorelOutside (T : Subgroup G) M Mc H (residualClosure H Mc)) := by
  rcases source_prime_normalizer_suitable_or_small_cubic_image
      hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax with
    hdone | ⟨hp,L,s,hL,hcomp,hq,hs,hsn,hprod,hgen,hr,hr3,hlayer,hsmall⟩
  · exact Or.inl hdone
  · have hB := source_small_sixteen_cubic_borel hG T hempty hM hunique hmany hcard e hab
      H hH (hp ▸ hprim) (residualClosure H Mc) L s hr3 hlayer hsmall
    exact Or.inr ⟨hp,L,s,hL,hcomp,hq,hs,hsn,hprod,hgen,hr,hr3,hlayer,hsmall,hB⟩
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
