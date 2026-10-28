module
public import CFSG.KnownSimple.PrimeToFifteen
public import CFSG.Quasithin.Chapter10.SourceA5OriginalCentralizerFaithfulness

/-!
# Complete catalogue discharge for the original A₅ centralizer

The full known-simple prime-to-fifteen solvability theorem now discharges
solvability of the literal centralizer C_Q(J). The original faithful binary
representation and its quotient/action markings are retained. In particular,
the resulting starred-offender conjugation theorem has no separate solvability
or catalogue-divisibility premise. The earlier minimality and cubic-bound
source inputs remain explicit exactly as in the existing consumer.

Source: Aschbacher–Smith D.2.13 and D.3.21, in the Chapter 10 A₅ passage.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

attribute [local instance] centralizerFullElementary

theorem source_a5_original_actor_centralizer_solvable
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    Group.IsSolvable (centralizer (J : Set
      (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))) :=
  source_a5_original_actor_centralizer_solvable_of_prime_to_fifteen D
    KnownSimple.isSolvable_of_coprime_three_five e hn ht htn

theorem source_minimal_full_quotient_starred_conjugation
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    let _ : J.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    ∃ ρ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
      (Additive D.fullCentralQuotient),
      Function.Injective ρ ∧ ρ.IsIrreducible ∧ cubicRatio ρ ≤ 2 ∧
      (∀ A ∈ ChapterD.QhatStar ρ,
        Function.Injective ((MulAut.conjNormal :
          (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)) →* MulAut J).comp A.subtype)) ∧
      (∀ (m : D.maximalLocal) (v : D.fullModule),
        ρ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
          Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
                v.property⟩)) :=
  source_minimal_full_quotient_starred_conjugation_of_prime_to_fifteen D e
    KnownSimple.isSolvable_of_coprime_three_five hD hbound hn ht htn

end CFSG.Quasithin.Chapter10
