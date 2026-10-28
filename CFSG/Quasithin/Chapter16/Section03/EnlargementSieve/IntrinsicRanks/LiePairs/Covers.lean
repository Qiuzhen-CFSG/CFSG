module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Contracts
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Geometry
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Rank
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.Bounds

/-!
# The permitted PSL₃(4) covers in the Lie-pair sieve

E1 identifies the center of the actual component with its two-core. The
PSL₃(4) clause of E2(i) makes its Frattini subgroup trivial, hence its center
elementary abelian. The first assertion of I.2.2(3b), retained explicitly
as an earlier source input, then supplies involutory lifts. The identity
coset and the centerless case are handled separately. The central-cover
rank formula and the enlargement inequality now apply without assuming
any numerical assertion about a cover.

Source: Aschbacher–Smith, I.2.2(3b), printed p.409; E1–E2 and 16.1.2,
p.1170; and the ordinary Lie-pair paragraph of 16.3.9, p.1180.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs
universe u

/-- Exactly the involution-lifting assertion of I.2.2(3b), with its original
quasisimplicity, nontrivial center, two-group and Frattini hypotheses.
This is an earlier theorem input, not a rank assertion. -/
def PSLThreeFourCoverLifting : Prop :=
  ∀ (M : Type u) (_ : Group M) (_ : Finite M) (_ : IsQuasisimple M),
    center M ≠ ⊥ → IsPGroup 2 (center M) →
    ClassicalGroup.IsPSL (M ⧸ center M) 3 4 → frattini (center M) = ⊥ →
    ∀ x : M ⧸ center M, orderOf x = 2 →
      ∃ y : M, QuotientGroup.mk' (center M) y = x ∧ orderOf y = 2

variable {G : Type u} [Group G] [Finite G] {t : G} {K : Subgroup G}

/-- Transport the actual PSL quotient across the E1 equality Z(K)=O₂(K). -/
theorem pslThreeFour_twoCore_model
    (he : HasEvenTypeCentralizers G) (ht : orderOf t = 2)
    (hK : IsCentralizerComponent t K)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ center K) 3 4) :
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 :=
  hmodel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq
    (he.component_center_eq_twoCore ht hK).symm)

/-- E2(i) gives the elementary center needed by the lifting formula. -/
theorem pslThreeFour_center_elementary
    (he : HasEvenTypeCentralizers G) (ht : orderOf t = 2)
    (hK : IsCentralizerComponent t K) (hLie : IsEvenTypeLieComponent K)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ center K) 3 4) :
    IsElementaryAbelian 2 (center K) := by
  have hphi := hLie.2.2.2 (pslThreeFour_twoCore_model he ht hK hmodel)
  rw [he.component_center_eq_twoCore ht hK]
  let : Fact (IsPGroup 2 (pCore 2 K)) := ⟨pCore_isPGroup⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi

/-- The source talks about elements of order two. The rank formula also
needs the identity coset, and does not require a nontrivial center. -/
theorem pslThreeFour_square_lifts
    (source : PSLThreeFourCoverLifting.{u})
    (he : HasEvenTypeCentralizers G) (ht : orderOf t = 2)
    (hK : IsCentralizerComponent t K) (hLie : IsEvenTypeLieComponent K)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ center K) 3 4) :
    ∀ x : K ⧸ center K, x ^ 2 = 1 →
      ∃ y : K, QuotientGroup.mk' (center K) y = x ∧ y ^ 2 = 1 := by
  intro x hx
  by_cases hZ : center K = ⊥
  · obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center K) x
    refine ⟨y, hy, ?_⟩
    have hm : y ^ 2 ∈ center K := (QuotientGroup.eq_one_iff _).mp (by
      change QuotientGroup.mk' (center K) (y ^ 2) = 1
      rw [map_pow, hy, hx])
    simpa only [hZ, mem_bot] using hm
  · by_cases hx1 : x = 1
    · subst x
      exact ⟨1, map_one _, one_pow _⟩
    · have hp : IsPGroup 2 (center K) := by
        rw [he.component_center_eq_twoCore ht hK]
        exact pCore_isPGroup
      have hphi : frattini (center K) = ⊥ := by
        rw [he.component_center_eq_twoCore ht hK]
        exact hLie.2.2.2 (pslThreeFour_twoCore_model he ht hK hmodel)
      obtain ⟨y, hy, hy2⟩ := source K inferInstance inferInstance hK.quasisimple
        hZ hp hmodel hphi x (orderOf_eq_prime hx hx1)
      exact ⟨y, hy, hy2 ▸ pow_orderOf_eq_one y⟩

/-- The full numerical cover formula is derived, with its center size
retained rather than built into an assumed rank comparison. -/
theorem pslThreeFour_cover_rank
    (source : PSLThreeFourCoverLifting.{u})
    (he : HasEvenTypeCentralizers G) (ht : orderOf t = 2)
    (hK : IsCentralizerComponent t K) (hLie : IsEvenTypeLieComponent K)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ center K) 3 4) :
    ∃ n : ℕ, Nat.card (center K) = 2 ^ n ∧
      primeRank 2 K = primeRank 2 (K ⧸ center K) + n := by
  let := pslThreeFour_center_elementary he ht hK hLie hmodel
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 (center K)).exists_card_eq
  exact ⟨n, hn, two_rank_eq_quotient_add_of_central_involution_lifts
    (center K) le_rfl hn (pslThreeFour_square_lifts source he ht hK hLie hmodel)⟩

variable {T : Sylow 2 G} {z : G} {L : Subgroup G}

/-- The extra rank in K⟨t⟩ follows for the permitted covers on either side
of the inside/outside dichotomy. -/
theorem pslThreeFour_quotient_rank_succ_le
    (source : PSLThreeFourCoverLifting.{u})
    (he : HasEvenTypeCentralizers G) (h : TerminalCounterexample T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hLie : IsEvenTypeLieComponent (enlargement t L))
    (hmodel : ClassicalGroup.IsPSL
      (enlargement t L ⧸ center (enlargement t L)) 3 4) :
    primeRank 2 (enlargement t L ⧸ center (enlargement t L)) + 1 ≤
      primeRank 2 (enlargement t L ⊔ zpowers t : Subgroup G) := by
  let := pslThreeFour_center_elementary he h.involution hK hLie hmodel
  exact quotient_rank_succ_le h
    (pslThreeFour_square_lifts source he h.involution hK hLie hmodel)

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs
