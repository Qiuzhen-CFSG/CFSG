module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.Pair
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.Evenness
public import Theory.GroupTheory.CyclicSylowNormalComplement
public import FeitThompson.BGsection1.PLengthLemmas

/-!
# Normal two-complements from the local cyclic Sylow conclusion

GLS, Volume 4, Chapter 2, Corollary 16.6(e) concludes that a subgroup
with trivial distinguished closure has cyclic Sylow two-subgroups and a
normal two-complement. Burnside transfer proves the normal-complement
part from the cyclic Sylow part, including the odd-order case.

We also specialize this implication to the two-point stabilizer and
transport its normal complement to the internal copy in `M`. Its local
circle is trivial by product disconnection, and its even order has been
proved from failure of strong embedding and double transitivity.
The Section 16 centralizer analysis needed to establish the cyclic Sylow
premise is not asserted here; the assembly below is explicitly conditional.
-/

namespace BenderSuzuki.ZD

open Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Burnside transfer supplies a normal two-complement once the Sylow
 two-subgroups of the local group are known to be cyclic. Normality is
 inside `Y`. This does not assert that local Sylow subgroups are cyclic. -/
public theorem local_normalComplement_of_cyclicSylow (Y : Subgroup G)
    (hcyc : ∀ S : Sylow 2 Y, IsCyclic S) : HasNormalPComplement 2 Y := by
  classical
  by_cases heven : 2 ∣ Nat.card Y
  · let S : Sylow 2 Y := Classical.choice inferInstance
    exact External.Suzuki.V.suzuki_ch5_theorem_2_10_corollary_1
      S ((Nat.minFac_eq_two_iff _).mpr heven) (hcyc S)
  · refine ⟨⊤, inferInstance, ?_, ?_⟩
    · simpa using Nat.prime_two.coprime_iff_not_dvd.mpr heven
    · have : Subsingleton (Y ⧸ (⊤ : Subgroup Y)) := QuotientGroup.subsingleton_quotient_top
      exact IsPGroup.of_card (n := 0) (by simp)

/-- Conditional Section 16 assembly for the internal two-point stabilizer.
The circle premise is proved by product disconnection. The source's cyclic
Sylow conclusion remains an explicit premise, to be discharged by the
centralizer and involution-fusion analysis. -/
public theorem residualPairIn_normalComplement_of_local_cyclicSylow
    (h : IsProductDisconnected Z M) (ha : ResidualAction Z M)
    (hn : ¬ IsStronglyEmbedded M)
    (hcyc : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      ∀ S : Sylow 2 Y, IsCyclic S) {t : G} (ht : t ∉ M) :
    HasNormalPComplement 2 (residualPairIn M t) ∧
      2 ∣ Nat.card (residualPairIn M t) := by
  refine ⟨?_, residualPairIn_even h ha hn ht⟩
  apply hasNormalPComplement_of_equiv 2 (residualPairInEquiv M t).symm
  exact local_normalComplement_of_cyclicSylow _
    (hcyc _ (residualPairStabilizer_localClosure_eq_bot h ht))

end BenderSuzuki.ZD
