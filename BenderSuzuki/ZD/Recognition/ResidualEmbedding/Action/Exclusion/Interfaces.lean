module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Basic

/-!
# Source obligations for the distinguished Section 7 argument

These predicates are proof boundaries, not established source theorems.
Corollary 6.4 follows from generation in Proposition 6.3 and the ZJ theorem.
The theta chain comes from Proposition 7.4 and Lemmas 7.5--7.7. The final
configuration is constructed by maximal normalizers, (7D)--(7G), and Lemmas
7.10--7.11; Corollary 6.4 then excludes it.

The odd core is `O_{2'}`, never a residual. Sylow subgroups of that core are
mapped through both subtype maps. All points are actual cosets, and the
prime and distinguished involution belong to the original (6A) witness.

Source: GLS, Volume 4, Chapter 2, Corollary 6.4 and Section 7.
-/

noncomputable section

namespace BenderSuzuki.ZD

open PFAppendixIII PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The full source Corollary 6.4 conclusion for a distinguished witness.
Its proof, including generation, remains a separate obligation. -/
@[expose] public def ActionCorollary64 (d : ActionCounterexample Z M) : Prop :=
  ∀ beta : G ⧸ M, beta ∈ d.toTheorem4bSixA.kFixedPoints →
    beta ≠ QuotientGroup.mk 1 →
    d.z ∈ Subgroup.normalizer
      (corollary64Theta d.p (theorem4bSection7D M beta) : Set G) →
    corollary64Theta d.p (theorem4bSection7D M beta) = ⊥ ∧
      ∀ R : Subgroup G, IsPGroup d.p R → R ≤ theorem4bSection7D M beta →
        (∃ P₀ : Sylow d.p (twoPrimeCore (theorem4bSection7D M beta)),
          (((P₀ : Subgroup (twoPrimeCore (theorem4bSection7D M beta))).map
            (twoPrimeCore (theorem4bSection7D M beta)).subtype).map
            (theorem4bSection7D M beta).subtype) ≤ R) →
        d.z ∉ Subgroup.normalizer (corollary64Z ⟨d.p, d.hp⟩ R : Set G) ∧
        d.z ∉ Subgroup.normalizer (R : Set G)

/-- The precise output of the theta-chain construction, before applying
Corollary 6.4. No oddness of either two-point stabilizer is assumed. -/
@[expose] public def ActionThetaChain (d : ActionCounterexample Z M) : Prop :=
  ∃ beta : G ⧸ M, beta ∈ d.toTheorem4bSixA.kFixedPoints ∧
    beta ≠ QuotientGroup.mk 1 ∧
    corollary64Theta d.p (theorem4bSection7F d.z beta) ≤
      corollary64Theta d.p (theorem4bSection7E M d.z beta) ∧
    corollary64Theta d.p (theorem4bSection7E M d.z beta) ≤
      corollary64Theta d.p (theorem4bSection7D M beta) ∧
    Nat.card (corollary64Theta d.p (theorem4bSection7D M beta)) ≤
      Nat.card (corollary64Theta d.p (theorem4bSection7F d.z beta))

/-- The concrete output of the final maximal-normalizer construction:
the conjugated subgroup `R^x` is Sylow in `D` and its characteristic
`Omega₁(Z(J(R^x)))` is normalized by `z`. -/
@[expose] public def ActionFinalConfiguration (d : ActionCounterexample Z M) : Prop :=
  ∃ beta : G ⧸ M, beta ∈ d.toTheorem4bSixA.kFixedPoints ∧
    beta ≠ QuotientGroup.mk 1 ∧
    corollary64Theta d.p (theorem4bSection7D M beta) = ⊥ ∧
    ∃ R : Subgroup G, theorem4bIsSylowSubgroupOf d.p R (theorem4bSection7D M beta) ∧
      d.z ∈ Subgroup.normalizer (corollary64Z ⟨d.p, d.hp⟩ R : Set G)

end BenderSuzuki.ZD
