module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Transport
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# Removing central covers in the sporadic pair calculation

A two-primary center is contained in the two-core. Thus the source hypothesis
O₂(Q) = 1 eliminates it and upgrades Q/Z(Q) ≃ G to Q ≃ G. The transported
Sylow pair then uses precisely the local action computation on the fixed
carrier. Finiteness, simplicity and perfectness of that carrier are inherited
from Q and the supplied quotient isomorphism.

`CentralCoverBound G n` states the universal earlier multiplier implication
for every finite quasisimple cover, with no local-pair assumptions. For the
four source cases the required bounds are n = 1 for M₂₃, M₂₄ and J₄, and
n = 2 for J₂. No multiplier calculation is asserted here.
`CarrierPairExclusion G` is the independent local computation still required:
it asks for actual invariant subgroups for every two-subgroup of the pair
automizer. The reduction theorems are explicitly conditional on that result;
neither its definition nor the cover reduction proves a sporadic exclusion.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), with the earlier I.1 multiplier input.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
universe u v
variable {Q : Type u} {G : Type v} [Group Q] [Group G]

/-- A normal two-primary center vanishes with the two-core. -/
theorem center_eq_bot_of_twoCore_eq_bot
    (hcore : pCore 2 Q = ⊥) (hcenter : IsPGroup 2 (center Q)) : center Q = ⊥ := by
  apply le_bot_iff.mp
  rw [← hcore]
  exact le_sSup ⟨inferInstance, hcenter⟩

/-- The actual ambient isomorphism after eliminating the central two-kernel. -/
noncomputable def centralQuotientEquiv
    (hcore : pCore 2 Q = ⊥) (hcenter : IsPGroup 2 (center Q))
    (e : (Q ⧸ center Q) ≃* G) : Q ≃* G :=
  ((QuotientGroup.quotientMulEquivOfEq
    (center_eq_bot_of_twoCore_eq_bot hcore hcenter)).trans
      QuotientGroup.quotientBot).symm.trans e

/-- The resulting isomorphism agrees with the given quotient isomorphism. -/
theorem centralQuotientEquiv_apply
    (hcore : pCore 2 Q = ⊥) (hcenter : IsPGroup 2 (center Q))
    (e : (Q ⧸ center Q) ≃* G) (x : Q) :
    centralQuotientEquiv hcore hcenter e x = e (QuotientGroup.mk' (center Q) x) := by
  rfl

/-- The remaining fixed-carrier calculation, allowing the source's inherited
finite nonabelian simplicity. This is a task contract, not an asserted fact. -/
def CarrierPairExclusion (G : Type v) [Group G] : Prop :=
  ∀ [Finite G] [IsSimpleGroup G] [Group.IsPerfect G]
    (S : Sylow 2 G) (R : Subgroup G), PairInput S R → PairReducible (S : Subgroup G) R

/-- The exact universal central-order consequence of a multiplier bound.
Unlike a local hypothesis, this applies to every finite quasisimple cover. -/
def CentralCoverBound (G : Type v) [Group G] (n : ℕ) : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q] [IsQuasisimple Q],
    Nonempty ((Q ⧸ center Q) ≃* G) → Nat.card (center Q) ∣ n

/-- Once the center is two-primary, the fixed-carrier action theorem applies upstairs. -/
theorem pairReducible_of_centralQuotient [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (e : (Q ⧸ center Q) ≃* G) (hcenter : IsPGroup 2 (center Q))
    (hmodel : CarrierPairExclusion G) : PairReducible (S : Subgroup Q) R := by
  let f := centralQuotientEquiv h.twoCore hcenter e
  let _ : Finite G := Finite.of_equiv Q f.toEquiv
  let _ : IsQuasisimple Q := h.quasisimple
  let _ : IsQuasisimple G := IsQuasisimple.of_mulEquiv f
  let _ : IsSimpleGroup G := (MulEquiv.isSimpleGroup_congr e).mp h.quasisimple.simple
  exact pairReducible_of_equiv f h (fun S' R' h' => hmodel S' R' h')

/-- A universal two-power multiplier bound discharges the center condition. -/
theorem pairReducible_of_centralCoverBound [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (e : (Q ⧸ center Q) ≃* G) {k : ℕ}
    (hbound : CentralCoverBound.{u, v} G (2 ^ k))
    (hmodel : CarrierPairExclusion G) : PairReducible (S : Subgroup Q) R := by
  let _ := h.quasisimple
  exact pairReducible_of_centralQuotient h e
    (IsPGroup.of_card_dvd_pow (hbound Q ⟨e⟩)) hmodel

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
