module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.Reduction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.PSL3.QuadraticThreeSylow

/-!+# The nonsplit and elementary branches of the odd PSL₃ pair sieve

For field order congruent to −1 modulo three, the concrete quadratic torus
gives cyclic Sylow three-subgroups of the central quotient. The central-image
reduction therefore excludes every quasisimple cover, without a multiplier
assumption.

At field order three the elementary complement is the required plane. The
only cover input used here is the universal trivial-center implication of
I.1.3 for PSL₃(3), independent of the pair and its action. It is stated as an
explicit parameter, not asserted. The extraspecial local-core calculation
and the split congruence case remain separate obligations.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528), and I.1.3, printed p.407.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- The universal cover consequence of I.1.3 at PSL₃(3). This is an explicit
earlier theorem input, with no dependence on a Sylow pair or local action. -/
def TrivialThreeCover : Prop :=
  ∀ (K : Type u) [Group K] [Finite K], IsQuasisimple K →
    ClassicalGroup.IsPSL (K ⧸ center K) 3 3 → center K = ⊥

/-- The cyclic-Sylow exclusion includes every central cover. -/
theorem reducible_of_mod_three_eq_two {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 p) :
    PairReducible (S : Subgroup Q) R := by
  apply reducible_of_cyclic_three_sylow h
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fintype F := Fintype.ofFinite F
  let _ : CharP F p := charP_of_card_eq_prime
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  intro U
  let V := U.mapSurjective (f := e.toMonoidHom) e.surjective
  have hc : IsCyclic V := Matrix.PSL3.QuadraticThreeSylow.sylow_three_isCyclic F p
    (by simpa only [hF] using hmod) V
  exact (U.toSubgroup.equivMapOfInjective e.toMonoidHom e.injective).isCyclic.mpr hc

omit [Finite Q] in
/-- A trivial central kernel recovers the actual model on the covering group. -/
theorem model_of_center_eq_bot (hz : center Q = ⊥)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 3) : LinearThreeModel 3 Q := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let q := QuotientGroup.mk' (center Q)
  have hq : Function.Injective q := by
    apply q.ker_eq_bot_iff.mp
    simpa only [q, QuotientGroup.ker_mk'] using hz
  let eQ : Q ≃* (Q ⧸ center Q) :=
    MulEquiv.ofBijective q ⟨hq, QuotientGroup.mk'_surjective _⟩
  exact Or.inr ⟨F, inferInstance, inferInstance, hF, ⟨eQ.trans e⟩⟩

/-- In the elementary branch the complement is the concrete plane E₉. -/
theorem elementary_alternative (hcover : TrivialThreeCover.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 3)
    (he : IsElementaryAbelian 3 R) (hc : Nat.card R = 9) :
    Nonempty (R ≃* Plane 3) ∧ LinearThreeModel 3 Q := by
  let _ := he
  exact ⟨plane_of_elementary_card (by simpa using hc),
    model_of_center_eq_bot (hcover Q h.quasisimple hm) hm⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree
