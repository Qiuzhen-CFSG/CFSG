module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Central
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.PowerAction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Placement
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Actions
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# The binary PSL₃ three-complement sieve

For Q/Z(Q) ≅ PSL₃(2), the actual projective order is 168. Thus the
three-complement has cyclic image modulo the center, and the central
intersection argument supplies a proper nonzero invariant subgroup. This
works for every central cover, without an assumed multiplier calculation.

For f > 1, genuine Sylow membership and RS = SR give proper-parabolic and
Borel placement. The scalar-cover comparison makes R abelian. If R meets
Z(Q) nontrivially, its central image gives an invariant line. Otherwise
projection is injective on R, and the actual field and graph actions on
R/Φ(R) give reducibility for every two-subgroup of the pair automizer.

The final assembly retains only the explicitly named universal multiplier
input from I.1.3: the ordinary cyclic multiplier, or C₄ × C₄ × C₃ for
PSL₃(4). Placement, the scalar-cover comparison and the action identities
are proved, including standard-automorphism coverage. The source assembly
must still supply this earlier multiplier theorem.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528), and I.1.1 and I.1.3,
printed p.407 (PDF p.418 of `refs/quasithin.pdf`).
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear

/-- The field of order two is excluded for every central cover by its exact order. -/
theorem pairReducible_binary {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (hmodel : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 2) :
    PairReducible (S : Subgroup Q) R := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  apply pairReducible_of_not_nine_dvd_central_quotient h
  rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.card_projective F, hF]
  norm_num

/-- Once the complement is abelian, central intersection handles all cases
except those where projection to the simple central quotient is injective.
Only that remaining case needs the actual field and graph formulas. -/
theorem pairReducible_of_commutative_and_disjoint_action
    {Q : Type*} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (hc : IsMulCommutative R)
    (haction : Disjoint R (center Q) → ∀ D : Subgroup (MulAut R),
      D ≤ pairAutomizer (S : Subgroup Q) R → IsPGroup 2 D →
      ∃ g : MulAut (R ⧸ frattini R), g ^ 2 = 1 ∧
        ∀ a ∈ D, ∀ v, quotientAut (frattini R) a v ∈ zpowers v ∨
          quotientAut (frattini R) a v ∈ zpowers (g v)) :
    PairReducible (S : Subgroup Q) R := by
  by_cases hd : Disjoint R (center Q)
  · exact pairReducible_of_power_involution h (haction hd)
  let _ := hc
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fact (IsPGroup 3 R) := ⟨h.oddComplement.isPGroup⟩
  have hPhi : frattini R = ⊥ := by
    rcases h.oddComplement with ⟨he, _⟩ | ⟨he, _, _⟩
    · let _ := he
      exact frattini_eq_bot_of_isElementaryAbelian (p := 3)
    · exact ((QuotientGroup.nontrivial_iff.mp he.quotient_nontrivial)
        (center_eq_top (G := R))).elim
  apply pairReducible_of_central_not_le_frattini h
  intro hC
  apply hd
  apply Subgroup.disjoint_def.mpr
  intro r hr hz
  have hh : (⟨r, hr⟩ : R) ∈ (⊥ : Subgroup R) := by
    rw [← hPhi]
    exact hC hz
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hh)

/-- Exclude every binary PSL₃ pair, including degree one and all central covers
with trivial two-core. The sole earlier-source parameter is the exact universal
multiplier implication of I.1.3. No placement or action premise remains. -/
theorem pairReducible_of_universalMultiplierInput
    {Q : Type*} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) {f : ℕ} (hf : 1 ≤ f)
    (hmodel : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 (2 ^ f))
    (hI : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ f →
      Placement.ScalarCover.UniversalMultiplierInput F f) :
    PairReducible (S : Subgroup Q) R := by
  by_cases hf1 : f = 1
  · apply pairReducible_binary h
    simpa only [hf1, pow_one] using hmodel
  have hf2 : 2 ≤ f := by omega
  obtain ⟨hn, hc⟩ := Placement.placement_of_universalMultiplierInput h hf2 hmodel hI
  apply pairReducible_of_commutative_and_disjoint_action h hc
  intro hd D hD htwo
  exact Actions.pair_power_involution h hf2 hmodel hn hc hd D hD htwo


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear
