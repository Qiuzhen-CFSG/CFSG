module

public import Theory.GroupTheory.DoubleCoverCentralizer.DisplacementTransport
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms.Full
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionFusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Noncentral


/-!
# Non-two-central displacements for every outer J₂ involution

For the displayed outer action σ fixing a and inverting b, the word
x = (ba)³b⁻¹ satisfies x σ(x)⁻¹ = a. This follows just from the already
checked relations a² = b³ = (ab)⁷ = 1; no additional permutation certificate
is needed. The actual centralizer C(a) has order 240, hence even index 2520,
which excludes centrality in any Sylow two-subgroup.

The full automorphism equivalence and the exhaustive outer-involution fusion
in the permutation extension transport this carrier witness to every abstract
outer involution. Both the action and the witness remain on the original
ATLAS degree-100 J₂ carrier; no cover theorem is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, I.2.2,
observation (iii), printed p.411 / PDF p.422. The source generating pair and
outer action retain the ATLAS J2G1-p100B0 data and attribution in
Theory/SpecificGroups/LeechRelated/AtlasCarriers/source/ and LICENSES/ATLAS.txt.
-/

public section
namespace Theory.SpecificGroups.ExceptionalOuterDisplacements.J2

open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.ExceptionalParabolics

private def witness : Carrier := (b * a) ^ 3 * b⁻¹

private theorem word_displacement {G : Type*} [Group G] (a b : G)
    (σ : MulAut G) (ha : a ^ 2 = 1) (hb : b ^ 3 = 1)
    (hab : (a * b) ^ 7 = 1) (hσa : σ a = a) (hσb : σ b = b⁻¹) :
    ((b * a) ^ 3 * b⁻¹) * (σ ((b * a) ^ 3 * b⁻¹))⁻¹ = a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha)
  have hbi : b⁻¹ * b⁻¹ = b := by
    calc
      b⁻¹ * b⁻¹ = b⁻¹ * b⁻¹ * b ^ 3 := by rw [hb, mul_one]
      _ = b := by group
  simp only [map_mul, map_pow, map_inv, hσb, hσa, inv_inv]
  rw [mul_inv_rev, ← inv_pow, mul_inv_rev, inv_inv, hai]
  calc
    (b * a) ^ 3 * b⁻¹ * (b⁻¹ * (a * b) ^ 3) =
        (b * a) ^ 3 * (b⁻¹ * b⁻¹) * (a * b) ^ 3 := by group
    _ = (b * a) ^ 3 * b * (a * b) ^ 3 := by rw [hbi]
    _ = a⁻¹ * (a * b) ^ 7 := by
      simp only [pow_succ, pow_zero]
      group
    _ = a := by rw [hab, mul_one, hai]

private theorem witness_displacement :
    witness * (involutionAut witness)⁻¹ = a :=
  word_displacement a b involutionAut a_pow_two b_pow_three ab_pow_seven
    involutionAut_a involutionAut_b

private theorem a_not_twoCentral : ¬ TwoCentral a := by
  have hc : Nat.card (centralizer ({a} : Set Carrier)) = 240 := by
    rw [Nat.card_congr InnerInvolutionCores.a_centralizer_equiv.toEquiv, Nat.card_prod,
      nat_card_alternatingGroup, Nat.card_fin]
    norm_num [InnerInvolutionCores.E4, InnerInvolutionCores.C2, Nat.card_fun, Nat.factorial]
  have h := (centralizer ({a} : Set Carrier)).card_mul_index
  rw [hc, FirstParabolic.card_carrier] at h
  have hi : (centralizer ({a} : Set Carrier)).index = 2520 := by omega
  intro ha
  exact ha.not_dvd_centralizer_index (hi ▸ (by decide : 2 ∣ 2520))

private theorem representative : HasNonTwoCentralDisplacement involutionAut := by
  refine ⟨witness, ?_, ?_⟩
  · rw [witness_displacement]
    apply orderOf_eq_prime a_pow_two
    intro h
    apply comm_word_pow_four_ne
    simp only [h, one_mul, mul_one, mul_inv_cancel, one_pow]
  · rw [witness_displacement]
    exact a_not_twoCentral

/-- Every outer involution of the actual Hall–Janko carrier has a
non-two-central displacement. -/
theorem outer_displacement (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ s : Carrier, r = MulAut.conj s) : HasNonTwoCentralDisplacement r := by
  obtain ⟨x, rfl⟩ := extensionAction_surjective r
  have hx : orderOf x = 2 :=
    (orderOf_injective extensionAction extensionAction_injective x).symm.trans hr
  have hxout : x ∉ intoExtension.range := by
    rintro ⟨g, rfl⟩
    exact ho ⟨g, extensionAction_inner g⟩
  have h := extensionAction.map_isConj
    (OuterInvolutionFusion.extension_outer_involution_fusion x hx hxout)
  rw [extensionAction_involution] at h
  obtain ⟨e, he⟩ := isConj_iff.mp h
  rw [← he]
  exact representative.map e

end Theory.SpecificGroups.ExceptionalOuterDisplacements.J2
