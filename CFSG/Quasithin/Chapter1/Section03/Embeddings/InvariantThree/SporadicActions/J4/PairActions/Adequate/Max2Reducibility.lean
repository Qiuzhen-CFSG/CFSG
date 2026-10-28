module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Cubic
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.Transport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.CubicStructure
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence

/-!
# Max2 reducibility from concrete cubic structure

Transport the source pair through its actual maximal-overgroup equivalence
and the certified two-core quotient. In the elementary-nine case, a cubic
three-core contained in the image pulls back to an invariant Frattini line.
Every supplied actor preserves it because the three-core is characteristic.
In the extraspecial order-27 case, the image would yield a subgroup of order
6912, so the finite order exclusion eliminates that branch.

The unconditional theorem discharges the cubic order, elementary containment,
and order-6912 exclusion using the concrete matrix calculations. The conditional
assembly remains available with its existing interface.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511/PDF p.528
of `refs/quasithin.pdf`; GLS3 Table 5.3i. See `docs/quasithin-proof-basis.md`.
-/

public section
open Subgroup
open scoped Pointwise
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Janko4.modelGroup sourceSubgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate
namespace Max2

/-- The order-27 branch gives a forbidden subgroup of order 6912. -/
theorem not_order27_pair (hexclude : Order27Exclusion)
    (S : Sylow 2 MatrixGroup) (R : Subgroup MatrixGroup)
    (h3 : IsPGroup 3 R) (hc : Nat.card R = 27)
    (hp : (R : Set MatrixGroup) * (S : Set MatrixGroup) =
      (S : Set MatrixGroup) * (R : Set MatrixGroup)) : False := by
  have hd : Disjoint R S.toSubgroup :=
    h3.disjoint_of_coprime S.isPGroup' (by decide)
  have hcard := card_set_mul_mul_card_inf R S.toSubgroup
  rw [hd.eq_bot, card_bot, mul_one, ← coe_sup_of_set_mul_comm R S.toSubgroup hp,
    hc, involutionMatrixSylow_card S] at hcard
  exact hexclude (R ⊔ S.toSubgroup) hcard

end Max2

/-- Conditional assembly from the cubic structure and the finite pair
calculations. All actors and both source complement alternatives are retained. -/
theorem max2_localModelPairReducibility_of_matrix_conditions
    (hC : Nat.card (pCore 3 Max2.MatrixGroup) = 3)
    (hcontains : Max2.ElementaryCubicContainment)
    (hexclude : Max2.Order27Exclusion) : LocalModelPairReducibility sourceSubgroup := by
  intro _ _ _ S R h M _hM hSM hRM e D _hD _hD2 hact
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : IsPGroup 3 R := h.oddComplement.isPGroup
  let f := (Max2.projection e).comp (inclusion hRM)
  let T := Max2.quotientSylow S hSM e
  have hi : Function.Injective f := Max2.complement_injective e hRM h3
  have hp : (f.range : Set Max2.MatrixGroup) * (T : Set Max2.MatrixGroup) =
      (T : Set Max2.MatrixGroup) * (f.range : Set Max2.MatrixGroup) :=
    Max2.pair_permutes S hSM hRM e h.permutes
  have hc : Nat.card f.range = Nat.card R := Max2.complement_card e hRM h3
  rcases h.oddComplement with ⟨hE, hcard⟩ | ⟨_hEx, hcard, _hexp⟩
  · let _ := hE
    have hE' : IsElementaryAbelian 3 f.range := Max2.complement_elementary e hRM hE
    have hline : pCore 3 Max2.MatrixGroup ≤ f.range :=
      hcontains T f.range hE' (hc.trans hcard) hp
    exact actorReducible_of_characteristic_cubic hcard D f hi
      (pCore 3 Max2.MatrixGroup) hC hline (Max2.compatible_quotientActors e hRM D hact)
  · exact (Max2.not_order27_pair hexclude T f.range
      (h3.of_surjective f.rangeRestrict f.rangeRestrict_surjective) (hc.trans hcard) hp).elim

/-- Every compatible actor in an actual max2 maximal embedding preserves a
proper nonzero subgroup of the complement's Frattini quotient. The elementary
case uses the characteristic cubic core; the order-27 case is impossible. -/
theorem max2_localModelPairReducibility : LocalModelPairReducibility sourceSubgroup :=
  max2_localModelPairReducibility_of_matrix_conditions Max2.matrix_threeCore_card
    (Max2.elementaryCubicContainment_of_threeCore_card Max2.matrix_threeCore_card)
    Max2.order27Exclusion

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate
