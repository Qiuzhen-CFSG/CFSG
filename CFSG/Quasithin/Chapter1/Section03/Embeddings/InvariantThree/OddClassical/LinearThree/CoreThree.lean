module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Basic
public import Theory.SpecificGroups.PSL3Three.Order432Core
public import Theory.SpecificGroups.PSL3Three.CandidateOrders
public import Theory.SpecificGroups.PSL3Three.ParabolicThreeCores
public import Theory.SpecificGroups.LinearCoefficientEquiv
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# The extraspecial PSL₃(3) pair and its local three-core

The universal trivial-center consequence of I.1.3 gives an actual equivalence
from Q to PSL₃ over `ZMod 3`. The Sylow two-subgroup has order sixteen, so the
permutable pair with `|R| = 27` generates a subgroup of order 432. Inside that
subgroup R is Sylow three. Its intrinsic three-core therefore lies in R,
justifying the restriction to R in the cardinality consumed by
`reducible_of_extraspecial_local_core_nine`.

The concrete maximal-subgroup cover and candidate orders identify this local
subgroup with a full parabolic. Its three-core has order nine by the proved
root-plane computation. `local_threeCore_card` discharges all six model
calculations, retaining only the universal earlier-theorem cover input.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528), and I.1.3, printed p.407
(PDF p.418). The earlier cover input is independent of the pair and its action.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree
universe u
variable {Q : Type u} [Group Q] [Finite Q]

namespace CoreThree

/-- The permitted universal cover input identifies the covering group with
the actual matrix quotient over `ZMod 3`, including coefficient transport. -/
theorem exists_model_equiv (hcover : TrivialThreeCover.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 3) :
    Nonempty (Q ≃* Matrix.PSL3Three.PSL) := by
  have hz := hcover Q h.quasisimple hm
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let _ : Fintype F := Fintype.ofFinite F
  let eF : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q := QuotientGroup.mk' (center Q)
  have hq : Function.Injective q := by
    apply q.ker_eq_bot_iff.mp
    simpa only [q, QuotientGroup.ker_mk'] using hz
  let eQ : Q ≃* (Q ⧸ center Q) :=
    MulEquiv.ofBijective q ⟨hq, QuotientGroup.mk'_surjective _⟩
  exact ⟨eQ.trans (e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF.symm))⟩

/-- Permutability and the coprime orders give `|RS| = 27 · 16 = 432`. -/
theorem pair_card {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (e : Q ≃* Matrix.PSL3Three.PSL) (hR : Nat.card R = 27) :
    Nat.card ↥(R ⊔ (S : Subgroup Q)) = 432 := by
  have hQ : Nat.card Q = 5616 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Three.card_PSL
  have hS : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity, hQ, show 5616 = 2 ^ 4 * 351 by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 351)]
    norm_num
  have hd : Disjoint R (S : Subgroup Q) :=
    h.oddComplement.isPGroup.disjoint_of_coprime S.isPGroup' (by decide)
  have hc := card_set_mul_mul_card_inf R (S : Subgroup Q)
  rw [← coe_sup_of_set_mul_comm R (S : Subgroup Q) h.permutes,
    hd.eq_bot, Subgroup.card_bot, mul_one, hR, hS] at hc
  exact hc

/-- The order-27 complement is Sylow three in the order-432 local subgroup.
Normality is used inside that local subgroup, so its three-core lies in R. -/
theorem local_core_le_complement {S : Sylow 2 Q} {R : Subgroup Q}
    (hR : Nat.card R = 27) (hH : Nat.card ↥(R ⊔ (S : Subgroup Q)) = 432) :
    (R ⊔ (S : Subgroup Q)).pCoreIn 3 ≤ R := by
  let H := R ⊔ (S : Subgroup Q)
  have hRH : R ≤ H := le_sup_left
  have hRc : Nat.card (R.subgroupOf H) = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv).trans hR
  let U : Sylow 3 H := Sylow.ofCard (R.subgroupOf H) (by
    rw [hRc, show Nat.card H = 432 from hH, show 432 = 3 ^ 3 * 16 by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 16)]
    norm_num)
  have hc := H.pCoreIn_le_sylow U
  simpa only [U, Sylow.coe_ofCard, map_subgroupOf_eq_of_le hRH] using hc

/-- Since the local three-core lies in R, restricting it to R preserves
its order. This connects the intrinsic core to the exact source consumer. -/
theorem local_core_intersection_card {S : Sylow 2 Q} {R : Subgroup Q}
    (hR : Nat.card R = 27) (hH : Nat.card ↥(R ⊔ (S : Subgroup Q)) = 432) :
    Nat.card (((R ⊔ (S : Subgroup Q)).pCoreIn 3).subgroupOf R) =
      Nat.card (pCore 3 ↥(R ⊔ (S : Subgroup Q))) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (local_core_le_complement hR hH)).toEquiv]
  exact card_map_of_injective (R ⊔ (S : Subgroup Q)).subtype_injective


end CoreThree

open Matrix.PSL3Three in
/-- Conditional assembly of the extraspecial local-core calculation. The
universal cover premise is the authorized earlier-theorem input;
`local_threeCore_card` supplies the six explicit model orders below. -/
theorem local_threeCore_card_of_parabolic_calculations
    (hline : Nat.card lineStabilizer = 432)
    (hplane : Nat.card planeStabilizer = 432)
    (hmono : Nat.card monomial = 24)
    (hsinger : Nat.card singerNormalizer = 39)
    (hlineCore : Nat.card (pCore 3 lineStabilizer) = 9)
    (hplaneCore : Nat.card (pCore 3 planeStabilizer) = 9)
    (hcover : TrivialThreeCover.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 3) (hR : Nat.card R = 27) :
    Nat.card (((R ⊔ (S : Subgroup Q)).pCoreIn 3).subgroupOf R) = 9 := by
  obtain ⟨e⟩ := CoreThree.exists_model_equiv hcover h hm
  have hH := CoreThree.pair_card h e hR
  rw [CoreThree.local_core_intersection_card hR hH]
  let H := R ⊔ (S : Subgroup Q)
  have hc : Nat.card (H.map e.toMonoidHom) = 432 := by
    rw [card_map_of_injective e.injective]
    exact hH
  let f : H ≃* H.map e.toMonoidHom := e.subgroupMap H
  have hcore : Nat.card (pCore 3 H) = Nat.card (pCore 3 (H.map e.toMonoidHom)) := by
    rw [← pCore_map_iso 3 f, card_map_of_injective f.injective]
  exact hcore.trans
    (threeCore_card_of_card_eq_432_of_parabolic_calculations hline hplane hmono hsinger
      hlineCore hplaneCore _ hc)

open Matrix.PSL3Three in
/-- The local three-core of an order-27 PSL₃(3) pair has order nine inside R.
All candidate and full-parabolic core orders are proved; the only earlier
theorem parameter is the universal trivial-center consequence of I.1.3. -/
theorem local_threeCore_card (hcover : TrivialThreeCover.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 3) (hR : Nat.card R = 27) :
    Nat.card (((R ⊔ (S : Subgroup Q)).pCoreIn 3).subgroupOf R) = 9 := by
  exact local_threeCore_card_of_parabolic_calculations
    card_lineStabilizer card_planeStabilizer card_monomial card_singerNormalizer
    (card_threeCore_lineStabilizer card_lineStabilizer)
    (card_threeCore_planeStabilizer card_planeStabilizer) hcover h hm hR

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree
