module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.Divisibility
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.HigmanSims.ElementaryResidual
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.HigmanSims.CoverBound
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.HigmanSims.CoreNormalOrders
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.HigmanSims.ProductNormalOrders

/-!
# Excluding the Higman--Sims residual pairs

The involution rows for HS are retained as an explicit earlier input.  The
`S₈` outer row is separated from both inner rows by the odd prime `7`.  The
elementary-kernel outer residual is nonsolvable and has order dividing 960.
The HS covering bound |Z(L)| ≤ 2 raises its ambient order to a divisor of
1920. Its image in L/Z(L) is normal in the inner residual, because the whole
inner centralizer normalizes the outer residual. The two intrinsic inner
normal-order theorems force this image's order to be divisible by 3840 or
by nine, neither of which divides 1920.

The final theorem `not_hs_quotient` discharges both intrinsic model prerequisites.
Simplicity and perfectness of the actual HS carrier are transported from the
quasisimple component's central quotient. The only earlier inputs retained
are the involution table and `hZ`, precisely the HS clause of 16.1.2(2).

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
16.1.5(10), printed p.1172, and the comparison in the proof of 16.4.11(2),
printed p.1193. The covering order bound is 16.1.2(2), printed p.1170.
-/

set_option backward.isDefEq.respectTransparency false

public section

namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

private theorem hs_s8_card : Nat.card S8 = 40320 := by
  simp only [S8, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num [Nat.factorial]

private theorem hs_s8_seven_dvd : 7 ∣ Nat.card S8 := by
  rw [hs_s8_card]
  norm_num

private theorem hs_core_inner_not_seven {C : Type*} [Group C] [Finite C]
    (h : IsHSCoreExtension C) : ¬ 7 ∣ Nat.card C := by
  rw [HSInner.coreExtension_card h]
  norm_num

private theorem hs_product_inner_not_seven {C : Type*} [Group C] [Finite C]
    (e : C ≃* C2 × MulAut A6) : ¬ 7 ∣ Nat.card C := by
  rw [Nat.card_congr e.toEquiv, HSInner.ClassCoverage.product_card]
  norm_num

private theorem hs_inner_not_seven (a : MulAut Sporadic.LeechRelated.HS.Carrier)
    (h : HSInvolutionAlternative a) (hi : ∃ x, a = MulAut.conj x) :
    ¬ 7 ∣ Nat.card a.fixedSubgroup := by
  rcases h with ⟨_, h⟩ | ⟨ho, _⟩
  · rcases h with hc | hp
    · exact hs_core_inner_not_seven hc
    · obtain ⟨e⟩ := hp
      exact hs_product_inner_not_seven e
  · exact (ho hi).elim

/-- The `S₈` row cannot be the actual outer action in the contrary setup.
Both inner rows lack the prime seven; the two covering kernels are kept
separate throughout the divisibility transport. -/
theorem not_hs_s8_outer (d : Contrary T z L g R r)
    (rows : ∀ a : MulAut Sporadic.LeechRelated.HS.Carrier,
      orderOf a = 2 → HSInvolutionAlternative a)
    (e : (L ⧸ center L) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hout : Nonempty ((MulAut.centralQuotientAction
      ((centralQuotientCongr ((MulAut.conj g).subgroupMap L)).symm.trans e)
        (action d.z_normalizes)).fixedSubgroup ≃* S8)) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let ec : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
  let : IsQuasisimple (L.conjBy g) := IsQuasisimple.of_mulEquiv ec
  let eM := (centralQuotientCongr ec).symm.trans e
  let hi := d.setup.sylow_normalizes (d.setup.le_sylow d.mem)
  let a := MulAut.centralQuotientAction e (action hi)
  let b := MulAut.centralQuotientAction eM (action d.z_normalizes)
  have ha : orderOf a = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) _).trans d.inner_action_order
  have hia : ∃ x : Sporadic.LeechRelated.HS.Carrier, a = MulAut.conj x :=
    (MulAut.centralQuotientAction_inner_iff e (action hi)).mpr d.inner_action
  obtain ⟨eS⟩ := hout
  change b.fixedSubgroup ≃* S8 at eS
  have h7 : 7 ∣ Nat.card b.fixedSubgroup := by
    rw [Nat.card_congr eS.toEquiv]
    exact hs_s8_seven_dvd
  have hbo := (odd_prime_dvd_residual_iff (by norm_num : Nat.Prime 7)
    (by norm_num : 7 ≠ 2)).mpr h7
  have ho : 7 ∣ Nat.card (centralImage (L.conjBy g) (residual (L.conjBy g) z)) := by
    rw [Nat.card_congr (centralImageModelEquiv (conjugate_oddCore d) eM
      d.z_normalizes).toEquiv]
    exact hbo
  have hai := outer_odd_prime_dvd_inner d (by norm_num : Nat.Prime 7)
    (by norm_num : 7 ≠ 2) ho
  rw [Nat.card_congr (centralImageModelEquiv (component_oddCore d) e hi).toEquiv] at hai
  exact hs_inner_not_seven a (rows a ha) hia
    ((odd_prime_dvd_residual_iff (by norm_num : Nat.Prime 7)
      (by norm_num : 7 ≠ 2)).mp hai)

/-- The elementary outer row is impossible once the intrinsic normal-order
facts for the two inner residuals are supplied. Only the sourced bound on
the HS covering center is needed; the quotient kernels are not identified. -/
theorem not_hs_elementary_outer_of_normal_orders (d : Contrary T z L g R r)
    (e : (L ⧸ center L) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center L) ≤ 2)
    (normalOrders : ∀ a : MulAut Sporadic.LeechRelated.HS.Carrier,
      orderOf a = 2 → (∃ x, a = MulAut.conj x) →
      ∀ N : Subgroup (pResidual 2 a.fixedSubgroup), N.Normal →
        (¬ Group.IsSolvable N) → 3840 ∣ Nat.card N ∨ 9 ∣ Nat.card N)
    (hout : IsHSElementaryExtension (MulAut.centralQuotientAction
      ((centralQuotientCongr ((MulAut.conj g).subgroupMap L)).symm.trans e)
        (action d.z_normalizes)).fixedSubgroup) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let ec : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
  let : IsQuasisimple (L.conjBy g) := IsQuasisimple.of_mulEquiv ec
  let eM := (centralQuotientCongr ec).symm.trans e
  let hi := d.setup.sylow_normalizes (d.setup.le_sylow d.mem)
  let a := MulAut.centralQuotientAction e (action hi)
  let b := MulAut.centralQuotientAction eM (action d.z_normalizes)
  have ha : orderOf a = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) _).trans d.inner_action_order
  have hia : ∃ x : Sporadic.LeechRelated.HS.Carrier, a = MulAut.conj x :=
    (MulAut.centralQuotientAction_inner_iff e (action hi)).mpr d.inner_action
  change IsHSElementaryExtension b.fixedSubgroup at hout
  let X := residual (L.conjBy g) z
  let Y := residual L r
  have hXY : X ≤ Y := d.residual_normal.1
  have hYL : Y ≤ L := (residual_le L r).trans inf_le_left
  have hXM : X ≤ L.conjBy g := (residual_le (L.conjBy g) z).trans inf_le_left
  have hZm : Nat.card (center (L.conjBy g)) ≤ 2 := by
    rw [← Nat.card_congr (centerCongr ec).toEquiv]
    exact hZ
  let eX := centralImageModelEquiv (conjugate_oddCore d) eM d.z_normalizes
  have hXimage : Nat.card (centralImage (L.conjBy g) X) ∣ 960 := by
    rw [Nat.card_congr eX.toEquiv]
    exact hs_elementary_residual_card_dvd hout
  have hXcard : Nat.card X ∣ 1920 :=
    card_dvd_two_mul_centralImage hXM hZm hXimage
  have hXns : ¬ Group.IsSolvable X := by
    intro hs
    let := (centralImage_solvable_iff hXM).mpr hs
    exact hs_elementary_residual_not_solvable hout
      (Group.isSolvable_of_surjective (f := eX.toMonoidHom) eX.surjective)
  have hXn : (X.subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer hXY).mpr
      ((residual_le L r).trans d.residual_normal.2.2)
  have hB : centralImage L X ≤ centralImage L Y :=
    map_mono (comap_mono hXY)
  let B := (centralImage L X).subgroupOf (centralImage L Y)
  let eY := centralImageModelEquiv (component_oddCore d) e hi
  let N := B.map eY.toMonoidHom
  let eN : centralImage L X ≃* N :=
    (subgroupOfEquivOfLe hB).symm.trans (eY.subgroupMap B)
  have hNn : N.Normal :=
    (centralImage_normal hYL hXY hXn).map eY.toMonoidHom eY.surjective
  have hNns : ¬ Group.IsSolvable N := by
    intro hs
    let := hs
    have hsI := Group.isSolvable_of_surjective (f := eN.symm.toMonoidHom) eN.symm.surjective
    exact hXns ((centralImage_solvable_iff (hXY.trans hYL)).mp hsI)
  have hNcard : Nat.card N ∣ 1920 := by
    rw [← Nat.card_congr eN.toEquiv]
    exact (card_dvd_of_surjective (centralImageMap (hXY.trans hYL))
      (centralImageMap_surjective (hXY.trans hYL))).trans hXcard
  rcases normalOrders a ha hia N hNn hNns with hlarge | hnine
  · have h := hlarge.trans hNcard
    norm_num at h
  · have h := hnine.trans hNcard
    norm_num at h

/-- Conditional assembly of the HS comparison. The table and the HS center
bound are earlier source inputs. The intrinsic `normalOrders` premise is
discharged in `not_hs_quotient` below. -/
theorem not_hs_quotient_of_normal_orders (d : Contrary T z L g R r)
    (rows : ∀ a : MulAut Sporadic.LeechRelated.HS.Carrier,
      orderOf a = 2 → HSInvolutionAlternative a)
    (e : (L ⧸ center L) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center L) ≤ 2)
    (normalOrders : ∀ a : MulAut Sporadic.LeechRelated.HS.Carrier,
      orderOf a = 2 → (∃ x, a = MulAut.conj x) →
      ∀ N : Subgroup (pResidual 2 a.fixedSubgroup), N.Normal →
        (¬ Group.IsSolvable N) → 3840 ∣ Nat.card N ∨ 9 ∣ Nat.card N) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let ec : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
  let : IsQuasisimple (L.conjBy g) := IsQuasisimple.of_mulEquiv ec
  let eM := (centralQuotientCongr ec).symm.trans e
  let b := MulAut.centralQuotientAction eM (action d.z_normalizes)
  have hb : orderOf b = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction eM)
      (MulAut.centralQuotientAction_injective eM) _).trans d.outer_action_order
  have hob : ¬ ∃ x : Sporadic.LeechRelated.HS.Carrier, b = MulAut.conj x := fun h =>
    d.outer_action ((MulAut.centralQuotientAction_inner_iff eM _).mp h)
  rcases rows b hb with ⟨hi, _⟩ | ⟨_, hs | he⟩
  · exact (hob hi).elim
  · exact not_hs_s8_outer d rows e hs
  · exact not_hs_elementary_outer_of_normal_orders d e hZ normalOrders he

/-- The HS case of the residual comparison in 16.4.11(2) is impossible.
Both inner rows and both outer rows are covered. The only earlier inputs
are the genuine table 16.1.5(10) and the HS covering bound 16.1.2(2);
all intrinsic residual-order and model hypotheses are discharged. -/
theorem not_hs_quotient (d : Contrary T z L g R r)
    (rows : ∀ a : MulAut Sporadic.LeechRelated.HS.Carrier,
      orderOf a = 2 → HSInvolutionAlternative a)
    (e : (L ⧸ center L) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center L) ≤ 2) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let : IsSimpleGroup Sporadic.LeechRelated.HS.Carrier :=
    (MulEquiv.isSimpleGroup_congr e).mp IsQuasisimple.simple
  let : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply not_hs_quotient_of_normal_orders d rows e hZ
  intro a ha hi N hn hns
  rcases HSInner.inner_centralizer_alternative a ha hi with hc | hp
  · exact Or.inl (hs_core_residual_normal_card_dvd a ha hi hc N hn hns)
  · obtain ⟨ep⟩ := hp
    exact Or.inr (hs_product_residual_normal_nine_dvd ep N hn hns)

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
