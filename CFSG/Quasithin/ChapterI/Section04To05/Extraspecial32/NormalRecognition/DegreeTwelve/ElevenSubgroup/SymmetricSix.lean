module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.CommutingCubic
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.LocalGluing
public import Theory.SpecificGroups.SymmetricCoxeterRecognition

/-!
# The marked symmetric-six subgroup

The cubic actions give the end braid relations, the squares of the end
reflections, and all distant commutations. The two remaining braids and
generation are the local gluing calculation of Lemma 4.6. A cubic generator
prevents collapse of the resulting type-A₅ presentation. The faithful
presentation map identifies the literal generated subgroup with S₆ and
sends the distinguished involutions to the first and last adjacent swaps.

The final theorem `symmetricSixData` constructs the commuting cubic using
Lemma 4.5 and discharges the local gluing calculation using the two cubic
four-groups and their compatible fixed lines. Its only inputs are the local
hypotheses, relative quaternion normality, fusion-eight data and the earlier
source geometry. Both ambient order alternatives remain available until the
marked symmetric subgroup has been constructed.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemmas 4.5–4.6, pp.40–41.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup

open Subgroup

variable {G : Type*} [Group G] {z : G}

private theorem reverse_cube {r s : G} (hr : r * r = 1) (hs : s * s = 1)
    (hrs : (r * s) ^ 3 = 1) : (s * r) ^ 3 = 1 := by
  have hri : r⁻¹ = r := inv_eq_iff_mul_eq_one.mpr hr
  have hsi : s⁻¹ = s := inv_eq_iff_mul_eq_one.mpr hs
  have hi := congrArg Inv.inv hrs
  simpa only [← inv_pow, mul_inv_rev, hri, hsi, inv_one] using hi

private theorem commuting_square {r s : G} (hr : r * r = 1) (hs : s * s = 1)
    (hrs : Commute r s) : (r * s) ^ 2 = 1 := by
  rw [hrs.mul_pow, pow_two, pow_two, hr, hs, one_mul]

private theorem inverting_squares {r x : G} (hr : r * r = 1)
    (hi : r * x * r⁻¹ = x⁻¹) :
    (x * r) * (x * r) = 1 ∧ (r * x) * (r * x) = 1 := by
  have hri : r⁻¹ = r := inv_eq_iff_mul_eq_one.mpr hr
  have hx : r * x * r = x⁻¹ := by simpa only [hri] using hi
  constructor
  · calc
      (x * r) * (x * r) = x * (r * x * r) := by group
      _ = 1 := by rw [hx, mul_inv_cancel]
  · calc
      (r * x) * (r * x) = (r * x * r) * x := by group
      _ = 1 := by rw [hx, inv_mul_cancel]

variable [Finite G] {h : Hypotheses z} {a : SourceGeometry h}

/-- All 25 relations in the source A₅ chain, derived from the two local
braids and the centralizing/inverting actions of the cubic subgroups. -/
public theorem CoxeterGluingData.relations (c : CommutingCubicData h a)
    (b : CoxeterGluingData c) :
    CoxeterMatrix.IsLiftable (CoxeterMatrix.A 5) (sourceChain z c.u b.x b.x1 b.v) := by
  have hx : b.x ∈ cubicInG h := b.x_generator ▸ mem_zpowers b.x
  have hx1 : b.x1 ∈ c.X1 := b.x1_generator ▸ mem_zpowers b.x1
  have ho : orderOf b.x = 3 := by rw [← Nat.card_zpowers, b.x_generator, cubicInG_card]
  have ho1 : orderOf b.x1 = 3 := by rw [← Nat.card_zpowers, b.x1_generator, c.card_X1]
  have hx3 : b.x ^ 3 = 1 := ho ▸ pow_orderOf_eq_one b.x
  have hx13 : b.x1 ^ 3 = 1 := ho1 ▸ pow_orderOf_eq_one b.x1
  have hz2 : z * z = 1 := by simpa only [h.involution, pow_two] using pow_orderOf_eq_one z
  have hu2 : c.u * c.u = 1 := by simpa only [c.u_order, pow_two] using pow_orderOf_eq_one c.u
  have hzi : z⁻¹ = z := inv_eq_iff_mul_eq_one.mpr hz2
  have hui : c.u⁻¹ = c.u := inv_eq_iff_mul_eq_one.mpr hu2
  have hinv1 := c.z_inverts_X1 b.x1 hx1
  have hinv := c.u_inverts_X b.x hx
  have hz1 : z * (b.x1 * z) = b.x1⁻¹ := by
    simpa only [hzi, mul_assoc] using hinv1
  have hu1 : (c.u * b.x) * c.u = b.x⁻¹ := by simpa only [hui] using hinv
  have h12 : (b.x1 * z) * (b.x1 * z) = 1 := (inverting_squares hz2 hinv1).1
  have h32 : (c.u * b.x) * (c.u * b.x) = 1 := (inverting_squares hu2 hinv).2
  have h01 : (z * (b.x1 * z)) ^ 3 = 1 := by rw [hz1, inv_pow, hx13, inv_one]
  have h34 : ((c.u * b.x) * c.u) ^ 3 = 1 := by rw [hu1, inv_pow, hx3, inv_one]
  have hxz : Commute b.x z := mem_centralizer_singleton_iff.mp (cubicInG_le h hx)
  have hx1u : Commute b.x1 c.u := (c.u_centralizes_X1 b.x1 hx1).symm
  have hx1x : Commute b.x1 b.x := (c.X1_centralizes_X hx1 b.x hx).symm
  have h03 : Commute z (c.u * b.x) := c.u_commutes_z.symm.mul_right hxz.symm
  have h13 : Commute (b.x1 * z) (c.u * b.x) :=
    (hx1u.mul_right hx1x).mul_left h03
  have h14 : Commute (b.x1 * z) c.u := hx1u.mul_left c.u_commutes_z.symm
  have h02 := commuting_square hz2 b.v_sq b.v_commutes_z.symm
  have h03' := commuting_square hz2 h32 h03
  have h04 := commuting_square hz2 hu2 c.u_commutes_z.symm
  have h13' := commuting_square h12 h32 h13
  have h14' := commuting_square h12 hu2 h14
  have h24 := commuting_square b.v_sq hu2 b.v_commutes_u
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [CoxeterMatrix.A, sourceChain]
  all_goals first
    | assumption
    | exact b.v_sq
    | exact b.left_braid
    | exact b.right_braid
    | exact reverse_cube hz2 h12 h01
    | exact reverse_cube h12 b.v_sq b.left_braid
    | exact reverse_cube b.v_sq h32 b.right_braid
    | exact reverse_cube h32 hu2 h34
    | simpa only [b.v_commutes_z.eq] using h02
    | simpa only [h03.eq] using h03'
    | simpa only [c.u_commutes_z.eq] using h04
    | simpa only [h13.eq] using h13'
    | simpa only [h14.eq] using h14'
    | simpa only [b.v_commutes_u.eq] using h24

/-- The chain cannot collapse to the sign quotient: its first adjacent
product is the inverse of a genuine cubic generator. -/
public theorem CoxeterGluingData.first_product_ne_one (c : CommutingCubicData h a)
    (b : CoxeterGluingData c) :
    sourceChain z c.u b.x b.x1 b.v 0 * sourceChain z c.u b.x b.x1 b.v 1 ≠ 1 := by
  have hx1 : b.x1 ∈ c.X1 := b.x1_generator ▸ mem_zpowers b.x1
  have ho1 : orderOf b.x1 = 3 := by rw [← Nat.card_zpowers, b.x1_generator, c.card_X1]
  have hz2 : z * z = 1 := by simpa only [h.involution, pow_two] using pow_orderOf_eq_one z
  have hzi : z⁻¹ = z := inv_eq_iff_mul_eq_one.mpr hz2
  have hi : z * (b.x1 * z) = b.x1⁻¹ := by
    simpa only [hzi, mul_assoc] using c.z_inverts_X1 b.x1 hx1
  change z * (b.x1 * z) ≠ 1
  rw [hi, inv_ne_one]
  intro he
  simp only [he, orderOf_one] at ho1
  omega

/-- The complete marked symmetric-six construction, conditional only on
the commuting cubic of 4.5 and the local gluing calculation of 4.6. -/
public theorem symmetricSixData_of_cubic_and_gluing (c : CommutingCubicData h a)
    (b : CoxeterGluingData c) : Nonempty (SymmetricSixData h a) := by
  obtain ⟨e, he⟩ := Theory.GroupTheory.SymmetricCoxeterRecognition.exists_marked_equiv
    1 (sourceChain z c.u b.x b.x1 b.v) (b.relations c) (b.first_product_ne_one c)
  let S := closure (Set.range (sourceChain z c.u b.x b.x1 b.v))
  have hzS : z ∈ S := subset_closure ⟨0, rfl⟩
  have huS : c.u ∈ S := subset_closure ⟨4, rfl⟩
  have hzmark : e ⟨z, hzS⟩ = Equiv.swap (0 : Fin 6) 1 := he 0
  have humark : e ⟨c.u, huS⟩ = Equiv.swap (4 : Fin 6) 5 := he 4
  refine ⟨{
    u := c.u
    u_choice := c.u_choice
    u_order := c.u_order
    u_fused := c.u_fused
    X1 := c.X1
    card_X1 := c.card_X1
    X1_centralizes_X := c.X1_centralizes_X
    z_inverts_X1 := c.z_inverts_X1
    u_centralizes_X1 := c.u_centralizes_X1
    centralizer_X_card := c.centralizer_X_card
    S := S
    generated := b.generated
    equiv := e
    z_mem := hzS
    u_mem := huS
    z_swap := ?_
    u_swap := ?_ }⟩
  · rw [hzmark]
    exact ⟨0, 1, by decide, rfl⟩
  · rw [humark]
    exact ⟨4, 5, by decide, rfl⟩

/-- Aschbacher 4.5–4.6: the commuting cubic and the actual marked symmetric
subgroup, with both intermediate constructions discharged. The chosen
involution is either `a.u` or `a.u * z`, retains its order and fusion, and
maps to a transposition, as does `z`. The centralizer of the original cubic
has order 18 or 54. No ambient simplicity or choice of ambient order is
assumed. -/
public theorem symmetricSixData (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SourceGeometry h) : Nonempty (SymmetricSixData h a) := by
  obtain ⟨c⟩ := commutingCubicData h hn d a
  obtain ⟨b⟩ := LocalGluing.coxeterGluingData_of_commutingCubic h hn d a c
  exact symmetricSixData_of_cubic_and_gluing c b

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
