module

public import Theory.SpecificGroups.Rudvalis.Model.Basic
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

/-!
# A certification criterion for the concrete Rudvalis model

The word `w = ababb` normally generates the model: in a quotient killing it,
put `x = ab`. Then `b = x⁻²` and `a = x³`; the relations `a² = 1` and
`x¹³ = 1` force `x = 1`, hence both generators die.

If the action on 4060 points is primitive, every nontrivial normal subgroup
is transitive, so its order is divisible by 29. If the model has the ATLAS
order 145926144000, its quotient by such a subgroup has order prime to 29.
Thus the order-29 word dies in that quotient, forcing the subgroup to be
all of the model. The order and primitivity premises remain to be certified
for the explicit tables; this theorem does not assume or assert recognition
of any ambient group from its order.

The numerical data and word relations are from the ATLAS Ru entry:
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Ru/ .
-/

namespace Rudvalis

private theorem kill_generators {G : Type*} [Group G] (a b : G)
    (ha : a ^ 2 = 1) (hab : (a * b) ^ 13 = 1)
    (hw : a * b * a * b * b = 1) : a = 1 ∧ b = 1 := by
  let x := a * b
  have hb : b = (x ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right (by
    simpa only [x, pow_two, mul_assoc] using hw)
  have ha' : a = x ^ 3 := by
    calc
      a = x * b⁻¹ := by dsimp [x]; group
      _ = x ^ 3 := by rw [hb]; group
  have hx6 : x ^ 6 = 1 := by
    simpa only [ha', ← pow_mul] using ha
  have hx : x = 1 := by
    have heq : x ^ 13 = x := by
      calc
        x ^ 13 = (x ^ 6) ^ 2 * x := by group
        _ = x := by rw [hx6]; simp
    exact heq.symm.trans hab
  constructor
  · simp only [ha', hx, one_pow]
  · simp only [hb, hx, one_pow, inv_one]

/-- Every normal subgroup containing the order-29 word is the whole model. -/
public theorem normal_eq_top_of_w_mem (N : Subgroup Model) [N.Normal] (hw : w ∈ N) :
    N = ⊤ := by
  let q := QuotientGroup.mk' N
  have hq : q a = 1 ∧ q b = 1 := kill_generators (q a) (q b)
    (by rw [← map_pow, a_sq, map_one])
    (by rw [← map_mul, ← map_pow, ab_thirteenth, map_one])
    (by
      have h : q w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
      simpa only [w, map_mul] using h)
  exact eq_top_of_a_mem_of_b_mem N
    ((QuotientGroup.eq_one_iff a).mp hq.1)
    ((QuotientGroup.eq_one_iff b).mp hq.2)

/-- The standard order-29 word normally generates the concrete model. -/
public theorem w_normalClosure : Subgroup.normalClosure ({w} : Set Model) = ⊤ :=
  normal_eq_top_of_w_mem _ (Subgroup.subset_normalClosure (Set.mem_singleton _))


/-- The two remaining concrete certificates suffice for simplicity. -/
public theorem simple_of_card_of_primitive
    [MulAction.IsPreprimitive Model (Fin 4060)]
    (hcard : Nat.card Model = 145926144000) : IsSimpleGroup Model := by
  classical
  let : Fact (Nat.Prime 29) := ⟨by decide⟩
  apply IsSimpleGroup.mk
  intro N hN
  by_cases hfix : MulAction.fixedPoints N (Fin 4060) = Set.univ
  · left
    apply N.eq_bot_iff_forall.mpr
    intro n hn
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin 4060)
    intro x
    rw [one_smul]
    exact Set.eq_univ_iff_forall.mp hfix x ⟨n, hn⟩
  · right
    have : MulAction.IsPretransitive N (Fin 4060) :=
      MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfix
    have hd : 4060 ∣ Nat.card N := by
      have h := (MulAction.stabilizer N (0 : Fin 4060)).index_dvd_card
      simpa only [MulAction.index_stabilizer_of_transitive, Nat.card_fin] using h
    have hn29 : 29 ∣ Nat.card N := dvd_trans (by decide : 29 ∣ 4060) hd
    have hindex : ¬29 ∣ N.index := by
      intro hi
      have hsq : 29 * 29 ∣ Nat.card Model := by
        rw [← N.index_mul_card]
        exact Nat.mul_dvd_mul hi hn29
      rw [hcard] at hsq
      norm_num at hsq
    apply normal_eq_top_of_w_mem N
    apply (QuotientGroup.eq_one_iff w).mp
    by_contra hw
    have ho : orderOf (QuotientGroup.mk' N w) = 29 :=
      orderOf_eq_prime (by rw [← map_pow, w_twentyNinth, map_one]) hw
    apply hindex
    change 29 ∣ Nat.card (Model ⧸ N)
    rw [← ho]
    exact orderOf_dvd_natCard _


end Rudvalis
