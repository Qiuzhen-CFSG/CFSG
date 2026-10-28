module

public import Theory.SpecificGroups.Janko3.Model.ThreePrimary.Certificate
public import Theory.SpecificGroups.Janko3.Model.Order
public import Theory.GroupTheory.CubicClassThreePair
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# The marked order-243 subgroup in the actual J₃ model

The five checked generators `d,e,c,x,y` form a cyclic series with relative
orders three. Collection gives at most 243 elements and the separating
letter gives exactly 243. The iterated-commutator identities show that the
last two generators alone generate this subgroup. Its index is prime to
three by the checked ambient order, so central transfer applies to its
literal preimage in every perfect central cover.

This supplies concrete local data for Aschbacher–Smith I.1.4(2), printed
p.408; the local group is in GLS III, Table 5.3h. The central-extension
calculation remains separate from these permutation-group facts.
-/

namespace Sporadic.Janko3.ThreePrimary
open Subgroup Theory.GroupTheory TwoLocal.ThompsonCertificate
open scoped commutatorElement

/-- The two-generator local subgroup used for the multiplier calculation. -/
@[expose] public def localSubgroup : Subgroup Model := closure ({x, y} : Set Model)

public theorem x_mem : x ∈ localSubgroup := subset_closure (by simp)
public theorem y_mem : y ∈ localSubgroup := subset_closure (by simp)

private theorem comm_mem {a b : Model} (ha : a ∈ localSubgroup)
    (hb : b ∈ localSubgroup) : ⁅a, b⁆ ∈ localSubgroup :=
  localSubgroup.mul_mem
    (localSubgroup.mul_mem (localSubgroup.mul_mem ha hb) (localSubgroup.inv_mem ha))
    (localSubgroup.inv_mem hb)

public theorem c_mem : c ∈ localSubgroup := c_eq.symm ▸ comm_mem x_mem y_mem
public theorem d_mem : d ∈ localSubgroup := d_eq.symm ▸ comm_mem c_mem x_mem
public theorem e_mem : e ∈ localSubgroup := e_eq.symm ▸ comm_mem c_mem y_mem

public theorem chain_eq : chain 5 = localSubgroup := by
  apply le_antisymm
  · apply (NormalForm.series_le_iff gen 5 localSubgroup).mpr
    intro i hi
    interval_cases i <;> simp only [gen] <;>
      first | exact d_mem | exact e_mem | exact c_mem | exact x_mem | exact y_mem
  · apply (closure_le _).mpr
    rintro z (rfl | rfl)
    · exact NormalForm.gen_mem gen (i := 3) (by decide)
    · exact NormalForm.gen_mem gen (i := 4) (by decide)

private theorem chain_normalizes (k : ℕ) (hk : k < 5) :
    gen k ∈ normalizer (chain k : Set Model) := by
  apply NormalForm.normalizes
  · intro i hi
    rw [conjugate_relation ⟨k, hk⟩ ⟨i, hi⟩]
    exact NormalForm.rep_mem gen radix _ _
  · intro i hi
    rw [inverse_conjugate_relation ⟨k, hk⟩ ⟨i, hi⟩]
    exact NormalForm.rep_mem gen radix _ _

public theorem normal_form {z : Model} (hz : z ∈ localSubgroup) :
    ∃ r : Fin 243, z = representative 5 r.val := by
  rw [← chain_eq] at hz
  apply NormalForm.cover gen radix 5 (fun _ _ => Nat.zero_lt_succ 2)
    (fun k hk => chain_normalizes k hk) ?_ z hz
  intro k hk
  change gen k ^ 3 ∈ chain k
  rw [power_relation ⟨k, hk⟩]
  exact NormalForm.rep_mem gen radix _ _

/-- The 243 normal forms are complete and distinct. -/
public theorem localSubgroup_card : Nat.card localSubgroup = 243 := by
  let f : Fin 243 → localSubgroup := fun r =>
    ⟨representative 5 r.val, chain_eq ▸ NormalForm.rep_mem gen radix 5 r.val⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact representative_injective (congrArg Subtype.val h)
    · intro z
      obtain ⟨r, hr⟩ := normal_form z.property
      exact ⟨r, Subtype.ext hr.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fin]

/-- The source subgroup has index prime to three in the actual permutation model. -/
public theorem localSubgroup_index_prime_to_three : ¬ 3 ∣ localSubgroup.index := by
  have h := localSubgroup.card_mul_index
  rw [localSubgroup_card, model_card] at h
  have hi : localSubgroup.index = 206720 := by omega
  rw [hi]
  decide

/-- The first marked generator as an element of the literal local subgroup. -/
@[expose] public def pairX : localSubgroup := ⟨x, x_mem⟩
/-- The second marked generator as an element of the literal local subgroup. -/
@[expose] public def pairY : localSubgroup := ⟨y, y_mem⟩

public theorem pair_generates : closure ({pairX, pairY} : Set localSubgroup) = ⊤ := by
  have h : closure (localSubgroup.subtype ⁻¹' ({x, y} : Set Model)) = ⊤ :=
    closure_preimage_eq_top _
  have hs : localSubgroup.subtype ⁻¹' ({x, y} : Set Model) =
      ({pairX, pairY} : Set localSubgroup) := by
    ext z
    change (z.val = pairX.val ∨ z.val = pairY.val) ↔ (z = pairX ∨ z = pairY)
    simp only [Subtype.ext_iff]
  rwa [hs] at h

private theorem central_of_commute_pair {a : Model}
    (hx : Commute a x) (hy : Commute a y) :
    ∀ z ∈ localSubgroup, z * a = a * z := by
  have h : localSubgroup ≤ centralizer ({a} : Set Model) := by
    apply (closure_le _).mpr
    rintro z (rfl | rfl)
    · exact mem_centralizer_singleton_iff.mpr hx.symm.eq
    · exact mem_centralizer_singleton_iff.mpr hy.symm.eq
  exact fun z hz => mem_centralizer_singleton_iff.mp (h hz)

/-- Actual cubic and class-three relations on a generating pair of the order-243 subgroup.
This asserts relations on the model, not an unproved presentation identification. -/
public theorem pair_relations : CubicClassThreePair pairX pairY where
  commutator_cube := by
    apply Subtype.ext
    change ⁅x, y⁆ ^ 3 = 1
    rw [← c_eq, c_cube]
  left_central := by
    apply mem_center_iff.mpr
    intro z
    apply Subtype.ext
    change (z : Model) * ⁅⁅x, y⁆, x⁆ = ⁅⁅x, y⁆, x⁆ * z
    rw [← c_eq, ← d_eq]
    exact central_of_commute_pair d_commute_x d_commute_y z z.property
  right_central := by
    apply mem_center_iff.mpr
    intro z
    apply Subtype.ext
    change (z : Model) * ⁅⁅x, y⁆, y⁆ = ⁅⁅x, y⁆, y⁆ * z
    rw [← c_eq, ← e_eq]
    exact central_of_commute_pair e_commute_x e_commute_y z z.property
  left_cube := by
    apply Subtype.ext
    change x ^ 3 = ⁅⁅x, y⁆, x⁆ ^ 2 * ⁅⁅x, y⁆, y⁆
    rw [← c_eq, ← d_eq, ← e_eq, x_cube]
  right_cube := by
    apply Subtype.ext
    change y ^ 3 = ⁅⁅x, y⁆, x⁆ ^ 2 * ⁅⁅x, y⁆, y⁆ ^ 2
    rw [← c_eq, ← d_eq, ← e_eq, y_cube]

end Sporadic.Janko3.ThreePrimary
