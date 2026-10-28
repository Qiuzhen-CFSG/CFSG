module
public import Theory.GroupAction.PerfectFixedCover
public import Theory.GroupAction.SubgroupConjugation
public import Theory.ElementaryAbelian.Basic

/-!
# Centralizing transporters in elementary two-subgroups

Suppose an odd subgroup normalizes an elementary abelian two-subgroup and
fixes two points in the same orbit of that two-subgroup. Coprime fixed-point
lifting in the point-stabilizer coset gives a transporter centralizing the
whole odd subgroup. It remains an involution in the original elementary
subgroup. No faithfulness or finiteness of the ambient group is required.

This is the coprime adjustment used for the cubic endpoint in DGS,
*Groups and Graphs* (1985), (14.2), pp.210--211.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction
variable {G X : Type*} [Group G] [MulAction G X]

/-- A fixed orbit pair has an involutive transporter centralizing the odd actor. -/
theorem exists_elementary_centralizing_transporter
    (E C : Subgroup G) [Finite E] [Finite C] [IsElementaryAbelian 2 E]
    (hCE : C ≤ normalizer (E : Set G)) (hodd : Odd (Nat.card C))
    (a b : X) (ha : ∀ c ∈ C, c • a = a) (hb : ∀ c ∈ C, c • b = b)
    (x : E) (hx : (x : G) • a = b) :
    ∃ t ∈ E, t ∈ centralizer (C : Set G) ∧ t*t=1 ∧ t • a=b := by
  let _ : MulDistribMulAction C E := conjMulDistribMulActionOfLeNormalizer C E hCE
  let N := MulAction.stabilizer E a
  let _ : IsInvariant C E N := by
    constructor
    intro c y
    change (y : G) • a=a ↔ ((c : G)*(y : G)*(c : G)⁻¹) • a=a
    constructor
    · intro hy
      rw [mul_smul,mul_smul,ha _ (C.inv_mem c.property),hy,ha _ c.property]
    · intro hy
      have hci : (c : G)⁻¹ • a=a := ha _ (C.inv_mem c.property)
      rw [mul_smul,mul_smul,hci] at hy
      have hh := congrArg (fun z : X => (c : G)⁻¹ • z) hy
      simpa only [inv_smul_smul,hci] using hh
  have hcop : Nat.Coprime (Nat.card C) (Nat.card N) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).to_subgroup N |>.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  obtain ⟨n,hn⟩ := exists_fixed_mul_of_solvable_coprime_displacement
    (A := C) N (Group.isSolvable_of_comm (mul_comm' (M := N))) hcop x (by
      intro c
      change ((x : G)⁻¹*((c : G)*(x : G)*(c : G)⁻¹)) • a=a
      rw [mul_smul,mul_smul,mul_smul,ha _ (C.inv_mem c.property),hx,hb _ c.property]
      rw [←hx,inv_smul_smul])
  let t : E := x*n
  refine ⟨t,t.property,?_,?_,?_⟩
  · apply mem_centralizer_iff.mpr
    intro c hc
    have he := congrArg Subtype.val (hn (⟨c,hc⟩ : C))
    change c*(t : G)*c⁻¹=t at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (t : G) t.property
  · change ((x : G)*(n : E)) • a=b
    rw [mul_smul,show ((n : E) : G) • a=a from n.property,hx]

end Theory.GroupAction
