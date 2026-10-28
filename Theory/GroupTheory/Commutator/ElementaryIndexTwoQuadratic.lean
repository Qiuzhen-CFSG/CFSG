module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# Quadratic action through a centralizing subgroup of index two

Let V be an elementary abelian two-subgroup of an arbitrary group and let
T normalize V. If a subgroup Q of index two in T centralizes V, then the
iterated commutator [[V,T],T] is trivial. No finiteness assumption on the
ambient group or on V is needed.

For a commutator generator [v,a], index two gives a² in Q. Conjugation by a
therefore swaps the two commuting involutions v and a*v*a⁻¹ whose product
is [v,a], and fixes that generator. An actor b outside Q differs from a by
an element of Q when a is outside Q; elements of Q already centralize the
generator because it lies in V. Thus every actor fixes every generator,
and the centralizer subgroup contains [V,T].

This elementary calculation supplies the edge-intersection quadraticity
step of Stellmacher (8.2), Journal of Algebra 190 (1997), pp.37–38, as
recorded in refs/latex/stellmacher-n-group.tex and the journal scan.
-/

open scoped commutatorElement IsMulCommutative
namespace Subgroup

private theorem involution_conjugation_fixes_commutator
    {G : Type*} [Group G] (V : Subgroup G) [IsElementaryAbelian 2 V]
    (a v : G) (hv : v ∈ V) (ha : a ∈ normalizer (V : Set G))
    (hcent : a * a ∈ centralizer (V : Set G)) :
    a * ⁅v, a⁆ * a⁻¹ = ⁅v, a⁆ := by
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left
    (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv)
  have hav : a * v * a⁻¹ ∈ V := (mem_normalizer_iff.mp ha v).mp hv
  have hc : (a * a) * v = v * (a * a) := (mem_centralizer_iff.mp hcent v hv).symm
  have hconj : a * (a * v * a⁻¹) * a⁻¹ = v := by
    calc
      _ = ((a * a) * v) * (a * a)⁻¹ := by group
      _ = (v * (a * a)) * (a * a)⁻¹ := by rw [hc]
      _ = v := by group
  have hcomm : (a * v * a⁻¹) * v = v * (a * v * a⁻¹) :=
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := V)).comm ⟨_, hav⟩ ⟨v, hv⟩)
  simp only [commutatorElement_def, hvi]
  calc
    a * (v * a * v * a⁻¹) * a⁻¹ =
      (a * v * a⁻¹) * (a * (a * v * a⁻¹) * a⁻¹) := by group
    _ = (a * v * a⁻¹) * v := by rw [hconj]
    _ = v * (a * v * a⁻¹) := hcomm
    _ = v * a * v * a⁻¹ := by group

/-- A centralizing subgroup of index two makes the action on an elementary two-group quadratic. -/
public theorem commutator_commutator_eq_bot_of_centralizing_index_two
    {G : Type*} [Group G] (V Q T : Subgroup G)
    [IsElementaryAbelian 2 V]
    (hTV : T ≤ normalizer (V : Set G)) (_hQT : Q ≤ T)
    (hQV : Q ≤ centralizer (V : Set G)) (hidx : Q.relIndex T = 2) :
    ⁅⁅V, T⁆, T⁆ = ⊥ := by
  have hi : (Q.subgroupOf T).index = 2 := hidx
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply commutator_le.mpr
  intro v hv a ha
  have hcv : ⁅v, a⁆ ∈ V :=
    le_normalizer_iff_commutator_le_left.mp hTV (commutator_mem_commutator hv ha)
  rw [mem_centralizer_iff]
  intro b hb
  by_cases haQ : a ∈ Q
  · have hav : v * a = a * v := mem_centralizer_iff.mp (hQV haQ) v hv
    have hone : ⁅v, a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hav
    simp [hone]
  by_cases hbQ : b ∈ Q
  · exact (mem_centralizer_iff.mp (hQV hbQ) _ hcv).symm
  have hsq : a * a ∈ Q :=
    (Q.subgroupOf T).mul_self_mem_of_index_two hi ⟨a, ha⟩
  have hfix := involution_conjugation_fixes_commutator V a v hv (hTV ha) (hQV hsq)
  have hqa : b * a⁻¹ ∈ Q := by
    have hh := (Q.subgroupOf T).mul_mem_iff_of_index_two hi
      (a := (⟨b, hb⟩ : T)) (b := (⟨a, ha⟩ : T)⁻¹)
    apply hh.mpr
    change b ∈ Q ↔ a⁻¹ ∈ Q
    simp only [inv_mem_iff, hbQ, haQ]
  have hqcomm : ⁅v, a⁆ * (b * a⁻¹) = (b * a⁻¹) * ⁅v, a⁆ :=
    mem_centralizer_iff.mp (hQV hqa) _ hcv
  have hafix : a * ⁅v, a⁆ = ⁅v, a⁆ * a := mul_inv_eq_iff_eq_mul.mp hfix
  symm
  calc
    ⁅v, a⁆ * b = ⁅v, a⁆ * (b * a⁻¹) * a := by group
    _ = (b * a⁻¹) * ⁅v, a⁆ * a := by rw [hqcomm]
    _ = (b * a⁻¹) * (a * ⁅v, a⁆) := by rw [mul_assoc, ← hafix]
    _ = b * ⁅v, a⁆ := by group

end Subgroup
