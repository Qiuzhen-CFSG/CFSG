module
public import Theory.Mathieu.M22.Properties.Transitivity
public import Theory.Mathieu.M22.Properties.OuterCentralizers.DesignAction
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Finite

/-!
# Seven-elements in M₂₂ outer centralizers

Three-transitivity makes a three-point stabilizer have order 48. An
element of order seven therefore fixes exactly one point, which every
commuting design automorphism preserves. This excludes seven-elements
from the fixed-point-free row used in Aschbacher–Smith 2.5.19, pp.560–563.
-/
public section
open Subgroup
namespace Sporadic.Mathieu.M22OuterCentralizers

/-- Three-transitivity and the actual M₂₂ order force every element of order
seven to fix exactly one point in the degree-twenty-two action. -/
theorem seven_fixed_card (g : M22) (hg : orderOf g = 7) :
    (g.val.supportᶜ).card = 1 := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hgpow : g.val ^ 7 ^ 1 = 1 := by
    simpa only [map_pow,map_one,Subgroup.subtype_apply,pow_one,hg] using congrArg M22.subtype (pow_orderOf_eq_one g)
  have hmod := Equiv.Perm.card_compl_support_modEq hgpow
  have hlt : g.val.supportᶜ.card < 3 := by
    by_contra hlt
    obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq (show 3 ≤ g.val.supportᶜ.card by omega)
    let R := fixingSubgroup M22 (s : Set (Fin 22))
    have hs3 : (s : Set (Fin 22)).ncard = 3 := by simpa using hcard
    have htrans : MulAction.IsMultiplyPretransitive M22 (Fin 22) (s : Set (Fin 22)).ncard :=
      hs3.symm ▸ m22_isThreePretransitive
    have hi := htrans.index_of_fixingSubgroup_eq (s : Set (Fin 22))
    rw [hs3,Nat.card_fin] at hi
    norm_num [Nat.choose,Nat.factorial] at hi
    have hc := R.index_mul_card
    change (fixingSubgroup M22 (s : Set (Fin 22))).index * Nat.card R = Nat.card M22 at hc
    rw [hi,m22_order] at hc
    have hr : Nat.card R = 48 := by omega
    have hgin : g ∈ R := by
      apply (mem_fixingSubgroup_iff M22).mpr
      intro x hx
      exact Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp (hs hx))
    have ho : orderOf (⟨g,hgin⟩ : R) = 7 := (Subgroup.orderOf_coe ⟨g,hgin⟩).symm.trans hg
    have hd := orderOf_dvd_natCard (⟨g,hgin⟩ : R)
    rw [ho,hr] at hd
    norm_num at hd
  change g.val.supportᶜ.card % 7 = Fintype.card (Fin 22) % 7 at hmod
  norm_num at hmod
  omega

/-- A fixed-point-free design involution cannot centralize an element of
order seven, since such an element fixes a unique point. -/
theorem fixedPointFree_centralizer_not_seven (s : m22DesignAut)
    (hfree : (fixedPoints s).card = 0) :
    ¬ 7 ∣ Nat.card (centralizer s) := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := centralizer s) 7 hd
  let g : M22 := x.val
  have hg : orderOf g = 7 := (Subgroup.orderOf_coe x).trans hx
  have hcard := seven_fixed_card g hg
  obtain ⟨y,hy⟩ := Finset.card_eq_one.mp hcard
  have hgy : g.val y = y := Equiv.Perm.notMem_support.mp
    (Finset.mem_compl.mp (hy.symm ▸ Finset.mem_singleton_self y))
  have hcomm := (mem_centralizer_iff s g).mp x.property
  have he := Equiv.congr_fun hcomm y
  have hsy : g.val (s.val y) = s.val y := by
    simpa only [Equiv.Perm.mul_apply,hgy] using he
  have hm : s.val y ∈ g.val.supportᶜ :=
    Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr hsy)
  rw [hy,Finset.mem_singleton] at hm
  have hyfixed : y ∈ fixedPoints s := (mem_fixedPoints s y).mpr hm
  rw [Finset.card_eq_zero.mp hfree] at hyfixed
  exact Finset.notMem_empty y hyfixed

end Sporadic.Mathieu.M22OuterCentralizers
