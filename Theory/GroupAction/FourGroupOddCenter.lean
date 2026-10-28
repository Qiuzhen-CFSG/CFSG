module

public import Theory.PGroupCore
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupAction.AutomorphismFixedSubgroup
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.Tactic

/-!
# Four-group actions and odd centers

A four-group acting on a nontrivial finite group has a nonidentity actor with
a nonidentity fixed element. Indeed, a fixed-point-free involution acts by
inversion. If two distinct involutions were both fixed-point-free, their
nonidentity product would act trivially.

Apply this to an invariant odd central subgroup. The resulting fixed central
element cannot lie in the two-core, since its order is odd. It therefore
obstructs a self-centralizing two-core in the actor's actual fixed subgroup.

This is the odd-center part of the component elimination in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined 1 March 2004 manuscript,
15.4.18, printed pp.1162–1163. It applies independently of faithfulness and of
any Sylow subgroup. In particular, it handles triple covers by their center,
without replacing the cover by a different concrete group.
-/

open Subgroup
namespace Theory.GroupAction

private theorem exists_fixed_pair {A C : Type*} [Group A] [Group C] [Finite C] [Nontrivial C]
    (ρ : A →* MulAut C) (a b : A) (ha : a ≠ 1) (hb : b ≠ 1)
    (hab : a ≠ b) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) :
    ∃ t : A, t ≠ 1 ∧ ∃ x : C, x ≠ 1 ∧ ρ t x = x := by
  by_contra h
  have hfree (t : A) (ht : t ≠ 1) : MonoidHom.FixedPointFree (ρ t) := by
    intro x hx
    by_contra hxn
    exact h ⟨t, ht, x, hxn, hx⟩
  have hinv (t : A) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) (x : C) : ρ t x = x⁻¹ := by
    apply congrFun ((hfree t ht).coe_eq_inv_of_involutive ?_) x
    intro y
    have hs : ρ t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
    exact congrArg (fun e : MulAut C => e y) hs
  have hp : a * b ≠ 1 := by
    intro he
    have hib : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hb2)
    exact hab ((eq_inv_of_mul_eq_one_left he).trans hib)
  obtain ⟨x, hx⟩ := exists_ne (1 : C)
  apply hx (hfree (a * b) hp x ?_)
  rw [map_mul]
  change ρ a (ρ b x) = x
  rw [hinv b hb hb2, map_inv, hinv a ha ha2, inv_inv]

/-- Some nonidentity member of a four-group fixes a nonidentity element of
any nontrivial finite group on which it acts. -/
public theorem exists_nontrivial_fixed_of_elementaryFour {A C : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group C] [Finite C] [Nontrivial C] (hA : Nat.card A = 4)
    (ρ : A →* MulAut C) :
    ∃ t : A, t ≠ 1 ∧ ∃ x : C, x ≠ 1 ∧ ρ t x = x := by
  classical
  let := Fintype.ofFinite A
  have hc : Fintype.card A = 4 := by simpa using hA
  have hnt : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({1, a} : Finset A).card < Finset.univ.card from by
      rw [Finset.card_univ, hc, Finset.card_pair (Ne.symm ha)]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  have hs (t : A) : t ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) t
  exact exists_fixed_pair ρ a b ha hb.1 (Ne.symm hb.2) (hs a) (hs b)

/-- A fixed nonidentity central element of odd order prevents the fixed
subgroup from having self-centralizing two-core. -/
public theorem not_selfCentralizing_twoCore_fixedSubgroup_of_odd_central_element {K : Type*} [Group K]
    (α : MulAut K) (x : K) (hx : x ≠ 1) (hZ : x ∈ center K)
    (hodd : Odd (orderOf x)) (hf : α x = x) :
    ¬ centralizer (pCore 2 α.fixedSubgroup : Set α.fixedSubgroup) ≤
      pCore 2 α.fixedSubgroup := by
  intro hchar
  let y : α.fixedSubgroup := ⟨x, (MulAut.mem_fixedSubgroup α x).mpr hf⟩
  have hy : y ∈ pCore 2 α.fixedSubgroup := hchar (by
    intro z _
    apply Subtype.ext
    exact mem_center_iff.mp hZ z)
  obtain ⟨n, hn⟩ := pCore_isPGroup (p := 2) ⟨y, hy⟩
  have hpow : x ^ (2 ^ n) = 1 :=
    congrArg (fun z : pCore 2 α.fixedSubgroup => (z : K)) hn
  have horder : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes
    ((Nat.coprime_two_left.mpr hodd).pow_left n)
    (orderOf_dvd_of_pow_eq_one hpow) (dvd_refl _)
  exact hx (orderOf_eq_one_iff.mp horder)

/-- A four-group action on a group with a nontrivial characteristic odd
central subgroup has a fixed subgroup whose two-core is not self-centralizing. -/
public theorem exists_fixedSubgroup_not_selfCentralizing_twoCore_of_characteristic_odd_center {A K : Type*} [Group A] [Finite A]
    [IsElementaryAbelian 2 A] [Group K] (C : Subgroup K) [C.Characteristic]
    [Finite C] (hc : C ≤ center K) (hodd : Odd (Nat.card C)) (hne : C ≠ ⊥)
    (hA : Nat.card A = 4) (ρ : A →* MulAut K) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup := by
  let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hne
  obtain ⟨a, ha, x, hx, hf⟩ := exists_nontrivial_fixed_of_elementaryFour hA ((MulAut.characteristic C).comp ρ)
  refine ⟨a, ha, not_selfCentralizing_twoCore_fixedSubgroup_of_odd_central_element (ρ a) x ?_ (hc x.property) ?_ ?_⟩
  · exact fun h => hx (Subtype.ext h)
  · rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hodd (orderOf_dvd_natCard x)
  · exact congrArg Subtype.val hf

/-- The whole odd center gives the same obstruction for every four-group action. -/
public theorem exists_fixedSubgroup_not_selfCentralizing_twoCore_of_odd_center
    {A K : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group K] [Finite K] (hodd : Odd (Nat.card (center K))) (hne : center K ≠ ⊥)
    (hA : Nat.card A = 4) (ρ : A →* MulAut K) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup :=
  exists_fixedSubgroup_not_selfCentralizing_twoCore_of_characteristic_odd_center
    (center K) le_rfl hodd hne hA ρ

end Theory.GroupAction
