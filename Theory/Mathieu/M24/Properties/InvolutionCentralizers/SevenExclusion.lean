module
public import Theory.Mathieu.M24.Properties.Transitivity
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Defs
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Finite

/-!
# Seven-elements in M₂₄ involution centralizers

Five-transitivity makes a five-point stabilizer have order 48, so an
element of order seven fixes exactly three points. A fixed-point-free
involution cannot act on this odd set. This gives the precise 2B exclusion
used in Aschbacher–Smith 2.5.19, printed pp.560–563.
-/
public section
open Subgroup
namespace Sporadic.Mathieu.M24InvolutionCentralizers

/-- Five-transitivity and the actual M₂₄ order force every element of order
seven to fix exactly three points in the degree-twenty-four action. -/
theorem seven_fixed_card (g : M24) (hg : orderOf g = 7) :
    (g.val.supportᶜ).card = 3 := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hgpow : g.val ^ 7 ^ 1 = 1 := by
    simpa only [map_pow,map_one,Subgroup.subtype_apply,pow_one,hg] using congrArg M24.subtype (pow_orderOf_eq_one g)
  have hmod := Equiv.Perm.card_compl_support_modEq hgpow
  have hlt : g.val.supportᶜ.card < 5 := by
    by_contra hlt
    obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq (show 5 ≤ g.val.supportᶜ.card by omega)
    let R := fixingSubgroup M24 (s : Set (Fin 24))
    have hs5 : (s : Set (Fin 24)).ncard = 5 := by simpa using hcard
    have htrans : MulAction.IsMultiplyPretransitive M24 (Fin 24) (s : Set (Fin 24)).ncard :=
      hs5.symm ▸ m24_isFivePretransitive
    have hi := htrans.index_of_fixingSubgroup_eq (s : Set (Fin 24))
    rw [hs5,Nat.card_fin] at hi
    norm_num [Nat.choose,Nat.factorial] at hi
    have hc := R.index_mul_card
    change (fixingSubgroup M24 (s : Set (Fin 24))).index * Nat.card R = Nat.card M24 at hc
    rw [hi,m24_order] at hc
    have hr : Nat.card R = 48 := by omega
    have hgin : g ∈ R := by
      apply (mem_fixingSubgroup_iff M24).mpr
      intro x hx
      exact Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp (hs hx))
    have ho : orderOf (⟨g,hgin⟩ : R) = 7 := (Subgroup.orderOf_coe ⟨g,hgin⟩).symm.trans hg
    have hd := orderOf_dvd_natCard (⟨g,hgin⟩ : R)
    rw [ho,hr] at hd
    norm_num at hd
  change g.val.supportᶜ.card % 7 = Fintype.card (Fin 24) % 7 at hmod
  norm_num at hmod
  omega

private theorem centralizer_not_seven_of_fixed_point_free (t : M24)
    (htorder : orderOf t = 2) (hfree : ∀ y : Fin 24,t.val y ≠ y) :
    ¬ 7 ∣ Nat.card (centralizer ({t} : Set M24)) := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := (centralizer ({t} : Set M24))) 7 hd
  let g : M24 := x.val
  have hg : orderOf g = 7 := (Subgroup.orderOf_coe x).trans hx
  let P : Type := {y : Fin 24 // y ∈ g.val.supportᶜ}
  have hcard : Fintype.card P = 3 := by
    change Fintype.card {y // y ∈ g.val.supportᶜ} = 3
    rw [Fintype.card_coe]
    exact seven_fixed_card g hg
  have ht : t.val ^ 2 = 1 := by
    simpa only [map_pow,map_one,Subgroup.subtype_apply,htorder] using
      congrArg M24.subtype (pow_orderOf_eq_one t)
  have hcomm : g.val * t.val = t.val * g.val :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.property)
  have hpres (y : Fin 24) (hy : y ∈ g.val.supportᶜ) :
      t.val y ∈ g.val.supportᶜ := by
    apply Finset.mem_compl.mpr
    apply Equiv.Perm.notMem_support.mpr
    have hgy : g.val y = y := Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp hy)
    have he := Equiv.congr_fun hcomm y
    simpa only [Equiv.Perm.mul_apply,hgy] using he
  let u : Equiv.Perm P := t.val.subtypePermOfFintype hpres
  have hu : u ^ 2 ^ 1 = 1 := by
    apply Equiv.ext
    intro y
    apply Subtype.ext
    exact Equiv.congr_fun ht y.val
  have hus : u.support = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro y
    apply Equiv.Perm.mem_support.mpr
    intro he
    exact hfree y.val (congrArg Subtype.val he)
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hm := Equiv.Perm.card_compl_support_modEq hu
  rw [hus,Finset.compl_univ,Finset.card_empty,hcard] at hm
  norm_num [Nat.ModEq] at hm

/-- A fixed-point-free M₂₄ involution cannot centralize an element of order
seven: it would act without fixed points on a three-element set. -/
theorem twoB_centralizer_not_seven : ¬ 7 ∣ Nat.card centralizer2B := by
  apply centralizer_not_seven_of_fixed_point_free involution2B involution2B_order
  have hs : involution2B.val.support = Finset.univ := Finset.eq_univ_of_card _
    (by simpa only [involution2B,Fintype.card_fin] using m24Involution2B_fixed_card)
  intro y
  exact Equiv.Perm.mem_support.mp (by rw [hs]; exact Finset.mem_univ y)

end Sporadic.Mathieu.M24InvolutionCentralizers

