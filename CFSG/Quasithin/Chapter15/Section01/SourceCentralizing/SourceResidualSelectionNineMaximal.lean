module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SourceCases
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Maximal Sylow subgroups in the original elementary-nine action

An index-three subgroup would give a permutation action of degree three.
Every involution of the actual action group lies in a cyclic Sylow subgroup
of order four, hence is a square there and acts trivially on the three cosets.
The marked commutator relation then puts the endpoint's entire nine-kernel
inside the permutation kernel. This is impossible in a subgroup of order
twelve. The literal Sylow subgroup consequently has no proper overgroup.

The proof uses the original `SourceCases.Nine` witness and does not replace
the action or require a global Thompson residual premise.

Source: Aschbacher--Smith 15.1.2(5) and the nine-action row of 15.1.14,
printed pp.1086 and 1091.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD
universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem involution_killed_by_order_six
    (hS : ∀ Q : Sylow 2 D, IsCyclic Q ∧ Nat.card Q = 4)
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 6)
    (f : D →* H) (t : D) (ht : orderOf t = 2) : f t = 1 := by
  classical
  have hz : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ht]; decide)
  obtain ⟨Q,hQ⟩ := hz.exists_le_sylow
  let := (hS Q).1
  let tQ : Q := ⟨t,hQ (mem_zpowers t)⟩
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  rw [(hS Q).2] at hg
  have hgt : g ^ 2 = tQ := IsCyclic.eq_of_orderOf_eq_two
    (by rw [orderOf_pow,hg]; decide)
    (by rw [← Subgroup.orderOf_coe]; exact ht)
  have hd4 : orderOf (f (g : D)) ∣ 4 := by
    rw [←hg,←Subgroup.orderOf_coe]
    exact orderOf_map_dvd f g
  have hd6 : orderOf (f (g : D)) ∣ 6 := hH ▸ orderOf_dvd_natCard (f (g : D))
  have hd2 : orderOf (f (g : D)) ∣ 2 := by
    simpa only [show Nat.gcd 4 6 = 2 by decide] using Nat.dvd_gcd hd4 hd6
  have he : (g : D) ^ 2 = t := congrArg Subtype.val hgt
  rw [←he,map_pow]
  exact orderOf_dvd_iff_pow_eq_one.mp hd2

/-- The elementary-nine source action has no subgroup of index three. -/
theorem SourceCases.Nine.no_index_three
    {ρ : Representation (ZMod 2) D V} {S : Subgroup D}
    (h : SourceCases.Nine ρ S) (A : Subgroup D) : A.index ≠ 3 := by
  classical
  intro hA
  obtain ⟨l,h9,_,hD,_,hS,_,_⟩ := h
  let := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let := l.normal
  let K := Jhat ρ
  let f := MulAction.toPermHom D (D ⧸ A)
  have hfcard : Nat.card (Equiv.Perm (D ⧸ A)) = 6 := by
    rw [Nat.card_perm,←Subgroup.index_eq_card,hA]; decide
  have ht : f (l.involution : D) = 1 :=
    involution_killed_by_order_six hS hfcard f l.involution
      (by rw [Subgroup.orderOf_coe]; exact l.order_two)
  let g := f.comp K.subtype
  have hg : l.kernel.map g = ⊥ := by
    rw [←l.commutator,map_commutator,MonoidHom.map_zpowers]
    change ⁅l.kernel.map g,zpowers (f (l.involution : D))⁆ = ⊥
    rw [ht,zpowers_one_eq_bot,commutator_bot_right]
  have hle : l.kernel.map K.subtype ≤ A := by
    apply (map_le_iff_le_comap).mpr
    have hker : l.kernel ≤ g.ker := (Subgroup.map_eq_bot_iff l.kernel).mp hg
    intro x hx
    apply A.normalCore_le
    rw [A.normalCore_eq_ker]
    exact hker hx
  have hc : Nat.card A = 12 := by
    have hh := A.card_mul_index
    rw [hA,hD] at hh
    omega
  have hd : 9 ∣ 12 := by
    have hh := card_dvd_of_le hle
    rw [card_map_of_injective K.subtype_injective,h9.card_kernel,hc] at hh
    exact hh
  norm_num at hd

/-- A Sylow two-subgroup is maximal in the literal elementary-nine source action. -/
theorem SourceCases.Nine.sylow_isCoatom
    {ρ : Representation (ZMod 2) D V} {S : Subgroup D}
    (h : SourceCases.Nine ρ S) (Q : Sylow 2 D) : IsCoatom (Q : Subgroup D) := by
  have hD : Nat.card D = 36 := h.choose_spec.2.2.1
  have hQ : Nat.card Q = 4 := (h.choose_spec.2.2.2.2.1 Q).2
  have hi : (Q : Subgroup D).index = 9 := by
    have hh := (Q : Subgroup D).card_mul_index
    rw [hQ,hD] at hh
    omega
  refine ⟨?_,?_⟩
  · intro he
    rw [he,index_top] at hi
    omega
  · intro A hQA
    have hd : A.index ∣ 3^2 := by
      change A.index ∣ 9
      rw [←hi]
      exact index_dvd_of_le hQA.le
    obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    interval_cases n
    · exact index_eq_one.mp (by simpa using he)
    · exact (h.no_index_three A (by simpa using he)).elim
    · have hrel : (Q : Subgroup D).relIndex A = 1 := by
        have hh := relIndex_mul_index hQA.le
        rw [hi,he] at hh
        norm_num only [Nat.reducePow] at hh
        omega
      exact (hQA.not_ge (relIndex_eq_one.mp hrel)).elim
end CFSG.Quasithin.Chapter15.Section01
