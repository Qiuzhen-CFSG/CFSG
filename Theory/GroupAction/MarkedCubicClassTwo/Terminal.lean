module

public import Theory.GroupAction.MarkedCubicClassTwo.Defs
public import Mathlib.GroupTheory.FixedPointFree

/-!
# The cyclic fixed-subgroup contradiction in the third layer

Suppose the two Frattini joins are inverted modulo a normal cubic subgroup V.
An involution fixes the opposite cubic marking, disjoint from V. Cyclicity
of its fixed subgroup then forbids any nonidentity fixed point in V, by
uniqueness of a cubic subgroup in a cyclic group. Odd order also forbids
fixed points on the inverted quotient. Thus the full join is fixed-point-free
and is inverted, hence abelian.

The derived subgroup belongs to both abelian joins and centralizes their
join, the whole group. This is the required correction of the last sentence
in the three-group branch of Aschbacher–Smith F.6.16, printed p.308:
centrality of V itself would not contradict class three.
-/

public section

open Subgroup
namespace MarkedCubicClassTwo
variable {P : Type*} [Group P] [Finite P]

/-- A fixed cubic marking excludes fixed cubic elements in a disjoint subgroup. -/
theorem fixed_eq_one_of_cubic_disjoint (a : MulAut P)
    (B V : Subgroup P) (hB : Nat.card B = 3) (hV : Nat.card V = 3)
    (hfix : ∀ x ∈ B, a x = x) (hd : Disjoint B V)
    (hc : IsCyclic a.fixedSubgroup) {x : P} (hx : x ∈ V) (hax : a x = x) : x = 1 := by
  classical
  let := hc
  let : Fintype a.fixedSubgroup := Fintype.ofFinite _
  have hBC : B ≤ a.fixedSubgroup := fun y hy => (MulAut.mem_fixedSubgroup a y).mpr (hfix y hy)
  have hcard : Nat.card (B.subgroupOf a.fixedSubgroup) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv).trans hB
  have hpow : (⟨x, (MulAut.mem_fixedSubgroup a x).mpr hax⟩ : a.fixedSubgroup) ^
      Nat.card (B.subgroupOf a.fixedSubgroup) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hcard, ← hV]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : V)))
  let C := B.subgroupOf a.fixedSubgroup
  have hBcube (y : C) : (y : a.fixedSubgroup) ^ 3 = 1 := by
    rw [← hcard]
    exact congrArg Subtype.val (pow_card_eq_one' (x := y))
  have hsub : (C : Set a.fixedSubgroup).toFinset ⊆
      Finset.univ.filter (fun y : a.fixedSubgroup => y ^ 3 = 1) := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y,
      hBcube ⟨y, Set.mem_toFinset.mp hy⟩⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    have hbound := IsCyclic.card_pow_eq_one_le (α := a.fixedSubgroup) (by decide : 0 < 3)
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    change _ ≤ Nat.card C
    rw [show Nat.card C = 3 from hcard]
    exact hbound)
  have hxB : (⟨x, (MulAut.mem_fixedSubgroup a x).mpr hax⟩ : a.fixedSubgroup) ∈ C := by
    apply Set.mem_toFinset.mp
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hcard] using hpow⟩
  exact disjoint_def.mp hd hxB hx

/-- Inversion modulo a cubic kernel lifts when the fixed subgroup is cyclic. -/
theorem inverts_of_cyclic_fixed (hodd : Odd (Nat.card P))
    (a : MulAut P) (ha : a ^ 2 = 1) (B V X : Subgroup P) [V.Normal]
    (hB : Nat.card B = 3) (hV : Nat.card V = 3) (hVX : V ≤ X)
    (hfix : ∀ x ∈ B, a x = x) (hd : Disjoint B V)
    (hc : IsCyclic a.fixedSubgroup)
    (hinv : ∀ x ∈ X, a x * x ∈ V) :
    (∀ x ∈ X, a x = x⁻¹) ∧ IsMulCommutative X := by
  let q := QuotientGroup.mk' V
  have hqodd : Odd (Nat.card (P ⧸ V)) :=
    Odd.of_dvd_nat hodd (card_dvd_of_surjective q (QuotientGroup.mk'_surjective V))
  have hstable : ∀ x ∈ X, a x ∈ X := by
    intro x hx
    simpa only [mul_inv_cancel_right] using X.mul_mem (hVX (hinv x hx)) (X.inv_mem hx)
  let f : X →* X := a.toMonoidHom.restrict hstable
  have hf2 : Function.Involutive f := by
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun ha (x : P)
  have hf : MonoidHom.FixedPointFree f := by
    intro x hx
    have hax : a (x : P) = x := congrArg Subtype.val hx
    have hxV : (x : P) ∈ V := by
      apply (QuotientGroup.eq_one_iff _).mp
      have hsq : (q (x : P)) ^ 2 = 1 := by
        rw [pow_two, ← map_mul]
        exact (QuotientGroup.eq_one_iff _).mpr (by simpa only [hax] using hinv x x.property)
      exact hqodd.coprime_two_right.pow_left_bijective.injective
        (hsq.trans (one_pow 2).symm)
    exact Subtype.ext (fixed_eq_one_of_cubic_disjoint a B V hB hV hfix hd hc hxV hax)
  refine ⟨?_, ⟨⟨fun x y => (hf.commute_all_of_involutive hf2 x y).eq⟩⟩⟩
  intro x hx
  exact congrArg Subtype.val (congrFun (hf.coe_eq_inv_of_involutive hf2) ⟨x, hx⟩)

/-- Both abelian Frattini joins centralize their common derived subgroup. -/
theorem commutator_le_center_of_marked_quotient
    (hodd : Odd (Nat.card P)) (A B V : Subgroup P) [V.Normal]
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) (hgen : A ⊔ B = ⊤)
    (hV : Nat.card V = 3) (hVD : V ≤ _root_.commutator P)
    (hAV : Disjoint A V) (hBV : Disjoint B V)
    (a b : MulAut P) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hafix : ∀ x ∈ B, a x = x) (hbfix : ∀ x ∈ A, b x = x)
    (hac : IsCyclic a.fixedSubgroup) (hbc : IsCyclic b.fixedSubgroup)
    (hainv : ∀ x ∈ A ⊔ _root_.commutator P, a x * x ∈ V)
    (hbinv : ∀ x ∈ B ⊔ _root_.commutator P, b x * x ∈ V) :
    _root_.commutator P ≤ center P := by
  have hX := (inverts_of_cyclic_fixed hodd a ha B V (A ⊔ _root_.commutator P)
    hB hV (hVD.trans le_sup_right) hafix hBV hac hainv).2
  have hY := (inverts_of_cyclic_fixed hodd b hb A V (B ⊔ _root_.commutator P)
    hA hV (hVD.trans le_sup_right) hbfix hAV hbc hbinv).2
  let := hX
  let := hY
  have hAC : A ≤ centralizer (_root_.commutator P : Set P) := by
    intro x hx z hz
    exact setLike_mul_comm (s := A ⊔ _root_.commutator P)
      (show z ∈ _ from mem_sup_right hz) (show x ∈ _ from mem_sup_left hx)
  have hBC : B ≤ centralizer (_root_.commutator P : Set P) := by
    intro x hx z hz
    exact setLike_mul_comm (s := B ⊔ _root_.commutator P)
      (show z ∈ _ from mem_sup_right hz) (show x ∈ _ from mem_sup_left hx)
  have htop : (⊤ : Subgroup P) ≤ centralizer (_root_.commutator P : Set P) :=
    hgen ▸ sup_le hAC hBC
  simpa only [coe_top, centralizer_univ] using le_centralizer_iff.mp htop


end MarkedCubicClassTwo
