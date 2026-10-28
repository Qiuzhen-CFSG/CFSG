module

public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Odd subgroups in a commuting centralizer product

If E commutes with L and Y is self-centralizing in L, the centralizer of
the literal image of Y inside EL is EY. If E has exponent two, every
odd-order subgroup of EY lies in Y: take a square root in the odd subgroup,
decompose it in the commuting factors, and square away its E component.

The last theorem applies this argument to an element centralizer inside an
odd subgroup. It is the local input to generation by four-group centralizers
in Aschbacher–Smith, J.2.10, printed p.438 (PDF p.449), refs/quasithin.pdf.
-/

@[expose] public section
open scoped Pointwise
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- Compute the centralizer using the literal inclusion of Y into the ambient group. -/
theorem centralizer_inf_commuting_product (E L : Subgroup G) (Y : Subgroup L)
    (hEL : E ≤ centralizer (L : Set G))
    (hY : centralizer (Y : Set L) = Y) :
    centralizer (Y.map L.subtype : Set G) ⊓ (E ⊔ L) = Y.map L.subtype ⊔ E := by
  let YG := Y.map L.subtype
  have hYL : YG ≤ L := map_subtype_le Y
  have hEC : E ≤ centralizer (YG : Set G) := hEL.trans (centralizer_le hYL)
  have hLC : L ⊓ centralizer (YG : Set G) = YG := by
    rw [← map_centralizer_subtype, hY]
  have hYC : YG ≤ centralizer (YG : Set G) := hLC.ge.trans inf_le_right
  apply le_antisymm
  · intro x hx
    have hprod : x ∈ (E : Set G) * L := by
      rw [← coe_mul_of_right_le_normalizer_left E L
        ((le_centralizer_iff.mp hEL).trans (centralizer_le_normalizer _))]
      exact hx.2
    obtain ⟨e, he, l, hl, rfl⟩ := hprod
    have hlC : l ∈ centralizer (YG : Set G) :=
      (mul_mem_cancel_left (hEC he)).mp hx.1
    exact (YG ⊔ E).mul_mem
      ((show E ≤ YG ⊔ E from le_sup_right) he)
      ((show YG ≤ YG ⊔ E from le_sup_left) (hLC.le ⟨hl, hlC⟩))
  · exact sup_le (le_inf hYC (hYL.trans le_sup_right))
      (le_inf hEC le_sup_left)

/-- An odd subgroup cannot have a nontrivial component in the commuting exponent-two factor. -/
theorem odd_subgroup_le_of_commuting_square_one_factor
    (Y E P : Subgroup G) [Finite P] (hodd : Odd (Nat.card P))
    (hEP : E ≤ centralizer (Y : Set G)) (hE : ∀ e ∈ E, e ^ 2 = 1)
    (hP : P ≤ Y ⊔ E) : P ≤ Y := by
  intro x hx
  obtain ⟨u, hu⟩ := hodd.coprime_two_right.pow_left_bijective.surjective (⟨x, hx⟩ : P)
  have hum : (u : G) ∈ (Y : Set G) * E := by
    rw [← coe_mul_of_right_le_normalizer_left Y E
      (hEP.trans (centralizer_le_normalizer _))]
    exact hP u.property
  obtain ⟨y, hy, e, he, heq⟩ := hum
  have hc : Commute y e := mem_centralizer_iff.mp (hEP he) y hy
  have hxpow : (u : G) ^ 2 = x := congrArg Subtype.val hu
  rw [← hxpow, ← heq, hc.mul_pow, hE e he, mul_one]
  exact Y.pow_mem hy 2

/-- The odd element-centralizer containment used in the four-group generation argument. -/
theorem odd_centralizer_le_of_commuting_product
    (Y E P : Subgroup G) [Finite G] (hodd : Odd (Nat.card P))
    (hEP : E ≤ centralizer (Y : Set G)) (hE : ∀ e ∈ E, e ^ 2 = 1)
    (hP : P ≤ centralizer (Y : Set G)) {s : G}
    (hC : centralizer (Y : Set G) ⊓ centralizer ({s} : Set G) = Y ⊔ E) :
    P ⊓ centralizer ({s} : Set G) ≤ Y := by
  apply odd_subgroup_le_of_commuting_square_one_factor Y E
    (P ⊓ centralizer ({s} : Set G))
    (hodd.of_dvd_nat (card_dvd_of_le inf_le_left)) hEP hE
  exact (inf_le_inf_right _ hP).trans_eq hC

end Subgroup
