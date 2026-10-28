module
public import Theory.GroupTheory.OrderFourTransfer
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.GroupTheory.IndexNormal

/-!
# Transfer through a cyclic quotient of order four

Suppose H contains a Sylow two-subgroup T and H/B is cyclic of order four.
Compose the quotient map with its order-two quotient. This character kills
all involutions of T. Order-four transfer therefore conjugates any element
of order four into its kernel, and the square of that conjugate lies in B.
Only normality of B in H is required.

This supplies the cyclic-four exclusion for the actual opposite centralizer
in Aschbacher--Smith 14.3.22, printed p.999, using the order-four form of
Thompson transfer from `OrderFourTransfer`.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Sylow
variable {G : Type*} [Group G] [Finite G]

/-- A cyclic four quotient of an overgroup of T detects the square of a
conjugate of every order-four element in T. -/
theorem exists_isConj_square_mem_of_cyclic_four_quotient
    (T : Sylow 2 G)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (H : Subgroup G) (hTH : (T:Subgroup G)≤H)
    (B : Subgroup H) [B.Normal] [IsCyclic (H⧸B)]
    (hc : Nat.card (H⧸B)=4) (x : T) (hx : orderOf x=4) :
    ∃ y : T, IsConj (x:G) (y:G) ∧ (inclusion hTH y)^2∈B := by
  let Q := H⧸B
  let : CommGroup Q := IsCyclic.commGroup
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G:=Q) 2 (by rw [hc];decide)
  let W := zpowers v
  have hWc : Nat.card W=2 := by rw [Nat.card_zpowers,hv]
  have hWi : W.index=2 := by
    have hh := W.card_mul_index
    rw [hWc,hc] at hh
    omega
  let : W.Normal := inferInstance
  have htarget : Nat.card (Q⧸W)=2 := hWi
  let : IsCyclic (Q⧸W) := isCyclic_of_prime_card htarget
  let : CommGroup (Q⧸W) := IsCyclic.commGroup
  let q : T →* Q := (QuotientGroup.mk' B).comp (inclusion hTH)
  let χ : T →* (Q⧸W) := (QuotientGroup.mk' W).comp q
  have hi (y : T) (hy : y^2=1) : χ y=1 := by
    apply (QuotientGroup.eq_one_iff (q y)).mpr
    by_cases he : q y=1
    · exact he ▸ W.one_mem
    · have htwo : orderOf (q y)=2 := orderOf_eq_prime (by rw [←map_pow,hy,map_one]) he
      exact (IsCyclic.eq_of_orderOf_eq_two htwo hv).symm ▸ mem_zpowers v
  obtain ⟨y,hxy,hy⟩ := T.exists_isConj_ker_of_order_four hno χ htarget hi x hx
  have hyW : q y∈W := (QuotientGroup.eq_one_iff (q y)).mp hy
  have hysq : (q y)^2=1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    have hd : orderOf (⟨q y,hyW⟩ : W) ∣ Nat.card W :=
      _root_.orderOf_dvd_natCard (⟨q y,hyW⟩ : W)
    simpa only [←orderOf_coe,hWc] using hd
  refine ⟨y,hxy,(QuotientGroup.eq_one_iff ((inclusion hTH y)^2)).mp ?_⟩
  change q (y^2)=1
  rwa [map_pow]
end Sylow
