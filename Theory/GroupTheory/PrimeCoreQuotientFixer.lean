module
public import Theory.GroupTheory.PrimeCentralizerExclusion
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Prime-order fixers of a two-core quotient

Suppose p occurs only once in the ambient group order, divides the order of B,
and is odd. A p-element normalizing B belongs to B, by Sylow conjugacy inside
their join. If it centralizes B/O₂(B), and that quotient is centerless, it
then belongs to O₂(B), which is impossible.

Unlike a full centralizer exclusion this uses only the action modulo the
intrinsic two-core. The source application is the order-31 torus in the J₄
branch of Aschbacher--Smith 4.3.16, printed p.618.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Theory.GroupTheory
variable {A : Type*} [Group A] [Finite A]
/-- A prime occurring once cannot fix a centerless two-core quotient containing that prime. -/
theorem prime_order_not_trivial_on_twoCore_quotient
    (B : Subgroup A) (hz : center (B ⧸ pCore 2 B) = ⊥)
    {p : ℕ} [Fact p.Prime] (hp : Nat.Coprime 2 p)
    (hd : p ∣ Nat.card B) (hsq : ¬ p^2 ∣ Nat.card A)
    (a : A) (hn : a ∈ normalizer (B : Set A))
    (hc : ∀ b ∈ B, ⁅a,b⁆ ∈ (pCore 2 B).map B.subtype) : orderOf a ≠ p := by
  intro ho
  let H := B ⊔ zpowers a
  let C := B.subgroupOf H
  let e : C ≃* B := subgroupOfEquivOfLe le_sup_left
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le B.le_normalizer (zpowers_le.mpr hn))
  let x : H := ⟨a,mem_sup_right (mem_zpowers a)⟩
  have hx : x ∈ C := mem_normal_of_prime_order_of_square_not_dvd C
    (by rwa [Nat.card_congr e.toEquiv]) x (by simpa only [x,orderOf_mk] using ho)
    (fun h => hsq (h.trans H.card_subgroup_dvd_card))
  let y : B := ⟨a,hx⟩
  let q := QuotientGroup.mk' (pCore 2 B)
  have hq : q y ∈ center (B ⧸ pCore 2 B) := by
    apply mem_center_iff.mpr
    intro z
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
    apply (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
    rw [←map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨w,hw,he⟩ := hc b b.property
    have he' : w = ⁅y,b⁆ := Subtype.ext he
    exact he' ▸ hw
  rw [hz,mem_bot] at hq
  have hy : y ∈ pCore 2 B := (QuotientGroup.eq_one_iff _).mp hq
  have hh := (pCore_isPGroup (p := 2) (G := B)).orderOf_coprime hp ⟨y,hy⟩
  have he : orderOf (⟨y,hy⟩ : pCore 2 B) = p := by
    exact (orderOf_coe (⟨y,hy⟩ : pCore 2 B)).symm.trans ((orderOf_coe y).symm.trans ho)
  rw [he,Nat.coprime_self] at hh
  exact (Fact.out : p.Prime).ne_one hh
end Theory.GroupTheory
