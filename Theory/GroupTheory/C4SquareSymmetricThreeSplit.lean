module
public import Theory.GroupAction.C4SquareCubicBasis
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.IndexNormal
/-!
# Splitting the center-free homocyclic-square vertex

In an order-96 group with a self-centralizing normal C₄ × C₄ subgroup,
the normalizer of each cubic subgroup is a complement to that subgroup.
The cubic acts without fixed points. Frattini's argument in its order-48
product with the kernel supplies the whole ambient supplement. Thus a
symmetric-three quotient gives an actual symmetric-three complement.

Source: Aschbacher–Smith F.1.12(I)(8), printed p.263. All subgroups and
conjugation actions remain the original ones.
-/
public section
open Subgroup
open scoped Pointwise
namespace C4SquareExtension
variable {G : Type*} [Group G] [Finite G]
theorem cubic_normalizer_complement
    (Q : Subgroup G) [Q.Normal] (e : Q ≃* Model)
    (hG : Nat.card G=96) (hself : centralizer (Q : Set G) ≤ Q)
    (c : G) (hc : orderOf c=3) :
    Q.IsComplement' (normalizer (zpowers c : Set G)) := by
  have hQ : Nat.card Q=16 := by rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card]; decide
  let C := zpowers c
  have hC : Nat.card C=3 := by rw [Nat.card_zpowers,hc]
  have hd : Disjoint Q C := disjoint_of_coprime_natCard (by rw [hQ,hC]; decide)
  have hcQ : c∉Q := by
    intro h
    have he : c=1 := (disjoint_iff_inf_le.mp hd) ⟨h,mem_zpowers c⟩
    simp [he] at hc
  let a : MulAut Q := MulAut.conjNormal c
  have ha : a^3=1 := by
    rw [←map_pow,show c^3=1 from hc ▸ pow_orderOf_eq_one c,map_one]
  have hn : a≠1 := by
    intro he
    apply hcQ
    apply hself
    rw [mem_centralizer_iff]
    intro q hq
    have hh : c*q*c⁻¹=q := by
      simpa only [a,MulAut.conjNormal_apply,MulAut.one_apply] using
        congrArg Subtype.val (DFunLike.congr_fun he (⟨q,hq⟩ : Q))
    exact ((mul_inv_eq_iff_eq_mul).mp hh).symm
  have hfix := Cubic.fixed_free_of_model e a ha hn
  have hNC : Q ⊓ normalizer (C : Set G)=⊥ := by
    apply le_bot_iff.mp
    rintro x ⟨hxQ,hxN⟩
    have hxC : x*c*x⁻¹*c⁻¹∈C :=
      C.mul_mem ((mem_normalizer_iff.mp hxN c).mp (mem_zpowers c)) (C.inv_mem (mem_zpowers c))
    have hxQ' : x*c*x⁻¹*c⁻¹∈Q := by
      simpa only [mul_assoc] using Q.mul_mem hxQ
        ((inferInstance : Q.Normal).conj_mem _ (Q.inv_mem hxQ) c)
    have he : x*c*x⁻¹*c⁻¹=1 := (disjoint_iff_inf_le.mp hd) ⟨hxQ',hxC⟩
    have hh : x*c=c*x := mul_inv_eq_one.mp (by simpa only [mul_inv_rev,mul_assoc] using he)
    have hxfix : a ⟨x,hxQ⟩=⟨x,hxQ⟩ := by
      apply Subtype.ext
      change c*x*c⁻¹=x
      rw [←hh,mul_inv_cancel_right]
    exact congrArg Subtype.val (hfix ⟨x,hxQ⟩ hxfix)
  have hR : Nat.card (Q⊔C : Subgroup G)=48 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint Q C (by rw [Q.normalizer_eq_top];exact le_top) hd,hQ,hC]
  have hRi : (Q⊔C : Subgroup G).index=2 := by
    have hh := (Q⊔C : Subgroup G).card_mul_index
    rw [hR,hG] at hh
    omega
  let : (Q⊔C : Subgroup G).Normal := normal_of_index_eq_two hRi
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hCi : C.index=32 := by
    have hh := C.card_mul_index
    rw [hC,hG] at hh
    omega
  let P : Sylow 3 G := (IsPGroup.of_card (p:=3) (n:=1) (by simpa using hC)).toSylow
    (by rw [hCi];decide)
  have hsup : normalizer (C : Set G) ⊔ Q=⊤ := by
    have hh := P.normalizer_sup_eq_top' (show (P : Subgroup G)≤Q⊔C from le_sup_right)
    change normalizer (C : Set G) ⊔ (Q⊔C)=⊤ at hh
    rw [←sup_assoc,sup_eq_left.mpr (C.le_normalizer.trans le_sup_left)] at hh
    exact hh
  apply isComplement'_of_card_mul_and_disjoint
  · have hh := card_sup_eq_mul_of_normalizes_of_disjoint Q (normalizer (C:Set G))
      (by rw [Q.normalizer_eq_top];exact le_top) (disjoint_iff_inf_le.mpr (le_of_eq hNC))
    rw [sup_comm,hsup,Nat.card_congr Subgroup.topEquiv.toEquiv] at hh
    exact hh.symm
  · exact disjoint_iff_inf_le.mpr (le_of_eq hNC)
/-- The original quotient marking identifies the constructed complement. -/
theorem exists_symmetric_three_complement
    (Q : Subgroup G) [Q.Normal] (e : Q ≃* Model)
    (hG : Nat.card G=96) (hself : centralizer (Q : Set G) ≤ Q)
    (eQ : G ⧸ Q ≃* Equiv.Perm (Fin 3)) :
    ∃c : G, orderOf c=3 ∧ Q.IsComplement' (normalizer (zpowers c : Set G)) ∧
      Nonempty (normalizer (zpowers c : Set G) ≃* Equiv.Perm (Fin 3)) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G:=G) 3 (by rw [hG];decide)
  have hs := cubic_normalizer_complement Q e hG hself c hc
  exact ⟨c,hc,hs,⟨hs.symm.QuotientMulEquiv.symm.trans eQ⟩⟩
end C4SquareExtension
