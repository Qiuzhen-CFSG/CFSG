module
public import Theory.GroupTheory.MinusExtraspecialOddCentralizer.Model
public import Theory.SpecificGroups.SymmetricFiveCentralizerSquares
public import Theory.GroupTheory.MinusExtraspecialOddInvolutions
import all Theory.GroupTheory.MinusExtraspecialOddInvolutions
import all Theory.GroupTheory.MinusExtraspecialA5Fusion
public import Theory.SpecificGroups.MinusExtraspecial.CentralStructure

/-!
# Unique involution squares in minus extraspecial S₅ extensions

The intrinsic five-point action lifts a transposition to an involution in
a prescribed Sylow. Its core centralizer contains a square root of the
central involution. The commuting-automorphism calculation shows that all
order-four elements in its full local centralizer have that same square.
This construction retains local Sylow maximality and excludes membership
in every two-perfect subgroup. No splitting of the extension is assumed.
Source: Aschbacher–Smith 14.2.17(1), printed pp.986–987.
-/

open Subgroup
namespace MinusExtraspecial
open FixedFourCalculation.Outside
variable {H : Type*} [Group H]

private theorem transposition_square_data
    (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q) (j : H) (hj : j^2=1)
    (hs : (pointAction Q e j).IsSwap) :
    (∃ q : Q, Commute (q:H) j ∧ (q:H)^2 = (e.symm (quaternion z):H)) ∧
    ∀ x : H, Commute x j → x^4=1 →
      x^2=1 ∨ x^2=(e.symm (quaternion z):H) := by
  let a := modelAction Q e j
  have ha : a^2=1 := by rw [←map_pow,hj,map_one]
  obtain ⟨q,hq,hq2⟩ := FixedFourCalculation.OddCentralizer.exists_fixed_root a ha hs
  change e (MulAut.conjNormal j (e.symm q)) = q at hq
  refine ⟨?_,?_⟩
  · refine ⟨e.symm q,?_,?_⟩
    · have hh : MulAut.conjNormal j (e.symm q)=e.symm q := by
        apply e.injective
        simpa only [e.apply_symm_apply] using hq
      have h := congrArg Subtype.val hh
      change j*(e.symm q:H)*j⁻¹=(e.symm q:H) at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    · have he : (e.symm q)^2 = e.symm (quaternion z) := by
        apply e.injective
        simpa only [map_pow,MulEquiv.apply_symm_apply] using hq2
      exact congrArg Subtype.val he
  · intro x hx hx4
    have hf4 : (pointAction Q e x)^4=1 := by rw [←map_pow,hx4,map_one]
    have hf2 : (pointAction Q e x)^2=1 :=
      Equiv.Perm.square_eq_one_of_commute_swap_of_pow_four
        (pointAction Q e j) hs (pointAction Q e x)
        (hx.map (pointAction Q e)) hf4
    have hxQ : x^2 ∈ Q := by
      rw [←pointAction_kernel Q e hc,MonoidHom.mem_ker,map_pow]
      exact hf2
    let d : Q := ⟨x^2,hxQ⟩
    let b := modelAction Q e x
    have hd : (e d)^2=1 := by
      rw [←map_pow]
      have hh : d^2=1 := Subtype.ext (by change (x^2)^2=1; simpa only [←pow_mul] using hx4)
      rw [hh,map_one]
    have had : a (e d)=e d := by
      change e (MulAut.conjNormal j (e.symm (e d)))=e d
      rw [e.symm_apply_apply]
      congr 1
      apply Subtype.ext
      change j*x^2*j⁻¹=x^2
      exact mul_inv_eq_iff_eq_mul.mpr (hx.symm.pow_right 2).eq
    have hbd : b (e d)=e d := by
      change e (MulAut.conjNormal x (e.symm (e d)))=e d
      rw [e.symm_apply_apply]
      congr 1
      apply Subtype.ext
      change x*x^2*x⁻¹=x^2
      group
    have hb : b^2=MulAut.conj (e d) := by
      rw [←map_pow]
      apply MulEquiv.ext
      intro y
      change e (MulAut.conjNormal (x^2) (e.symm y))=e d*y*(e d)⁻¹
      rw [←e.apply_symm_apply y,←map_inv,←map_mul,←map_mul]
      congr 1
      simp only [e.symm_apply_apply]
      rfl
    rcases FixedFourCalculation.OddCentralizer.square_inner_central a b ha hs
      (hx.symm.map (modelAction Q e)) (e d) hd had hbd hb with hh | hh
    · left
      have he : d=1 := e.injective (hh.trans (map_one e).symm)
      exact congrArg Subtype.val he
    · right
      have he : d=e.symm (quaternion z) := e.injective (hh.trans (e.apply_symm_apply _).symm)
      exact congrArg Subtype.val he

/-- In a symmetric-five extension, a transposition lift can be chosen in
any prescribed Sylow with a local Sylow centralizer and unique involution
square. The root and square concern the literal embedded center of Q. -/
public theorem exists_outside_involution_with_unique_square [Finite H]
    (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q) (hq : Nat.card (H ⧸ Q)=120)
    (K : Subgroup H) (hK : IsPPerfect 2 K) (S : Sylow 2 H) :
    ∃ j : S, orderOf j = 2 ∧ (j:H) ∉ K ∧
      Nat.card ((centralizer ({(j:H)} : Set H)).subgroupOf Q) = 8 ∧
      Nat.card (centralizer ({(j:H)} : Set H)) ∣ 96 ∧
      (∃ P : Sylow 2 (centralizer ({(j:H)} : Set H)),
        (P : Subgroup (centralizer ({(j:H)} : Set H))) =
          (S : Subgroup H).subgroupOf (centralizer ({(j:H)} : Set H))) ∧
      (∃ q : Q, Commute (q:H) (j:H) ∧ (q:H)^2=(e.symm (quaternion z):H)) ∧
      (∀ x : H, Commute x (j:H) → x^4=1 →
        x^2=1 ∨ x^2=(e.symm (quaternion z):H)) := by
  classical
  let f := pointAction Q e
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply eq_top_of_card_eq
    rw [←index_ker,pointAction_kernel Q e hc]
    change Nat.card (H ⧸ Q)=Nat.card (Equiv.Perm (Fin 5))
    rw [hq,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  obtain ⟨t,ht⟩ := hf (Equiv.swap 0 1)
  have hswap : (f t).IsSwap := ht.symm ▸ Equiv.Perm.swap_isSwap_iff.mpr (by decide)
  obtain ⟨q,hq2⟩ := exists_involution_in_transposition_coset Q e hc t hswap
  let j0 : H := (q:H)*t
  have hj0map : f j0=Equiv.swap 0 1 := by
    rw [map_mul,show f (q:H)=1 from
      (show (q:H) ∈ f.ker from (pointAction_kernel Q e hc).symm ▸ q.property),one_mul,ht]
  have hj0 : orderOf j0=2 := orderOf_eq_prime hq2 (by
    intro hh
    have he := hj0map
    rw [hh,map_one] at he
    exact (by decide : (Equiv.swap (0:Fin 5) 1) ≠ 1) he.symm)
  obtain ⟨j,hconj,hlocal⟩ := S.exists_isConj_with_centralizer_sylow j0 1 (by simpa using hj0)
  obtain ⟨b,hb⟩ := isConj_iff.mp hconj
  have hj : orderOf (j:H)=2 := by
    rw [←hb]
    exact ((MulAut.conj b).orderOf_eq j0).trans hj0
  have hjs : (f (j:H)).IsSwap := by
    apply Equiv.Perm.card_support_eq_two.mp
    rw [←hb,map_mul,map_mul,map_inv,Equiv.Perm.card_support_conj,hj0map]
    exact Equiv.Perm.card_support_swap (by decide)
  have hsign : ∀ k:K, Equiv.Perm.sign (f (k:H))=1 := by
    let s := Equiv.Perm.sign.comp (f.comp K.subtype)
    have h2 : IsPGroup 2 ℤˣ := IsPGroup.of_card (n:=1) (by
      rw [Nat.card_eq_fintype_card,Fintype.card_units_int]; rfl)
    have hh := hK.hom_eq_one_of_isPGroup h2 s
    intro k
    exact DFunLike.congr_fun hh k
  have hj2 : (j:H)^2=1 := by simpa only [hj] using pow_orderOf_eq_one (j:H)
  refine ⟨j,(orderOf_coe j).symm.trans hj,?_,
    transposition_core_centralizer_card Q e (j:H) hj2 hjs,
    transposition_centralizer_card_dvd Q e hc (j:H) hj2 hjs,hlocal,
    transposition_square_data Q e hc (j:H) hj2 hjs⟩
  intro hjK
  have hh := hsign ⟨j,hjK⟩
  rw [hjs.sign_eq] at hh
  exact (by decide : (-1:ℤˣ) ≠ 1) hh
end MinusExtraspecial
