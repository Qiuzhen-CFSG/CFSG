module
public import Theory.GroupTheory.MinusExtraspecialOddInvolutions.Model
public import Theory.GroupTheory.MinusExtraspecialA5Fusion
import all Theory.GroupTheory.MinusExtraspecialA5Fusion
public import Theory.GroupTheory.PPerfectHom
public import Theory.SpecificGroups.SymmetricFiveInvolutions
public import Theory.GroupTheory.SylowCentralizerConjugacy
public import Theory.GroupTheory.SylowCentralizerRepresentative

/-!
# Outside involutions in symmetric-five extraspecial extensions

A self-centralizing normal minus extraspecial group Q has an intrinsic
five-point action with kernel Q. If |H/Q| = 120, this action is onto S₅.
Lift a transposition and correct its square using the model norm equation.
Its sign excludes membership in every two-perfect subgroup K of H.

Choose an extremal conjugate in the prescribed Sylow S. Its fixed core has
eight elements, and the induced centralizer image lies in the order-twelve
transposition centralizer, so |C_H(j)| divides 96. The same representative
has C_S(j) Sylow in C_H(j). The public result uses only group-theoretic data;
the internal import reuses the existing intrinsic action and kernel proof.

Source application: Aschbacher–Smith 14.2.17(1), printed pp.986–987.
No identification of the ambient group or full centralizer is asserted.
-/

open Subgroup
namespace MinusExtraspecial
open FixedFourCalculation.Outside
variable {H : Type*} [Group H]

/-- An element inducing a transposition can be corrected in its literal core
coset to an involution. No splitting of the whole extension is assumed. -/
private theorem exists_involution_in_transposition_coset
    (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q) (t : H)
    (ht : (pointAction Q e t).IsSwap) :
    ∃ q : Q, ((q:H) * t)^2 = 1 := by
  let a := modelAction Q e t
  have ht2 : t^2 ∈ Q := by
    rw [←pointAction_kernel Q e hc,MonoidHom.mem_ker,map_pow]
    exact ht.orderOf ▸ pow_orderOf_eq_one _
  let d : Q := ⟨t^2,ht2⟩
  have hd : a (e d) = e d := by
    change e (MulAut.conjNormal t (e.symm (e d))) = e d
    rw [e.symm_apply_apply]
    congr 1
    apply Subtype.ext
    change t * t^2 * t⁻¹ = t^2
    group
  have ha : a^2 = MulAut.conj (e d) := by
    rw [←map_pow]
    apply MulEquiv.ext
    intro x
    change e (MulAut.conjNormal (t^2) (e.symm x)) = e d * x * (e d)⁻¹
    rw [←e.apply_symm_apply x,←map_inv,←map_mul,←map_mul]
    congr 1
    simp only [e.symm_apply_apply]
    rfl
  obtain ⟨q,hq⟩ := FixedFourCalculation.OddInvolution.exists_norm_correction a ht (e d) hd ha
  let qQ := e.symm q
  have hqQ : qQ * MulAut.conjNormal t qQ * d = 1 := by
    apply e.injective
    change q * e (MulAut.conjNormal t (e.symm q)) * e d = 1 at hq
    simpa only [qQ,map_mul,map_one,MulEquiv.apply_symm_apply] using hq
  refine ⟨qQ,?_⟩
  have hh := congrArg Subtype.val hqQ
  change (qQ:H) * (t*(qQ:H)*t⁻¹) * t^2 = 1 at hh
  calc
    ((qQ:H)*t)^2 = (qQ:H) * (t*(qQ:H)*t⁻¹) * t^2 := by simp only [pow_two]; group
    _ = 1 := hh

/-- A transposition involution fixes exactly eight elements of the core. -/
private theorem transposition_core_centralizer_card
    (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (j : H) (hj : j^2=1) (hs : (pointAction Q e j).IsSwap) :
    Nat.card ((centralizer ({j} : Set H)).subgroupOf Q) = 8 := by
  let a := modelAction Q e j
  have ha : a^2=1 := by rw [←map_pow,hj,map_one]
  have hf := FixedFourCalculation.OddInvolution.fixed_card a ha hs
  have he : Nat.card ((centralizer ({j} : Set H)).subgroupOf Q) =
      Nat.card (a.toMonoidHom.eqLocus (MonoidHom.id Model)) := by
    apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
    intro x
    rw [mem_subgroupOf,mem_centralizer_singleton_iff]
    change ((x:H)*j=j*(x:H)) ↔ e (MulAut.conjNormal j (e.symm (e x))) = e x
    rw [e.symm_apply_apply,e.injective.eq_iff,Subtype.ext_iff]
    change ((x:H)*j=j*(x:H)) ↔ j*(x:H)*j⁻¹=(x:H)
    exact ⟨fun h => by rw [←h]; group,fun h => (mul_inv_eq_iff_eq_mul.mp h).symm⟩
  exact he.trans hf

/-- The full local centralizer of this involution has order dividing 96. -/
private theorem transposition_centralizer_card_dvd [Finite H]
    (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q)
    (j : H) (hj : j^2=1) (hs : (pointAction Q e j).IsSwap) :
    Nat.card (centralizer ({j} : Set H)) ∣ 96 := by
  let C := centralizer ({j} : Set H)
  let f := (pointAction Q e).comp C.subtype
  have hk : f.ker = Q.subgroupOf C := by
    change ((pointAction Q e).comp C.subtype).ker = _
    rw [←MonoidHom.comap_ker,pointAction_kernel Q e hc]
    rfl
  have hkc : Nat.card f.ker = 8 := by
    rw [hk,←card_map_of_injective C.subtype_injective,subgroupOf_map_subtype,inf_comm,
      ←subgroupOf_map_subtype C Q,card_map_of_injective Q.subtype_injective]
    exact transposition_core_centralizer_card Q e j hj hs
  have hr : f.range ≤ centralizer ({pointAction Q e j} : Set (Equiv.Perm (Fin 5))) := by
    rintro _ ⟨x,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change pointAction Q e (x:H) * pointAction Q e j = pointAction Q e j * pointAction Q e (x:H)
    simpa only [map_mul] using congrArg (pointAction Q e)
      (mem_centralizer_singleton_iff.mp x.property)
  have hd := card_dvd_of_le hr
  have h12 : Nat.card (centralizer ({pointAction Q e j} : Set (Equiv.Perm (Fin 5)))) = 12 := by
    rw [Equiv.Perm.nat_card_centralizer,Equiv.Perm.isSwap_iff_cycleType.mp hs]
    norm_num
  rw [h12] at hd
  have hh := f.ker.card_mul_index
  rw [hkc,index_ker] at hh
  rw [←hh]
  exact Nat.mul_dvd_mul_left 8 hd
/-- A symmetric-five extension contains an involution outside every
 two-perfect subgroup, in any prescribed Sylow two-subgroup. Its literal
 core centralizer has order eight and its local centralizer order divides 96. -/
public theorem exists_involution_outside_twoPerfect [Finite H]
    (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q) (hq : Nat.card (H ⧸ Q) = 120)
    (K : Subgroup H) (hK : IsPPerfect 2 K) (S : Sylow 2 H) :
    ∃ j : S, orderOf j = 2 ∧ (j:H) ∉ K ∧
      Nat.card ((centralizer ({(j:H)} : Set H)).subgroupOf Q) = 8 ∧
      Nat.card (centralizer ({(j:H)} : Set H)) ∣ 96 ∧
      ∃ P : Sylow 2 (centralizer ({(j:H)} : Set H)),
        (P : Subgroup (centralizer ({(j:H)} : Set H))) =
          (S : Subgroup H).subgroupOf (centralizer ({(j:H)} : Set H)) := by
  classical
  let f := pointAction Q e
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply eq_top_of_card_eq
    rw [←index_ker,pointAction_kernel Q e hc]
    change Nat.card (H ⧸ Q) = Nat.card (Equiv.Perm (Fin 5))
    rw [hq,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  obtain ⟨t,ht⟩ := hf (Equiv.swap 0 1)
  have hswap : (f t).IsSwap := ht.symm ▸ Equiv.Perm.swap_isSwap_iff.mpr (by decide)
  obtain ⟨q,hq2⟩ := exists_involution_in_transposition_coset Q e hc t hswap
  let j0 : H := (q:H)*t
  have hj0map : f j0 = Equiv.swap 0 1 := by
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
    transposition_centralizer_card_dvd Q e hc (j:H) hj2 hjs,hlocal⟩
  intro hjK
  have hh := hsign ⟨j,hjK⟩
  rw [hjs.sign_eq] at hh
  exact (by decide : (-1:ℤˣ) ≠ 1) hh
end MinusExtraspecial
