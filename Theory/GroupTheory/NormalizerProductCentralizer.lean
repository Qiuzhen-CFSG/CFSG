module

public import Theory.GroupTheory.OrderThreeNormalizer
public import Theory.GroupTheory.CyclicThreeNormalizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SubgroupConjugateIncidence
import Mathlib.Tactic.Group
/-!
# Centralizers inside a normalizer supplement

If H=Q N_H(X), Q∩X=1, and Q is H-invariant, then an element of H
centralizing U≤X has a normalizer component centralizing U.  Therefore
C_Q(U)≤N_H(X) implies C_H(U)≤N_H(X).  The proof compares the two
X-elements before and after conjugation by the Q-component.

Source: Aschbacher, *Sporadic Groups* (1994),45.7(1),printed p.245.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

theorem centralizer_le_of_normalizer_product (H Q X U : Subgroup G)
    (hQ : H ≤ normalizer (Q : Set G)) (hXH : X ≤ H)
    (hUX : U ≤ X) (hdis : Q ⊓ X = ⊥)
    (hsplit : H = Q ⊔ (H ⊓ normalizer (X : Set G)))
    (hfix : Q ⊓ centralizer (U : Set G) ≤ normalizer (X : Set G)) :
    H ⊓ centralizer (U : Set G) ≤ normalizer (X : Set G) := by
  intro h hh
  have hp : h ∈ (Q:Set G) * (H ⊓ normalizer (X:Set G) : Subgroup G) := by
    rw [←coe_mul_of_right_le_normalizer_left Q _ (inf_le_left.trans hQ),←hsplit]
    exact hh.1
  obtain ⟨q,hq,n,hn,rfl⟩ := hp
  have hnC : n ∈ centralizer (U : Set G) := by
    intro u hu
    have hx : n*u*n⁻¹ ∈ X := (hn.2 u).mp (hUX hu)
    have he : q*(n*u*n⁻¹)*q⁻¹=u := by
      have hf := mul_inv_eq_iff_eq_mul.mpr (hh.2 u hu).symm
      calc
        q*(n*u*n⁻¹)*q⁻¹=(q*n)*u*(q*n)⁻¹ := by group
        _ = u := hf
    have hδQ : (n*u*n⁻¹)*u⁻¹ ∈ Q := by
      have heq : (n*u*n⁻¹)*u⁻¹=q⁻¹*(u*q*u⁻¹) := by
        calc
          (n*u*n⁻¹)*u⁻¹=(q⁻¹*(q*(n*u*n⁻¹)*q⁻¹)*q)*u⁻¹ := by group
          _ = q⁻¹*(u*q*u⁻¹) := by rw [he]; group
      rw [heq]
      exact Q.mul_mem (Q.inv_mem hq) ((hQ (hXH (hUX hu)) q).mp hq)
    have hδX : (n*u*n⁻¹)*u⁻¹ ∈ X := X.mul_mem hx (X.inv_mem (hUX hu))
    have heq : n*u*n⁻¹=u := mul_inv_eq_one.mp (show (n*u*n⁻¹)*u⁻¹=1 from
      mem_bot.mp (hdis ▸ (show (n*u*n⁻¹)*u⁻¹∈Q⊓X from ⟨hδQ,hδX⟩)))
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  have hqC : q∈centralizer (U : Set G) := by
    simpa only [mul_inv_cancel_right] using (centralizer (U : Set G)).mul_mem hh.2
      ((centralizer (U : Set G)).inv_mem hnC)
  exact (normalizer (X : Set G)).mul_mem (hfix ⟨hq,hqC⟩) hn.2
theorem normalizer_le_of_cubic_inverter_centralizer [Finite G]
    (H N U : Subgroup G) (hU : Nat.card U=3) (s : G) (hsH : s∈H) (hsN : s∈N)
    (hi : ∀u∈U,s*u*s⁻¹=u⁻¹) (hC : H⊓centralizer (U:Set G)≤N) :
    H⊓normalizer (U:Set G)≤N := by
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G:=U) 3 (hU ▸ dvd_rfl)
  have huG : orderOf (u:G)=3 := (orderOf_injective U.subtype U.subtype_injective u).trans hu
  have he : zpowers (u:G)=U := eq_of_le_of_card_ge (zpowers_le.mpr u.property)
    (by rw [Nat.card_zpowers,huG,hU])
  have hs : s⁻¹*(u:G)*s=(u:G)⁻¹ := by
    have hh : s*(u:G)⁻¹*s⁻¹=(u:G) := by
      simpa only [mul_inv_rev,inv_inv,←mul_assoc] using congrArg Inv.inv (hi u u.property)
    calc
      s⁻¹*(u:G)*s=s⁻¹*(s*(u:G)⁻¹*s⁻¹)*s := congrArg (fun x:G=>s⁻¹*x*s) hh.symm
      _ = (u:G)⁻¹ := by group
  have hcentral : centralizer (U:Set G)=centralizer ({(u:G)}:Set G) := by
    calc
      centralizer (U:Set G) = centralizer (zpowers (u:G):Set G) := congrArg (fun A:Subgroup G=>centralizer (A:Set G)) he.symm
      _ = centralizer ({(u:G)}:Set G) := by rw [show zpowers (u:G)=closure ({(u:G)}:Set G) from zpowers_eq_closure _,centralizer_closure]
  have hnorm : normalizer (U:Set G)=zpowers s⊔centralizer (U:Set G) := by
    calc
      normalizer (U:Set G)=normalizer (zpowers (u:G):Set G) := congrArg (fun A:Subgroup G=>normalizer (A:Set G)) he.symm
      _ = zpowers s⊔centralizer ({(u:G)}:Set G) := normalizer_zpowers_order_three (u:G) s huG hs
      _ = zpowers s⊔centralizer (U:Set G) := by rw [hcentral]
  have hsNU : s∈normalizer (U:Set G) := hnorm ▸ mem_sup_left (mem_zpowers s)
  have hnc : zpowers s≤normalizer (centralizer (U:Set G):Set G) :=
    (zpowers_le.mpr hsNU).trans (normalizer_le_normalizer_centralizer U)
  intro g hg
  have hp : g∈(zpowers s:Set G)*(centralizer (U:Set G):Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hnc,←hnorm]
    exact hg.2
  obtain ⟨a,ha,c,hc,rfl⟩ := hp
  have haH : a∈H := (zpowers_le.mpr hsH) ha
  have hcH : c∈H := by simpa using H.mul_mem (H.inv_mem haH) hg.1
  exact N.mul_mem ((zpowers_le.mpr hsN) ha) (hC ⟨hcH,hc⟩)
theorem normalizes_fixed_of_square_centralizes [Finite G] (N X : Subgroup G)
    (hNX : N≤normalizer (X:Set G))
    (hsq : ∀n∈N,n^2∈centralizer (X:Set G)) (t:G) (ht:t∈N) :
    N≤normalizer ((X⊓centralizer ({t}:Set G):Subgroup G):Set G) := by
  let f : N →* MulAut X := X.normalizerMonoidHom.comp (inclusion hNX)
  have hf2 (n:N) : (f n)^2=1 := by
    rw [←map_pow]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (n:G)^2*(x:G)*((n:G)^2)⁻¹=(x:G)
    rw [←hsq n n.property x x.property,mul_inv_cancel_right]
  have hcomm (g:N) : f g * f ⟨t,ht⟩ = f ⟨t,ht⟩ * f g := by
    have hgi : (f g)⁻¹=f g := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hf2 g)
    have hti : (f ⟨t,ht⟩)⁻¹=f ⟨t,ht⟩ := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hf2 ⟨t,ht⟩)
    have hprod : (f g*f ⟨t,ht⟩)^2=1 := by
      simpa only [map_mul] using hf2 (g*⟨t,ht⟩)
    have hi : (f g*f ⟨t,ht⟩)⁻¹=f g*f ⟨t,ht⟩ := inv_eq_of_mul_eq_one_left
      (by simpa only [pow_two] using hprod)
    rw [mul_inv_rev,hgi,hti] at hi
    exact hi.symm
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨(hNX hg x).mp hx.1,?_⟩
    let x' : X := ⟨x,hx.1⟩
    have htx : f ⟨t,ht⟩ x'=x' := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx.2).symm
    have hh := congrArg (fun a:MulAut X=>a x') (hcomm ⟨g,hg⟩)
    change f ⟨g,hg⟩ (f ⟨t,ht⟩ x') = f ⟨t,ht⟩ (f ⟨g,hg⟩ x') at hh
    rw [htx] at hh
    apply mem_centralizer_singleton_iff.mpr
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh.symm)).symm
  · rw [card_map_of_injective (MulAut.conj g).injective]
end Subgroup
