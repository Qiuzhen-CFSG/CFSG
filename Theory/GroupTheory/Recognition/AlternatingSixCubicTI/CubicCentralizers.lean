module
public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.Card
public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.CyclicAction
public import Theory.GroupTheory.TINormalizerControl
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Cubic centralizers and normalizers in the TI configuration

The TI intersection property places the centralizer of a nonidentity element
of P in N(P). Its faithful cyclic-four quotient acts freely on P minus the
identity, so that centralizer is precisely P. Sylow conjugacy yields the
ambient cubic centralizer order nine. A lift of the square of a quotient
generator inverts P, and the order-two automorphism group of a cubic line
then gives its full normalizer order eighteen.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2, printed p.249.
All maps are the actual normalizer conjugation and quotient maps.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
variable {G:Type*} [Group G] [Finite G]
variable (P:Sylow 3 G) [IsElementaryAbelian 3 P]
variable (hP:Nat.card (P:Subgroup G)=9)
variable (hTI:∀g:G,(P:Subgroup G)⊓(P:Subgroup G).map (MulAut.conj g).toMonoidHom=⊥ ∨
  (P:Subgroup G).map (MulAut.conj g).toMonoidHom=P)
variable (hC:centralizer ((P:Subgroup G):Set G)≤P)
variable (eN: (normalizer ((P:Subgroup G):Set G) ⧸ (P:Subgroup G).subgroupOf (normalizer ((P:Subgroup G):Set G)))≃*Multiplicative (ZMod 4))

include hC in
omit [Finite G] in
private theorem action_ker : (P:Subgroup G).normalizerMonoidHom.ker =
    (P:Subgroup G).subgroupOf (normalizer ((P:Subgroup G):Set G)) := by
  rw [normalizerMonoidHom_ker]
  apply le_antisymm
  · intro x hx; exact hC hx
  · intro x hx y hy
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨y,hy⟩:P) ⟨x,hx⟩)

private noncomputable def actionRangeEquiv : (P:Subgroup G).normalizerMonoidHom.range ≃*Multiplicative (ZMod 4) :=
  (QuotientGroup.quotientKerEquivRange _).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (action_ker P hC)).trans eN)

include hP hTI hC eN in
theorem centralizer_eq_of_nonidentity (x:G) (hx:x∈P) (hx1:x≠1) :
    centralizer ({x}:Set G)=(P:Subgroup G) := by
  apply le_antisymm
  · intro g hg
    have hgn:g∈normalizer ((P:Subgroup G):Set G) :=
      inf_elementCentralizer_le_normalizer_of_trivial_intersections
        (M:=⊤) (fun a _=>hTI a) hx hx1 ⟨mem_top g,hg⟩
    by_contra hgp
    let α:normalizer ((P:Subgroup G):Set G):=⟨g,hgn⟩
    let a:(P:Subgroup G).normalizerMonoidHom.range:=
      ⟨(P:Subgroup G).normalizerMonoidHom α,α,rfl⟩
    let e:=actionRangeEquiv P hC eN
    let ρ:Multiplicative (ZMod 4)→*MulAut P :=
      (P:Subgroup G).normalizerMonoidHom.range.subtype.comp e.symm.toMonoidHom
    have hρ:Function.Injective ρ := Subtype.val_injective.comp e.symm.injective
    have ha:e a≠1 := by
      intro hh
      have ha1:a=1 := e.injective (hh.trans e.map_one.symm)
      have hker:α∈(P:Subgroup G).normalizerMonoidHom.ker := congrArg Subtype.val ha1
      rw [action_ker P hC] at hker
      exact hgp hker
    have hfix:ρ (e a) (⟨x,hx⟩:P)=⟨x,hx⟩ := by
      change ((e.symm (e a): (P:Subgroup G).normalizerMonoidHom.range):MulAut P) _=_
      rw [e.symm_apply_apply]
      apply Subtype.ext
      change g*x*g⁻¹=x
      have he:=mem_centralizer_singleton_iff.mp hg
      calc g*x*g⁻¹ = x*g*g⁻¹ := by rw [he]
           _ = x := mul_inv_cancel_right _ _
    have hh:=cyclic_four_fixed_eq_one hP ρ hρ (e a) ha (⟨x,hx⟩:P) hfix
    exact hx1 (congrArg Subtype.val hh)
  · intro g hg
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨g,hg⟩:P) ⟨x,hx⟩)

include hP hTI hC eN in
theorem cubic_centralizer_card (x:G) (hx:orderOf x=3) :
    Nat.card (centralizer ({x}:Set G))=9 := by
  let : Fact (Nat.Prime 3):=⟨by decide⟩
  have hp:IsPGroup 3 (zpowers x):=IsPGroup.of_card (n:=1) (by simpa using hx)
  obtain ⟨Q,hQ⟩:=hp.exists_le_sylow
  obtain ⟨g,hg⟩:=MulAction.exists_smul_eq G Q P
  have hxP:(MulAut.conj g) x∈P := by
    rw [←hg]
    exact mem_map_of_mem _ (hQ (mem_zpowers x))
  have hx1:(MulAut.conj g) x≠1 := by
    intro he
    have hx':x=1:=(MulAut.conj g).injective (he.trans (map_one _).symm)
    simp only [hx',orderOf_one] at hx
    omega
  rw [Nat.card_congr (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv
    (MulAut.conj g) x).toEquiv,centralizer_eq_of_nonidentity P hP hTI hC eN _ hxP hx1,hP]

include hP hC eN in
theorem exists_normalizer_inverter : ∃g∈normalizer ((P:Subgroup G):Set G),
    ∀x∈P,g*x*g⁻¹=x⁻¹ := by
  let e:=actionRangeEquiv P hC eN
  let a:=e.symm (Multiplicative.ofAdd (1:ZMod 4))
  obtain ⟨g,hg⟩:=a.property
  have h4:((P:Subgroup G).normalizerMonoidHom g)^4=1 := by
    have hh:a^4=1 := by
      dsimp [a]
      rw [←map_pow,show (Multiplicative.ofAdd (1:ZMod 4))^4=1 by decide,map_one]
    have hh':(a:MulAut P)^4=1:=congrArg Subtype.val hh
    rwa [←hg] at hh'
  have h2:((P:Subgroup G).normalizerMonoidHom g)^2≠1 := by
    intro hh
    have he:a^2=1:=Subtype.ext (by change (a:MulAut P)^2=1; rwa [←hg])
    have he':(Multiplicative.ofAdd (1:ZMod 4))^2=1 := by
      have hh:=congrArg e he
      simpa only [a,map_pow,e.apply_symm_apply,map_one] using hh
    exact (by decide : (Multiplicative.ofAdd (1:ZMod 4))^2≠1) he'
  refine ⟨(g:G)^2,(normalizer ((P:Subgroup G):Set G)).pow_mem g.property 2,?_⟩
  intro x hx
  have hh:=fourth_power_square_inverts hP ((P:Subgroup G).normalizerMonoidHom g) h4 h2 (⟨x,hx⟩:P)
  have he:=congrArg Subtype.val hh
  change (g:G)*((g:G)*x*(g:G)⁻¹)*(g:G)⁻¹=x⁻¹ at he
  simpa only [pow_two,mul_inv_rev,mul_assoc] using he

include hP hTI hC eN in
theorem cubic_normalizer_card (U:Subgroup G) (hU:Nat.card U=3) (hUP:U≤P) :
    Nat.card (normalizer (U:Set G))=18 := by
  let : Fact (Nat.Prime 3):=⟨by decide⟩
  let : IsCyclic U:=isCyclic_of_prime_card hU
  obtain ⟨x,hx⟩:=exists_prime_orderOf_dvd_card' (G:=U) 3 (by rw [hU])
  have hxG:orderOf (x:G)=3 := (orderOf_injective U.subtype U.subtype_injective x).trans hx
  have hx1:(x:G)≠1 := by intro he; rw [he,orderOf_one] at hxG; omega
  have hgen:zpowers (x:G)=U := eq_of_le_of_card_ge (zpowers_le.mpr x.property) (by rw [Nat.card_zpowers,hxG,hU])
  have hCU:centralizer (U:Set G)=(P:Subgroup G) := by
    apply le_antisymm
    · exact (centralizer_le (Set.singleton_subset_iff.mpr x.property)).trans
        (centralizer_eq_of_nonidentity P hP hTI hC eN x (hUP x.property) hx1).le
    · intro g hg u hu
      exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨u,hUP hu⟩:P) ⟨g,hg⟩)
  obtain ⟨g,hgn,hinv⟩:=exists_normalizer_inverter P hP hC eN
  have hgU:g∈normalizer (U:Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨u,hu,rfl⟩
      change g*u*g⁻¹∈U
      rw [hinv u (hUP hu)]
      exact U.inv_mem hu
    · rw [card_map_of_injective (MulAut.conj g).injective]
  have hgC:g∉centralizer (U:Set G) := by
    intro he
    have hxinv:(x:G)=(x:G)⁻¹ := by
      have hh:=he x x.property
      calc (x:G)=g*x*g⁻¹ := (by rw [←hh]; group)
           _=(x:G)⁻¹:=hinv x (hUP x.property)
    have hs:(x:G)^2=1 := by rw [pow_two]; nth_rw 1 [hxinv]; exact inv_mul_cancel _
    have hd:=orderOf_dvd_of_pow_eq_one hs
    rw [hxG] at hd
    norm_num at hd
  have hd:(centralizer (U:Set G)).relIndex (normalizer (U:Set G))∣2 := by
    have hh:=card_dvd_of_injective _ (QuotientGroup.kerLift_injective U.normalizerMonoidHom)
    rw [normalizerMonoidHom_ker,←index,←relIndex,IsCyclic.card_mulAut,hU] at hh
    simpa only [show Nat.totient 3=2 by decide] using hh
  have hi:(centralizer (U:Set G)).relIndex (normalizer (U:Set G))=2 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with he|he
    · exact (hgC ((relIndex_eq_one.mp he) hgU)).elim
    · exact he
  have hh:=((centralizer (U:Set G)).subgroupOf (normalizer (U:Set G))).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (U:Set G))).toEquiv] at hh
  change (centralizer (U:Set G)).relIndex (normalizer (U:Set G))*Nat.card (centralizer (U:Set G))=_ at hh
  rw [hi,hCU,hP] at hh
  omega
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
