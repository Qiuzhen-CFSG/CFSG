module
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Commutator.Basic
/-! # Derived subgroups of crossing Sylow factors
A square-moving pair of planes makes the two Sylow factors centralize each
other. If one factor maps onto a marked quotient, the derived subgroup of
its centralizer is killed by that quotient. This is the core-placement step
in Aschbacher--Smith 2.5.7, printed p.556, with the literal conjugation maps.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G Q:Type*} [Group G] [Group Q]
theorem crossing_pair_centralizes_of_square_generation
    (A V:Subgroup G) (x:G) (hgen:A=V⊔V.conjBy (x^2))
    (hx2:x^2∈normalizer (A:Set G))
    (hplus:V.conjBy x≤centralizer (V:Set G))
    (hminus:V.conjBy x⁻¹≤centralizer (V:Set G)) :
    A.conjBy x⁻¹≤centralizer (A:Set G) := by
  have hA:A.conjBy x⁻¹=V.conjBy x⁻¹⊔V.conjBy x:=by
    conv_lhs => rw [hgen]
    change (V⊔V.conjBy (x^2)).map (MulAut.conj x⁻¹).toMonoidHom=_
    rw [Subgroup.map_sup]
    change V.conjBy x⁻¹⊔(V.conjBy (x^2)).conjBy x⁻¹=_
    rw [conjBy_conjBy,show x⁻¹*x^2=x by group]
  have hc:A.conjBy x⁻¹≤centralizer (V:Set G):=by
    rw [hA]
    exact sup_le hminus hplus
  have he:(A.conjBy x⁻¹).conjBy (x^2)=A.conjBy x⁻¹:=by
    rw [conjBy_conjBy,show x^2*x⁻¹=x by group]
    have hh:=congrArg (fun B:Subgroup G=>B.conjBy x⁻¹)
      (mem_normalizer_iff_map_conj_eq.mp hx2)
    change (A.conjBy (x^2)).conjBy x⁻¹=A.conjBy x⁻¹ at hh
    rw [conjBy_conjBy,show x⁻¹*x^2=x by group] at hh
    exact hh
  have hc':A.conjBy x⁻¹≤centralizer (V.conjBy (x^2):Set G):=by
    rw [←he]
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    exact (MulAut.conj (x^2)).map_mul b a ▸
      (MulAut.conj (x^2)).map_mul a b ▸ congrArg (MulAut.conj (x^2)) (hc ha b hb)
  apply le_centralizer_iff.mpr
  conv_lhs => rw [hgen]
  exact sup_le (le_centralizer_iff.mp hc) (le_centralizer_iff.mp hc')

theorem commutator_le_marked_kernel_of_centralizes
    (R A B:Subgroup G) (f:R→*Q)
    (hf:Function.Surjective (f.comp (A.subgroupOf R).subtype))
    (hBR:B≤R) (hc:B≤centralizer (A:Set G)) :
    ⁅B,B⁆≤f.ker.map R.subtype := by
  have hcentral (b:G) (hb:b∈B):f ⟨b,hBR hb⟩∈center Q:=by
    apply mem_center_iff.mpr
    intro q
    obtain ⟨a,rfl⟩:=hf q
    have he:(a.val:R)*⟨b,hBR hb⟩=⟨b,hBR hb⟩*(a.val:R):=
      Subtype.ext (hc hb (a.val:G) a.property)
    simpa only [MonoidHom.comp_apply,Subgroup.subtype_apply,map_mul] using congrArg f he
  apply commutator_le.mpr
  intro b hb c hc'
  refine ⟨⁅(⟨b,hBR hb⟩:R),⟨c,hBR hc'⟩⁆,?_,rfl⟩
  change f ⁅(⟨b,hBR hb⟩:R),⟨c,hBR hc'⟩⁆=1
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  exact (mem_center_iff.mp (hcentral c hc') (f ⟨b,hBR hb⟩))
end Subgroup

namespace Subgroup
variable {G Q:Type*} [Group G] [Group Q]
theorem normalizes_conjugate_commutator (S A:Subgroup G) (x:G)
    (hSA:S≤normalizer (A:Set G)) (hx:x∈normalizer (S:Set G)) :
    S≤normalizer (⁅A,A⁆.conjBy x:Set G) := by
  have hn:S≤normalizer ((⁅A,A⁆:Subgroup G):Set G):=by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hSA hs)]
  have hm:=map_mono (f:=(MulAut.conj x).toMonoidHom) hn
  have hs:S.map (MulAut.conj x).toMonoidHom=S:=mem_normalizer_iff_map_conj_eq.mp hx
  rw [map_equiv_normalizer_eq,hs] at hm
  exact hm

theorem marked_commutator_ne_bot
    (R A:Subgroup G) (f:R→*Q)
    (hf:Function.Surjective (f.comp (A.subgroupOf R).subtype))
    (hQ:_root_.commutator Q≠⊥) : ⁅A,A⁆≠⊥ := by
  intro he
  apply hQ
  apply bot_unique
  apply commutator_le.mpr
  intro a _ b _
  obtain ⟨u,rfl⟩:=hf a
  obtain ⟨v,rfl⟩:=hf b
  rw [mem_bot,commutatorElement_eq_one_iff_mul_comm]
  have hc:=commutator_eq_bot_iff_le_centralizer.mp he
  have hh:(u.val:R)*(v.val:R)=(v.val:R)*(u.val:R):=
    Subtype.ext (hc v.property (u.val:G) u.property)
  simpa only [MonoidHom.comp_apply,Subgroup.subtype_apply,map_mul] using congrArg f hh
end Subgroup
