module
public import Theory.GroupTheory.WreathedThirtyTwoVertex.SourceCore

/-!
# Central squares outside the quaternion–cyclic core

ABG identifies the unique nonabelian centric subgroup with odd automorphisms in
the wreath product. Its index two makes every conjugate equal to itself. The
32-element coordinates show that an element with central square and fourth
power one lies in this core. The source theorem transports this fact through
a Sylow subgroup containing the given element, retaining the original core.

Source: Aschbacher–Smith F.1.12(I)(8), the nonabelian order-96 vertex.
-/

@[expose] public section
open Subgroup
namespace WreathedVertex
local instance : Fintype W:=Fintype.ofEquiv ((C2→C4)×C2) (RegularWreathProduct.equivProd C4 C2).symm
local instance : DecidableEq W:=(RegularWreathProduct.equivProd C4 C2).injective.decidableEq

theorem nonabelian_centric_eq_core (X:Subgroup W)
    (hc:centralizer (X:Set W)≤X) (hna:¬IsMulCommutative X)
    (hAut:¬IsPGroup 2 (MulAut X)) : X=coreEmbedding.range := by
  obtain ⟨P⟩:=ABG.Wreathed.nonempty_presentation ABG.RegularWreathHeightTwo.isWreathedOfHeight
  obtain ⟨e⟩:=nonabelian_centric_model X hc hna hAut
  have hv:Nat.card P.V=16 := by
    rcases ABG.Wreathed.exceptional_centric_classification P X hc hAut with h|⟨g,hg⟩
    · exact (hna (h ▸ P.base_structure.2.2.1)).elim
    · rw [←card_map_of_injective (f:=(MulAut.conj g).toMonoidHom) (K:=P.V) (MulAut.conj g).injective,hg,
        Nat.card_congr e.toEquiv,QuaternionCyclic.card_model]
  have hn:P.V.Normal := normal_of_index_eq_two (by
    have hh:=P.V.card_mul_index
    rw [hv,Theory.GroupTheory.wreathedThirtyTwo_card] at hh
    omega)
  have id (Y:Subgroup W)(hc:centralizer (Y:Set W)≤Y)(hna:¬IsMulCommutative Y)
      (ha:¬IsPGroup 2 (MulAut Y)) : Y=P.V := by
    rcases ABG.Wreathed.exceptional_centric_classification P Y hc ha with h|⟨g,hg⟩
    · exact (hna (h ▸ P.base_structure.2.2.1)).elim
    · exact hg.symm.trans (Normal.map_conj_eq P.V g)
  have hx:=id X hc hna hAut
  let eM:QuaternionCyclic.Model≃*coreEmbedding.range:=MonoidHom.ofInjective coreEmbedding_injective
  have hnM:¬IsMulCommutative coreEmbedding.range := by
    intro hh
    apply model_not_commutative
    exact IsMulCommutative.of_comm (fun a b=>eM.injective (by
      rw [map_mul,map_mul];exact hh.is_comm.comm _ _))
  have haM:¬IsPGroup 2 (MulAut coreEmbedding.range) := by
    intro hh
    exact model_aut_not_two (hh.of_equiv (MulAut.congr eM).symm)
  exact hx.trans (id _ coreEmbedding_centralizer hnM haM).symm

theorem fourth_one_central_square_mem (x:W) (hx:x^4=1) (hs:x^2∈center W) :
    x∈coreEmbedding.range := by
  have h:∀x:W,x^4=1→(∀y:W,y*x^2=x^2*y)→∃a:QuaternionCyclic.Model,coreEmbedding a=x := by
    decide +kernel
  exact h x hx (mem_center_iff.mp hs)
variable {G:Type*} [Group G] [Finite G]

theorem source_fourth_one_central_square_mem (Q:Subgroup G) [Q.Normal]
    (hQ:IsPGroup 2 Q) (hc:centralizer (Q:Set G)≤Q) (hna:¬IsMulCommutative Q)
    (h3:3∣Nat.card G) (S:Sylow 2 G) (eS:S≃*W)
    (x:G) (hx:x^4=1) (hs:x^2∈center G) : x∈Q := by
  have hp:IsPGroup 2 (zpowers x):=IsPGroup.of_card_dvd_pow (n:=2)
    (by rw [Nat.card_zpowers];exact orderOf_dvd_of_pow_eq_one hx)
  obtain ⟨T,hT⟩:=hp.exists_le_sylow
  let eT:T≃*W:=(T.equiv S).trans eS
  have hQT:Q≤T:=hQ.le_sylow_of_normal T
  let K:Subgroup T:=Q.subgroupOf T
  let X:Subgroup W:=K.map eT.toMonoidHom
  let eK:K≃*Q:=subgroupOfEquivOfLe hQT
  let eX:K≃*X:=K.equivMapOfInjective eT.toMonoidHom eT.injective
  let e:Q≃*X:=eK.symm.trans eX
  have hcent:centralizer (X:Set W)≤X := by
    intro w hw
    have ht:(eT.symm w:G)∈Q := by
      apply hc
      intro a ha
      let aT:T:=⟨a,hQT ha⟩
      have haX:eT aT∈X:=⟨aT,ha,rfl⟩
      have hh:=hw _ haX
      have he:aT*eT.symm w=eT.symm w*aT := by
        apply eT.injective
        simpa only [map_mul,eT.apply_symm_apply] using hh
      exact congrArg (fun a:T=>(a:G)) he
    exact ⟨eT.symm w,ht,eT.apply_symm_apply w⟩
  have hn:¬IsMulCommutative X := by
    intro hh
    apply hna
    exact IsMulCommutative.of_comm (fun a b=>e.injective (by
      rw [map_mul,map_mul];exact hh.is_comm.comm _ _))
  have ha:¬IsPGroup 2 (MulAut X) := by
    intro hh
    exact core_aut_not_two Q hQ hc h3 (hh.of_equiv (MulAut.congr e).symm)
  have hX:X=coreEmbedding.range:=nonabelian_centric_eq_core X hcent hn ha
  let xT:T:=⟨x,hT (mem_zpowers x)⟩
  have hxT:xT^4=1:=Subtype.ext hx
  have hsT:xT^2∈center T:=mem_center_iff.mpr (fun y=>Subtype.ext (mem_center_iff.mp hs y))
  have hm:eT xT∈coreEmbedding.range:=fourth_one_central_square_mem _
    (by rw [←map_pow,hxT,map_one]) (by
      rw [←map_pow]
      exact (centerCongr eT ⟨_,hsT⟩).property)
  rw [←hX] at hm
  obtain ⟨a,ha,he⟩:=hm
  have he':a=xT:=eT.injective he
  change xT∈K
  rw [←he']
  exact ha

end WreathedVertex
