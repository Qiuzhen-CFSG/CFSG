module
public import ABG.ChapterII.Section1.WreathedLemmaThree
public import Theory.GroupTheory.WreathedThirtyTwo
public import Theory.GroupTheory.SpecificGroups.QuaternionCyclicModel

/-!
# The nonabelian centric core in C₄ wreath C₂

Embed the explicit quaternion–cyclic central product in the actual regular
wreath product. Its elementary order-32 coordinates verify the embedding and
centricity. ABG's exceptional centric subgroup theorem then compares every
nonabelian centric subgroup with a non-two-group automorphism group to this
same core. No classification of groups of order 96 is used.

Sources: ABG II.1 Lemma 3; the G₂(2)′ vertex in Aschbacher–Smith F.1.12(I)(8).
-/

@[expose] public section
open Subgroup
namespace WreathedVertex
abbrev C2:=Multiplicative (ZMod 2)
abbrev C4:=Multiplicative (ZMod 4)
abbrev W:=Theory.GroupTheory.WreathedThirtyTwo
local instance : Fintype W:=Fintype.ofEquiv ((C2→C4)×C2) (RegularWreathProduct.equivProd C4 C2).symm
local instance : DecidableEq W:=(RegularWreathProduct.equivProd C4 C2).injective.decidableEq

def qx:W:=⟨fun q=>if q=1 then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 3,1⟩
def qy:W:=⟨fun q=>if q=1 then Multiplicative.ofAdd 2 else 1,Multiplicative.ofAdd 1⟩
def qr:W:=⟨fun _=>Multiplicative.ofAdd 1,1⟩
def quaternionWord : QuaternionGroup 2→W
  | .a i=>qx^i.val
  | .xa i=>qy*qx^i.val
def coreEmbedding:QuaternionCyclic.Model→*W where
  toFun a:=quaternionWord a.quaternion*(if a.odd then qr else 1)
  map_one':=by decide +kernel
  map_mul':=by decide +kernel

theorem coreEmbedding_injective : Function.Injective coreEmbedding := by decide +kernel

theorem coreEmbedding_centralizer : centralizer (coreEmbedding.range:Set W)≤coreEmbedding.range := by
  intro w hw
  have h:∀w:W,(∀a:QuaternionCyclic.Model,coreEmbedding a*w=w*coreEmbedding a)→
      ∃a:QuaternionCyclic.Model,coreEmbedding a=w := by decide +kernel
  exact h w (fun a=>hw _ ⟨a,rfl⟩)

theorem model_not_commutative : ¬IsMulCommutative QuaternionCyclic.Model := by
  intro h
  have hh:=h.is_comm.comm (QuaternionCyclic.quaternionEmbedding (.a 1))
    (QuaternionCyclic.quaternionEmbedding (.xa 0))
  exact (by decide +kernel : QuaternionCyclic.quaternionEmbedding (.a 1)*
    QuaternionCyclic.quaternionEmbedding (.xa 0)≠QuaternionCyclic.quaternionEmbedding (.xa 0)*
      QuaternionCyclic.quaternionEmbedding (.a 1)) hh

theorem model_aut_not_two : ¬IsPGroup 2 (MulAut QuaternionCyclic.Model) := by
  intro hp
  have h:=hp.dvd_orderOf QuaternionCyclic.cubic_ne_one
  rw [QuaternionCyclic.cubic_order] at h
  norm_num at h

theorem nonabelian_centric_model (X:Subgroup W)
    (hc:centralizer (X:Set W)≤X) (hna:¬IsMulCommutative X)
    (hAut:¬IsPGroup 2 (MulAut X)) : Nonempty (X≃*QuaternionCyclic.Model) := by
  obtain ⟨P⟩:=ABG.Wreathed.nonempty_presentation ABG.RegularWreathHeightTwo.isWreathedOfHeight
  have model(X:Subgroup W)(hc:centralizer (X:Set W)≤X)(hna:¬IsMulCommutative X)
      (hAut:¬IsPGroup 2 (MulAut X)) : Nonempty (P.V≃*X) := by
    rcases ABG.Wreathed.exceptional_centric_classification P X hc hAut with h|⟨g,hg⟩
    · subst X
      exact (hna P.base_structure.2.2.1).elim
    · exact ⟨((MulAut.conj g).subgroupMap P.V).trans (MulEquiv.subgroupCongr hg)⟩
  let e:QuaternionCyclic.Model≃*coreEmbedding.range:=MonoidHom.ofInjective coreEmbedding_injective
  have hn:¬IsMulCommutative coreEmbedding.range := by
    intro hh
    apply model_not_commutative
    exact IsMulCommutative.of_comm (fun a b=>e.injective (by
      rw [map_mul,map_mul];exact hh.is_comm.comm _ _))
  have ha:¬IsPGroup 2 (MulAut coreEmbedding.range) := by
    intro hh
    exact model_aut_not_two (hh.of_equiv (MulAut.congr e).symm)
  obtain ⟨e₁⟩:=model X hc hna hAut
  obtain ⟨e₂⟩:=model coreEmbedding.range coreEmbedding_centralizer hn ha
  exact ⟨e₁.symm.trans (e₂.trans e.symm)⟩
end WreathedVertex
