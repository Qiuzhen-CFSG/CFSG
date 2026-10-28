module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerKernel
/-!
# The literal symmetric quotient of the graph centralizer

Composing the actual graph quotient with the marked second direct-factor
projection gives a surjection onto S6. Its kernel is precisely the actual
centralizer of the A6 residual, and the original root maps to a transposition.
The root-generated S6 subgroup is a complement to this four-element kernel.

Source: Aschbacher--Smith F.5.5, printed p.302.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
open AlternatingSix.ShadowLocal
local notation "hn" => Nat.le_refl 1
local notation "S6" => Equiv.Perm (Fin 6)
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

theorem source_centralizer_symmetric_projection (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    ∃ (e:pResidual 2 (C c i)≃*A6) (f:C c i→*S6),
      Function.Surjective f ∧
      f.ker=centralizer (pResidual 2 (C c i):Set (C c i)) ∧
      (∀x:pResidual 2 (C c i),f x.val=(e x:S6)) ∧
      (f (sourceRootInGraphCentralizer c i z h)).IsSwap ∧
      (sourceRootComplement c i z h).map f=⊤ := by
  let q:=QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  obtain ⟨_,eW,eD,E,s,hs,hEs,heW,hED,_,_,hEker⟩:=
    source_graph_quotient_transposition_product c i z h R hR
  obtain ⟨eK,heK⟩:=source_centralizer_residual_quotient_equiv c i z h R hR
  let f : C c i→*S6 := (MonoidHom.snd _ _).comp (E.toMonoidHom.comp q)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩:=(QuotientGroup.mk'_surjective (zpowers (graphInCentralizer c i))) (E.symm (1,y))
    refine ⟨x,?_⟩
    change (E (q x)).2=y
    rw [hx,E.apply_symm_apply]
  have hker : f.ker=centralizer (pResidual 2 (C c i):Set (C c i)) := by
    rw [source_residual_centralizer_preimage c i z h R hR]
    ext x
    exact hEker (q x)
  have he (x:pResidual 2 (C c i)) : f x.val=(eW (eK x):S6) := by
    change (E (q x.val)).2=_
    rw [←heK x]
    exact congrArg Prod.snd ((hED ⟨(eK x).val,mem_sup_left (eK x).property⟩).trans
      (congrArg (fun y:S6=>(1,y)) (heW (eK x))))
  have hroot : f (sourceRootInGraphCentralizer c i z h)=s := congrArg Prod.snd hEs
  refine ⟨eK.trans eW,f,hf,hker,he,hroot ▸ hs,?_⟩
  apply top_unique
  intro y _
  obtain ⟨eJ,heJ⟩:=source_rootComplement_quotient_equiv c i z h R hR
  let u:=eD.symm y
  let x:=eJ.symm u
  refine ⟨x.val,x.property,?_⟩
  change (E (q x.val)).2=y
  rw [←heJ x,eJ.apply_symm_apply]
  exact (congrArg Prod.snd (hED u)).trans (eD.apply_symm_apply y)

theorem source_centralizer_residualCentralizer_quotient (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    Nonempty ((C c i⧸centralizer (pResidual 2 (C c i):Set (C c i)))≃*S6) := by
  obtain ⟨_,f,hf,hker,_,_,_⟩:=source_centralizer_symmetric_projection c i z h R hR
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

theorem source_residualCentralizer_sup_rootComplement (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    centralizer (pResidual 2 (C c i):Set (C c i))⊔sourceRootComplement c i z h=⊤ := by
  obtain ⟨_,f,_,hker,_,_,hm⟩:=source_centralizer_symmetric_projection c i z h R hR
  have hh:=congrArg (Subgroup.comap f) hm
  rw [comap_map_eq,comap_top,hker,sup_comm] at hh
  exact hh

theorem source_residualCentralizer_disjoint_rootComplement (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    Disjoint (centralizer (pResidual 2 (C c i):Set (C c i))) (sourceRootComplement c i z h) := by
  obtain ⟨_,f,_,hker,_,_,hm⟩:=source_centralizer_symmetric_projection c i z h R hR
  have hj : Function.Bijective (f.subgroupMap (sourceRootComplement c i z h)) := by
    apply (Nat.bijective_iff_surjective_and_card _).mpr
    refine ⟨f.subgroupMap_surjective _,?_⟩
    rw [source_rootComplement_card c i z h R hR,hm,card_top]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  apply disjoint_def.mpr
  intro x hxK hxJ
  have hx : f x=1 := by rw [←hker] at hxK; exact hxK
  have he : (⟨x,hxJ⟩:sourceRootComplement c i z h)=1 := hj.injective (Subtype.ext (by
    change f x=f 1
    rw [hx,map_one]))
  exact congrArg Subtype.val he

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
