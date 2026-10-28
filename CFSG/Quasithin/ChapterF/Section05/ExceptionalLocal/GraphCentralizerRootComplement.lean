module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerSplit
/-!
# Lifting the original root-generated symmetric subgroup

The marked quotient sends the original root to a transposition and the
residual to A6, so the root lies outside the residual. Its actual involution
extension therefore has order 720. The literal graph quotient maps that
extension onto the marked S6 factor of the same order, giving a faithful
lift with its quotient map retained.

Source: Aschbacher--Smith F.5.5, printed p.302.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)

abbrev sourceGraphRoot := QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  (sourceRootInGraphCentralizer c i z h)

def sourceRootComplement : Subgroup (C c i) :=
  pResidual 2 (C c i) ⊔ zpowers (sourceRootInGraphCentralizer c i z h)

/-- The actual residual and original root generating the lifted complement. -/
theorem sourceRootComplement_eq :
    sourceRootComplement c i z h =
      pResidual 2 (C c i) ⊔ zpowers (sourceRootInGraphCentralizer c i z h) := by rfl

include h in
theorem source_graph_root_not_mem_residual (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    sourceGraphRoot c i z h ∉ pResidual 2 (graphCentralQuotient c i) := by
  obtain ⟨_,e,q,E,s,hs,ha,hq,hE,_,_,_⟩:=source_graph_quotient_transposition_product c i z h R hR
  intro hr
  have he:=hE ⟨sourceGraphRoot c i z h,mem_sup_left hr⟩
  rw [hq ⟨sourceGraphRoot c i z h,hr⟩,ha] at he
  have hes : (e ⟨sourceGraphRoot c i z h,hr⟩:Equiv.Perm (Fin 6))=s :=
    (congrArg Prod.snd he).symm
  have hh:=(e ⟨sourceGraphRoot c i z h,hr⟩).property
  rw [Equiv.Perm.mem_alternatingGroup,hes,hs.sign_eq] at hh
  norm_num at hh

include h in
theorem source_root_not_mem_centralizer_residual (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    rootElement c i z ∉ (pResidual 2 (C c i)).map (C c i).subtype := by
  rintro ⟨x,hx,he⟩
  apply source_graph_root_not_mem_residual c i z h R hR
  have heq : x=sourceRootInGraphCentralizer c i z h := Subtype.ext he
  rw [heq] at hx
  exact map_pResidual_le 2 (QuotientGroup.mk' (zpowers (graphInCentralizer c i)))
    (mem_map_of_mem _ hx)

include h in
theorem source_rootComplement_card (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    Nat.card (sourceRootComplement c i z h)=720 := by
  obtain ⟨e⟩:=source_centralizer_residual_alternating c i z h R hR
  have hK : Nat.card (pResidual 2 (C c i))=360 :=
    (Nat.card_congr e.toEquiv).trans AlternatingSix.ShadowLocal.card_A6
  have hz2 : sourceRootInGraphCentralizer c i z h ^2=1 :=
    Subtype.ext (source_root_order c i z h ▸ pow_orderOf_eq_one _)
  have hout : sourceRootInGraphCentralizer c i z h∉pResidual 2 (C c i) := by
    intro hh
    exact source_root_not_mem_centralizer_residual c i z h R hR
      (mem_map_of_mem (C c i).subtype hh)
  rw [sourceRootComplement,card_sup_zpowers_of_normalizing_involution _ _ hz2 hout
    (by rw [normalizer_eq_top]; exact mem_top _),hK]

include h in
theorem source_rootComplement_quotient_equiv (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    ∃e:sourceRootComplement c i z h≃*
      (pResidual 2 (graphCentralQuotient c i)⊔zpowers (sourceGraphRoot c i z h):
        Subgroup (graphCentralQuotient c i)),
      ∀x:sourceRootComplement c i z h,(e x).val=
        QuotientGroup.mk' (zpowers (graphInCentralizer c i)) x.val := by
  let q:=QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  let J:=sourceRootComplement c i z h
  let Jstar:=pResidual 2 (graphCentralQuotient c i)⊔zpowers (sourceGraphRoot c i z h)
  have hmap : J.map q=Jstar := by
    change (pResidual 2 (C c i)⊔zpowers (sourceRootInGraphCentralizer c i z h)).map q=Jstar
    rw [Subgroup.map_sup,map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _),
      MonoidHom.map_zpowers]
  let j : J→*Jstar:=(MulEquiv.subgroupCongr hmap).toMonoidHom.comp (q.subgroupMap J)
  have hj : Function.Surjective j := by
    intro y
    have hy : y.val∈J.map q:=hmap.symm ▸ y.property
    obtain ⟨x,hx,he⟩:=hy
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  obtain ⟨_,_,eS,_,_,_,_,_,_⟩:=source_graph_quotient_marked_product c i z h R hR
  have hJstar : Nat.card Jstar=720 := by
    rw [Nat.card_congr eS.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hc : Nat.card J=Nat.card Jstar:= (source_rootComplement_card c i z h R hR).trans hJstar.symm
  exact ⟨MulEquiv.ofBijective j ((Nat.bijective_iff_surjective_and_card j).mpr ⟨hj,hc⟩),fun _=>rfl⟩

include h in
theorem source_rootComplement_symmetric (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    Nonempty (sourceRootComplement c i z h≃*Equiv.Perm (Fin 6)) := by
  obtain ⟨e,_⟩:=source_rootComplement_quotient_equiv c i z h R hR
  obtain ⟨_,_,eS,_,_,_,_,_,_⟩:=source_graph_quotient_marked_product c i z h R hR
  exact ⟨e.trans eS⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
