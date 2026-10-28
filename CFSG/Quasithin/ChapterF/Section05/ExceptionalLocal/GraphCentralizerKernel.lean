module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerRootComplement
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerEndpointResidual
/-!
# The four-element residual centralizer and the full centralizer join

Faithfulness of the graph quotient on the A6 residual identifies its
centralizer with the preimage of the quotient residual centralizer. The
latter has order two, so the actual centralizer has order four and lies in
every Sylow two-subgroup. The exact endpoint residual equality identifies
its ambient image with the source R0. The residual Sylow supplement also
proves C_G(f)=RD with the literal R and D inclusions.

Source: Aschbacher--Smith F.5.5(2)--(3), printed p.302. Cyclicity of R0 is
the separate global fusion argument; this module asserts only its order.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)

def sourceResidualCentralizer : Subgroup G :=
  (centralizer (pResidual 2 (C c i):Set (C c i))).map (C c i).subtype

include h in
theorem source_centralizer_card (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    Nat.card (C c i)=2880 := by
  obtain ⟨_,_,_,e,_,_,_,_,_⟩:=source_graph_quotient_marked_product c i z h R hR
  have hq : Nat.card (graphCentralQuotient c i)=1440 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hf : Nat.card (zpowers (graphInCentralizer c i))=2 := by
    rw [Nat.card_zpowers]
    exact (orderOf_coe (graphInCentralizer c i)).symm.trans
      (source_graph_order c i h.embedding_injective)
  have hc := (zpowers (graphInCentralizer c i)).card_mul_index
  rw [hf,index_eq_card,hq] at hc
  omega

include h in
theorem source_residual_centralizer_preimage (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    centralizer (pResidual 2 (C c i):Set (C c i))=
      (centralizer (pResidual 2 (graphCentralQuotient c i):Set (graphCentralQuotient c i))).comap
        (QuotientGroup.mk' (zpowers (graphInCentralizer c i))) := by
  let K:=pResidual 2 (C c i)
  let W:=pResidual 2 (graphCentralQuotient c i)
  let q:=QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  obtain ⟨e,he⟩:=source_centralizer_residual_quotient_equiv c i z h R hR
  have hi : Function.Injective (q.comp K.subtype) := by
    intro a b hab
    apply e.injective
    apply Subtype.ext
    rw [he a,he b]
    exact hab
  ext x
  constructor
  · intro hx
    change q x∈centralizer (W:Set (graphCentralQuotient c i))
    intro w hw
    obtain ⟨k,hk⟩:=e.surjective ⟨w,hw⟩
    have hval : q k.val=w := (he k).symm.trans (congrArg Subtype.val hk)
    rw [←hval,←map_mul,←map_mul,hx k.val k.property]
  · intro hx
    change q x∈centralizer (W:Set (graphCentralQuotient c i)) at hx
    intro y hy
    let yK:K:=⟨y,hy⟩
    have hyq : q y∈W := map_pResidual_le 2 q (mem_map_of_mem q hy)
    have hconj : MulAut.conjNormal x yK=yK := hi (by
      change q (x*y*x⁻¹)=q y
      rw [map_mul,map_mul,map_inv,←hx (q y) hyq,mul_inv_cancel_right])
    have hh : x*y*x⁻¹=y := congrArg Subtype.val hconj
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

include h in
theorem source_residual_centralizer_card (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    Nat.card (centralizer (pResidual 2 (C c i):Set (C c i)))=4 := by
  obtain ⟨hc,_,_,e,_,_,_,_,_⟩:=source_graph_quotient_marked_product c i z h R hR
  have hq : Nat.card (graphCentralQuotient c i)=1440 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hh := (centralizer (pResidual 2 (graphCentralQuotient c i):Set (graphCentralQuotient c i))).card_mul_index
  rw [hc,hq] at hh
  have hi : (centralizer (pResidual 2 (graphCentralQuotient c i):Set (graphCentralQuotient c i))).index=720 := by omega
  have hi' : (centralizer (pResidual 2 (C c i):Set (C c i))).index=720 := by
    rw [source_residual_centralizer_preimage c i z h R hR,
      index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),hi]
  have hm := (centralizer (pResidual 2 (C c i):Set (C c i))).card_mul_index
  rw [hi',source_centralizer_card c i z h R hR] at hm
  omega

include h in
theorem sourceResidualCentralizer_card (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    Nat.card (sourceResidualCentralizer c i)=4 := by
  rw [sourceResidualCentralizer,card_map_of_injective (C c i).subtype_injective]
  exact source_residual_centralizer_card c i z h R hR

include h in
theorem sourceResidualCentralizer_le_R (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    sourceResidualCentralizer c i≤Rimage c i R := by
  apply map_mono
  exact (IsPGroup.of_card (p:=2) (n:=2)
    (source_residual_centralizer_card c i z h R hR)).le_sylow_of_normal R

include h in
theorem source_Rzero_eq_residual_centralizer (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    Rzero c i R=sourceResidualCentralizer c i := by
  rw [Rzero,source_DtwoResidual_eq_centralizer_residual c i z h R hR]
  apply le_antisymm
  · intro x hx
    obtain ⟨xC,hxR,rfl⟩:=hx.1
    refine ⟨xC,?_,rfl⟩
    intro k hk
    exact Subtype.ext (hx.2 k.val (mem_map_of_mem (C c i).subtype hk))
  · intro x hx
    refine ⟨sourceResidualCentralizer_le_R c i z h R hR hx,?_⟩
    obtain ⟨xC,hxC,rfl⟩:=hx
    rintro _ ⟨k,hk,rfl⟩
    exact congrArg Subtype.val (hxC k hk)

include h in
theorem source_Rzero_card (R:Sylow 2 (C c i)) (hR:Tf c i≤R) : Nat.card (Rzero c i R)=4 := by
  rw [source_Rzero_eq_residual_centralizer c i z h R hR]
  exact sourceResidualCentralizer_card c i z h R hR

omit [Finite G] in
theorem source_graph_mem_residual_centralizer : Source.graphElement c i∈sourceResidualCentralizer c i := by
  refine ⟨graphInCentralizer c i,?_,rfl⟩
  intro k _
  exact Subtype.ext (mem_centralizer_singleton_iff.mp k.property)

include h in
theorem source_graph_mem_Rzero (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    Source.graphElement c i∈Rzero c i R := by
  rw [source_Rzero_eq_residual_centralizer c i z h R hR]
  exact source_graph_mem_residual_centralizer c i

include h in
theorem source_centralizer_join (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    C c i=Rimage c i R⊔D c i := by
  have hs:=congrArg (Subgroup.map (C c i).subtype) (pResidual_sup_sylow_eq_top R)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,(C c i).range_subtype,
    ←source_DtwoResidual_eq_centralizer_residual c i z h R hR] at hs
  apply le_antisymm
  · rw [←hs]
    exact sup_le (le_sup_of_le_right (map_subtype_le _) ) le_sup_left
  · exact sup_le (map_subtype_le _) (D_le_C c i)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
