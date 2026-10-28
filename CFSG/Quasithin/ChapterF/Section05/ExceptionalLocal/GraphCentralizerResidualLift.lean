module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerResidual
public import Theory.GroupTheory.PResidual.FaithfulSylowCover
/-!
# Lifting the graph-centralizer residual faithfully

The literal endpoint dihedral group maps injectively onto the Sylow subgroup
of the quotient residual. Transfer in the two-perfect original residual
places its central graph kernel in the Sylow Frattini subgroup. The faithful
Sylow lift therefore kills that kernel. The residual quotient map itself
is consequently an isomorphism, with its pointwise formula retained.

Source: Aschbacher--Smith F.5.5, printed p.302, the passage from the quotient
residual to the actual residual before identifying D and its centralizer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

theorem source_graph_residual_quotient_faithful_of_sylow
    (P:Sylow 2 (pResidual 2 (graphCentralQuotient c i)))
    (hP:(P:Subgroup (pResidual 2 (graphCentralQuotient c i))).map
      (pResidual 2 (graphCentralQuotient c i)).subtype=sourceResidualJoinQuotient c i) :
    Function.Injective ((QuotientGroup.mk' (zpowers (graphInCentralizer c i))).comp
      (pResidual 2 (C c i)).subtype) := by
  let K:=pResidual 2 (C c i)
  let W:=pResidual 2 (graphCentralQuotient c i)
  let q:=QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  let f:K→*W:=(q.comp K.subtype).codRestrict W (fun x=>map_pResidual_le 2 q (mem_map_of_mem q x.property))
  have hcomp : W.subtype.comp f=q.comp K.subtype := rfl
  have hc : f.ker≤center K := by
    intro x hx
    have hqx : q x.val=1 := congrArg Subtype.val (show f x=1 from hx)
    rcases (graph_quotient_eq_one_iff c i z h x.val).mp hqx with hx1|hxf
    · have hx1' : x=1:=Subtype.ext hx1
      exact hx1' ▸ (center K).one_mem
    · apply mem_center_iff.mpr
      intro a
      apply Subtype.ext
      change a.val*x.val=x.val*a.val
      rw [hxf]
      exact mem_center_iff.mp (graphInCentralizer_mem_center c i) a.val
  have hp : IsPGroup 2 f.ker := by
    intro x
    refine ⟨1,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (x.val.val)^2=1
    have hqx : q x.val.val=1 := congrArg Subtype.val (show f x.val=1 from x.property)
    rcases (graph_quotient_eq_one_iff c i z h x.val.val).mp hqx with hx1|hxf
    · simp [hx1]
    · rw [hxf]
      apply Subtype.ext
      change Source.graphElement c i^2=1
      rw [←source_graph_order c i h.embedding_injective]
      exact pow_orderOf_eq_one _
  let U:Subgroup (C c i):=(sourceResidualJoin c i).subgroupOf (C c i)
  have hUK:U≤K := by
    intro x hx
    exact (mem_map_iff_mem (C c i).subtype_injective).mp
      (sourceResidualJoin_le_twoResidual c i hx)
  let A:=U.subgroupOf K
  have hA : Disjoint A f.ker := by
    apply disjoint_def.mpr
    intro x hx hk
    apply Subtype.ext
    apply Subtype.ext
    let a:sourceResidualJoin c i:=⟨x.val.val,hx⟩
    have hq : sourceOrdinaryGraphQuotientMap c i (sourceResidualJoin c i)
      (sourceResidualJoin_le_C c i) a=1 := by
      exact congrArg Subtype.val (show f x=1 from hk)
    have ha1:a=1:=(sourceOrdinaryGraphQuotientMap_injective c i h.embedding_injective _
      (sourceResidualJoin_le_ordinary c i h.embedding_injective)
      (sourceResidualJoin_le_C c i)) (hq.trans (map_one _).symm)
    change a.val=1
    exact congrArg Subtype.val ha1
  have hAS : A.map f=(P:Subgroup W) := by
    apply map_injective W.subtype_injective
    rw [map_map,hcomp,←map_map,map_subgroupOf_eq_of_le hUK]
    exact hP.symm
  have hk:f.ker=⊥:=ker_eq_bot_of_faithful_sylow_image (isPPerfect_pResidual 2)
    f hc hp A hA P hAS
  exact W.subtype_injective.comp ((MonoidHom.ker_eq_bot_iff f).mp hk)

theorem source_graph_residual_equiv_of_sylow
    (P:Sylow 2 (pResidual 2 (graphCentralQuotient c i)))
    (hP:(P:Subgroup (pResidual 2 (graphCentralQuotient c i))).map
      (pResidual 2 (graphCentralQuotient c i)).subtype=sourceResidualJoinQuotient c i) :
    ∃ e : pResidual 2 (C c i) ≃* pResidual 2 (graphCentralQuotient c i),
      ∀x:pResidual 2 (C c i), (e x).val=
        QuotientGroup.mk' (zpowers (graphInCentralizer c i)) x.val := by
  let K:=pResidual 2 (C c i)
  let W:=pResidual 2 (graphCentralQuotient c i)
  let q:=QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  let f:K→*W:=(q.comp K.subtype).codRestrict W (fun x=>map_pResidual_le 2 q (mem_map_of_mem q x.property))
  have hf:Function.Injective f:=by
    intro x y he
    exact source_graph_residual_quotient_faithful_of_sylow c i z h P hP (congrArg Subtype.val he)
  have hs:Function.Surjective f:=by
    intro y
    have hh : y.val∈K.map q := by
      rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
      exact y.property
    obtain ⟨x,hx,he⟩:=hh
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  exact ⟨MulEquiv.ofBijective f ⟨hf,hs⟩,fun _=>rfl⟩
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
