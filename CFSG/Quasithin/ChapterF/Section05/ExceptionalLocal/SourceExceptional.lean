module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.SourceUpper
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionAmbient
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionGraphSylowModel
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionLocalTable
public import Theory.GroupTheory.GeneralizedThompsonTransfer
public import Theory.GroupTheory.SylowIndexTwoExtension
/-!
# Thompson transfer into the exceptional doubled-unitary branch

Assume the marked graph centralizer has its predicted Sylow subgroup of
order 32. A conjugate of the marked short involution would carry a two-group
of order 64 into that centralizer, which is impossible. Graph/root nonfusion
is already proved from the source hypotheses. The ordinary upper subgroup
has index two in the ambient Sylow, and each of its involutions is fused to
a root or short involution. Thompson transfer therefore puts the graph
involution outside O²(G), contradicting the original residual hypothesis.

The final source theorem discharges the short-centralizer order with the
marked affine-Sylow calculation. It retains only the original hypotheses;
no exceptional-case, fusion or model-recognition assumption is added.
Source: Aschbacher--Smith F.4.38, printed p.294, specialized to Aut(U₄(2)).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

private theorem graph_not_conjugate_short_of_nonexceptional
    (hi : Function.Injective i)
    (hshort : 32 < Nat.card (Tcentralizer c i (sourceMarkedShort c i)))
    (R : Sylow 2 (C c i)) (hR : (R : Subgroup (C c i))=Tf c i) :
    ¬ IsConj (Source.graphElement c i) (sourceMarkedShort c i) := by
  intro hf
  obtain ⟨g,hg⟩ := isConj_iff.mp hf.symm
  let a : G ≃* G := MulAut.conj g
  let K := (Tcentralizer c i (sourceMarkedShort c i)).map a.toMonoidHom
  have hKC : K ≤ C c i := by
    rintro _ ⟨k,hk,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change a k * Source.graphElement c i = Source.graphElement c i * a k
    have hh := congrArg a (mem_centralizer_singleton_iff.mp hk.2)
    simpa only [map_mul,show a (sourceMarkedShort c i)=Source.graphElement c i from hg] using hh
  have hTp : IsPGroup 2 (Tcentralizer c i (sourceMarkedShort c i)) :=
    (source_sylowImage_isTwoGroup c i).of_injective
      (inclusion (show Tcentralizer c i (sourceMarkedShort c i) ≤ Source.sylowImage c i from inf_le_left))
      (inclusion_injective _)
  have hKp : IsPGroup 2 K := hTp.map _
  have hc := card_le_sylow_two (W := K.subgroupOf (C c i)) hKp.comap_subtype R
  have hRc : Nat.card R=32 := (congrArg (fun A : Subgroup (C c i) => Nat.card A) hR).trans
    (source_Tf_card c i hi)
  rw [Nat.card_congr (subgroupOfEquivOfLe hKC).toEquiv,hRc,
    show Nat.card K=Nat.card (Tcentralizer c i (sourceMarkedShort c i)) from
      card_map_of_injective a.injective] at hc
  exact hshort.not_ge hc

/-- Thompson transfer forces the exceptional branch once the marked short
centralizer has the concrete order supplied by the local model calculation. -/
theorem source_exceptional_of_short_centralizer_card
    (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
    (hshort : Nat.card (Tcentralizer c i (sourceMarkedShort c i))=64) :
    Source.Exceptional c i := by
  intro hnex
  obtain ⟨R,hR⟩ := hnex
  have hfs := graph_not_conjugate_short_of_nonexceptional c i h.embedding_injective
    (by rw [hshort]; decide) R hR
  obtain ⟨T,hT⟩ := source_sylowImage_isSylow c i z h
  let S : Subgroup T := (sourceOrdinaryUpper c i).subgroupOf (T : Subgroup G)
  have hS : S.index=2 := by
    change (sourceOrdinaryUpper c i).relIndex (T : Subgroup G)=2
    rw [hT]
    exact sourceOrdinaryUpper_relIndex c i h.embedding_injective
  have hno : ∀ v : T, IsConj (Source.graphElement c i) (v:G) → v∉S := by
    intro v hfv hv
    have hv2 : orderOf (v:G)=2 := by
      obtain ⟨g,hg⟩ := isConj_iff.mp hfv
      rw [←hg]
      exact ((MulAut.conj g).orderOf_eq (Source.graphElement c i)).trans
        (source_graph_order c i h.embedding_injective)
    rcases sourceOrdinaryUpper_involution_classes c i z h v hv hv2 with hr | ht
    · exact Source.graph_not_conjugate_root c i z h (hfv.trans hr.symm)
    · exact hfs (hfv.trans ht.symm)
  have hf := T.involution_not_mem_twoResidual_of_no_conjugate S hS
    (Source.graphElement c i) (source_graph_order c i h.embedding_injective) hno
  apply hf
  rw [h.two_residual]
  exact mem_top _
/-- The original doubled source hypotheses force failure of F.4.37(4)(i).
All local orders, fusion coverage and transfer premises are discharged. -/
theorem source_exceptional (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    Source.Exceptional c i :=
  source_exceptional_of_short_centralizer_card c i z h
    (source_short_Tcentralizer_card c i h.embedding_injective)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
