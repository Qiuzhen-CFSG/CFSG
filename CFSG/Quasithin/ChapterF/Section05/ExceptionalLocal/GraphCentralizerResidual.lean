module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerModel
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionResidualJoin
public import Theory.GroupTheory.DihedralResidualTransfer
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Eight
/-!
# The residual of the graph centralizer

The center of the literal endpoint dihedral subgroup lies in the derived
line of the Sylow quotient, identifying it with the previously transported
root image. Its full centralizer is therefore the Sylow subgroup. Successive
transfer identifies the residual Sylow with this endpoint subgroup. Fusion
inside the residual then gives the exact I.4.1(2) hypotheses, hence A6 or PSL3(2).

Source: Aschbacher--Smith F.5.5, printed pp.301--302. The residual fusion
premise is isolated for the earlier endpoint conjugator producer; no residual
recognition or simplicity is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

theorem source_residual_center_centralizer (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    centralizer ({sourceResidualQuotientCenter c i h.embedding_injective}:
      Set (graphCentralQuotient c i))=
      (R:Subgroup (C c i)).map (QuotientGroup.mk' (zpowers (graphInCentralizer c i))) := by
  classical
  obtain ⟨u,ho,hC,hd⟩:=source_graph_quotient_derived_centralizer c i z h R hR
  let q:=QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  let U:=sourceResidualJoinQuotient c i
  let e:=sourceResidualJoinQuotientEquiv c i h.embedding_injective
  let v:U:=⟨sourceResidualQuotientCenter c i h.embedding_injective,
    sourceResidualQuotientCenter_mem c i h.embedding_injective⟩
  have he : e v=DihedralGroup.r 2 := sourceResidualJoinQuotientEquiv_center c i h.embedding_injective
  have hvComm : v.val∈⁅U,U⁆ := by
    have hd8 : ⁅(DihedralGroup.r 1:DihedralGroup 4),(DihedralGroup.sr 0:DihedralGroup 4)⁆=DihedralGroup.r 2 := by decide +kernel
    have hcomm : ⁅e.symm (DihedralGroup.r 1),e.symm (DihedralGroup.sr 0)⁆=v := by
      apply e.injective
      rw [map_commutatorElement,e.apply_symm_apply,e.apply_symm_apply,hd8,he]
    rw [←hcomm]
    exact commutator_mem_commutator (e.symm _).property (e.symm _).property
  have hle:=sourceResidualJoinQuotient_le_R c i h.embedding_injective R hR
  have hvLine : v.val∈zpowers (q u) := hd ▸ (commutator_mono hle hle hvComm)
  have hv1 : v.val≠1 := by
    intro hh
    have hv : v=1 := Subtype.ext hh
    have hh' := he
    rw [hv,e.map_one] at hh'
    exact (by decide : (1:DihedralGroup 4)≠DihedralGroup.r 2) hh'
  have hval : v.val=q u := by
    rw [mem_zpowers_iff_mem_range_orderOf,ho] at hvLine
    obtain ⟨n,hmem,hne⟩:=Finset.mem_image.mp hvLine
    have hnb:=Finset.mem_range.mp hmem
    have hcase : n=0∨n=1 := by omega
    rcases hcase with rfl|rfl
    · exact (hv1 (by simpa using hne.symm)).elim
    · simpa using hne.symm
  rw [←hval] at hC
  exact hC

theorem source_graph_residual_sylow_of_residual_fusion
    (R:Sylow 2 (C c i)) (hR:Tf c i≤R)
    (hf : ∀x:sourceResidualJoinQuotient c i,orderOf x=2 →
      IsConj (⟨sourceResidualQuotientCenter c i h.embedding_injective,
        sourceResidualJoinQuotient_le_twoResidual c i
          (sourceResidualQuotientCenter_mem c i h.embedding_injective)⟩:
        pResidual 2 (graphCentralQuotient c i))
      ⟨x.val,sourceResidualJoinQuotient_le_twoResidual c i x.property⟩) :
    ∃P:Sylow 2 (pResidual 2 (graphCentralQuotient c i)),
      (P:Subgroup (pResidual 2 (graphCentralQuotient c i))).map
        (pResidual 2 (graphCentralQuotient c i)).subtype=sourceResidualJoinQuotient c i := by
  let q:=QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  let S:=R.mapSurjective (f:=q) (QuotientGroup.mk'_surjective _)
  let Z:Subgroup (graphCentralQuotient c i):=(center S).map (S:Subgroup (graphCentralQuotient c i)).subtype
  let : IsElementaryAbelian 2 (center S):=source_graph_quotient_center_elementary c i z h R hR
  let : IsElementaryAbelian 2 Z:=IsElementaryAbelian.map_subtype
  have hZC : Z≤centralizer (S:Set (graphCentralQuotient c i)) := by
    rintro x ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hZcard : Nat.card Z=8 := by
    rw [card_map_of_injective (S:Subgroup (graphCentralQuotient c i)).subtype_injective]
    exact source_graph_quotient_center_card c i z h R hR
  apply DihedralCentralExtensionTransfer.residual_sylow_eq_of_center_nonfusion S
    (source_graph_quotient_sylow_card c i z h R hR) Z (map_subtype_le _) hZC hZcard
    (fun x hx y hy hxy=>source_graph_quotient_center_nonfusion c i z h R hR x y
      (hZC hx) (hZC hy) hxy)
    (sourceResidualJoinQuotient c i)
    (sourceResidualJoinQuotient_le_R c i h.embedding_injective R hR)
    (sourceResidualJoinQuotient_le_twoResidual c i)
    (sourceResidualJoinQuotientEquiv c i h.embedding_injective) _ hf

theorem source_graph_residual_recognition_of_residual_fusion
    (R:Sylow 2 (C c i)) (hR:Tf c i≤R)
    (hf : ∀x:sourceResidualJoinQuotient c i,orderOf x=2 →
      IsConj (⟨sourceResidualQuotientCenter c i h.embedding_injective,
        sourceResidualJoinQuotient_le_twoResidual c i
          (sourceResidualQuotientCenter_mem c i h.embedding_injective)⟩:
        pResidual 2 (graphCentralQuotient c i))
      ⟨x.val,sourceResidualJoinQuotient_le_twoResidual c i x.property⟩) :
    Nonempty ((pResidual 2 (graphCentralQuotient c i)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
    Nonempty ((pResidual 2 (graphCentralQuotient c i)) ≃* alternatingGroup (Fin 6)) := by
  let W:=pResidual 2 (graphCentralQuotient c i)
  let U:=sourceResidualJoinQuotient c i
  have hUW : U≤W:=sourceResidualJoinQuotient_le_twoResidual c i
  let v:U:=⟨sourceResidualQuotientCenter c i h.embedding_injective,
    sourceResidualQuotientCenter_mem c i h.embedding_injective⟩
  let vW:W:=⟨v.val,hUW v.property⟩
  let eU:=sourceResidualJoinQuotientEquiv c i h.embedding_injective
  have hv2 : orderOf v=2 := by
    rw [←eU.orderOf_eq v,sourceResidualJoinQuotientEquiv_center c i h.embedding_injective]
    exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hvW2 : orderOf vW=2 := (orderOf_coe vW).symm.trans ((orderOf_coe v).trans hv2)
  obtain ⟨P,hP⟩:=source_graph_residual_sylow_of_residual_fusion c i z h R hR hf
  change (P:Subgroup W).map W.subtype=U at hP
  let q:=QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  let S:=R.mapSurjective (f:=q) (QuotientGroup.mk'_surjective _)
  have hUS : U≤S:=sourceResidualJoinQuotient_le_R c i h.embedding_injective R hR
  have hInt : (S:Subgroup (graphCentralQuotient c i))⊓W=U := by
    obtain ⟨Q,hQ⟩:=S.exists_sylow_map_eq_inf_of_normal W
    apply (eq_of_le_of_card_ge (le_inf hUS hUW) ?_).symm
    rw [←hQ,card_map_of_injective W.subtype_injective]
    rw [←hP,card_map_of_injective W.subtype_injective]
    exact (Nat.card_congr (Sylow.equiv Q P).toEquiv).le
  have hcent : centralizer ({vW}:Set W)=U.subgroupOf W := by
    ext x
    have hh : x∈centralizer ({vW}:Set W) ↔
        x.val∈centralizer ({v.val}:Set (graphCentralQuotient c i)) := by
      simp only [mem_centralizer_singleton_iff]
      exact Subtype.ext_iff
    rw [hh,source_residual_center_centralizer c i z h R hR]
    constructor
    · intro hx
      exact hInt ▸ (show x.val∈(S:Subgroup (graphCentralQuotient c i))⊓W from ⟨hx,x.property⟩)
    · intro hx
      exact hUS hx
  let he : DihedralInvolutionCentralizerHypotheses W 3 := {
    two_le := by decide
    z := vW
    involution := ⟨fun hv=>by rw [hv,orderOf_one] at hvW2; omega,
      by rw [←hvW2]; exact pow_orderOf_eq_one _⟩
    involutions_conjugate := by
      intro x hx
      have hx2:orderOf x=2:=orderOf_eq_prime hx.2 hx.1
      have hp:IsPGroup 2 (zpowers x):=IsPGroup.of_card (n:=1) (by rw [Nat.card_zpowers,hx2,pow_one])
      obtain ⟨Q,hQ⟩:=hp.exists_le_sylow
      obtain ⟨g,hg⟩:=MulAction.exists_smul_eq W Q P
      have hxP : MulAut.conj g x∈(P:Subgroup W) := by
        rw [←hg]
        exact mem_map_of_mem _ (hQ (mem_zpowers x))
      have hxU : (MulAut.conj g x).val∈U := hP ▸ mem_map_of_mem W.subtype hxP
      let y:U:=⟨(MulAut.conj g x).val,hxU⟩
      have hy2:orderOf y=2 := (orderOf_coe y).symm.trans
        ((orderOf_coe (MulAut.conj g x)).trans (((MulAut.conj g).orderOf_eq x).trans hx2))
      have hy: IsConj vW (MulAut.conj g x) := hf y hy2
      exact isConj_iff.mp ((isConj_iff.mpr ⟨g,rfl⟩).trans hy.symm)
    centralizer_equiv := ⟨(MulEquiv.subgroupCongr hcent).trans
      ((subgroupOfEquivOfLe hUW).trans eU)⟩ }
  exact he.recognize_eight

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
