module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalLift
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Residual kernel growth inside the original point-centralizer core

Let N be the elementary cubic closure of the original H-span, R its
H-closure, and E = [R,O²(H)]. Sylow normalization of N gives R = NE.
The common-core bound on R puts E in O₂(O²(H)) and O₂(L₂T).
The source normality of O²(H) in C_G(z) then puts E in O₂(C_G(z)),
so its image on the full span modulo ⟨z⟩ is trivial. This proves equality
of the images of N and R without assuming projected invariance.

The two-perfect residual acts idempotently on E. Nilpotent saturation
still supplies an element of E outside N[R,O₂(H)]. Thus E is nontrivial
and H-normal; the trivial generated core prevents C from normalizing E.
The Chapter12 consumer supplies residual normality from the original
maximal, nonfaithful residual geometry. This does not yet exclude E.

Source: Aschbacher--Smith G.2.2--3, 5.1.14(2), 5.1.21--23,
printed pp.332--334,638,644--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {H C : Subgroup G} {z : G}

/-- Sylow invariance identifies exactly the residual part of hull growth. -/
theorem LocalData.local_cubic_hull_residual_generation (d : LocalData T H C z)
    (hTN : (T : Subgroup G) ≤ normalizer
      (conjugateSpanBy (setup T H C z).U C : Set G)) :
    let N := conjugateSpanBy (setup T H C z).U C
    let R := conjugateSpanBy N H
    R = N ⊔ ⁅R,residual H⁆ := by
  intro N R
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans d.g2.local_le
  have hHR : H ≤ normalizer (R : Set G) := le_normalizer_conjugateSpanBy N H
  have hTC : (T : Subgroup G) ≤ normalizer ((⁅R,residual H⁆ : Subgroup G) : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hHR (hTH ht)),
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_residual H (hTH ht))]
  have hTspan : conjugateSpanBy N (T : Subgroup G) = N :=
    le_antisymm (conjugateSpanBy_le le_rfl hTN) (le_conjugateSpanBy _ _)
  have hh := conjugateSpanBy_sup_eq_span_sup_commutator N (residual H) (T : Subgroup G)
    (by simpa only [residual_sup_sylow T H hTH] using hTC)
  simpa only [residual_sup_sylow T H hTH,hTspan] using hh

/-- The entire residual movement lies in the intrinsic residual core and
the point-centralizer core, and has trivial image under the literal projection. -/
theorem LocalData.local_cubic_hull_residual_core (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (setup T H C z).U C))
    (hNH : conjugateSpanBy (setup T H C z).U C ≤ H)
    (hK : centralizer ({z} : Set G) ≤ normalizer (residual H : Set G)) :
    let N := conjugateSpanBy (setup T H C z).U C
    let R := conjugateSpanBy N H
    let E := ⁅R,residual H⁆
    H ≤ normalizer (E : Set G) ∧
      E ≤ (residual H).pCoreIn 2 ⊓
        (actor T C ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      E ≤ (centralizer ({z} : Set G)).pCoreIn 2 ∧
      ⁅E,residual H⁆ = E ∧
      (E.subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s) = ⊥ := by
  intro N R E
  have hHC : H ≤ centralizer ({z} : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  have hRH : R ≤ H := conjugateSpanBy_le_self hNH
  have hHR : H ≤ normalizer (R : Set G) := le_normalizer_conjugateSpanBy N H
  have hER : E ≤ R := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans hHR)
  have hEK : E ≤ residual H := le_normalizer_iff_commutator_le_right.mp
    (hRH.trans (le_normalizer_residual H))
  have hRQ := d.local_cubic_hull_le_common_core he hNH
  have hEQ : E ≤ (residual H).pCoreIn 2 :=
    (le_inf hEK (hER.trans (hRQ.trans inf_le_left))).trans
      (inf_pCoreIn_le_of_le 2 (map_subtype_le _))
  have hEglobal : E ≤ (centralizer ({z} : Set G)).pCoreIn 2 :=
    hEQ.trans (pCoreIn_mono_of_normalizes ((map_subtype_le _).trans hHC) hK)
  refine ⟨?_,le_inf hEQ (hER.trans (hRQ.trans inf_le_right)),hEglobal,?_,?_⟩
  · intro x hx
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hHR hx),
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_residual H hx)]
  · exact commutator_isPPerfect_idempotent (residual H) R
      (isPPerfect_embedded_pResidual 2 H)
      ((isPGroup_pCoreIn 2 H).to_le (hRQ.trans inf_le_left))
      ((map_subtype_le _).trans hHR)
  · apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    apply SpanAction.core_le_projection_kernel s
    obtain ⟨q,hq,hqe⟩ := hEglobal hx
    exact (show q = x from Subtype.ext hqe) ▸ hq

/-- Equality of the two literal images follows from ambient residual normality. -/
theorem LocalData.local_cubic_hull_image_of_normal_residual (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (setup T H C z).U C))
    (hNH : conjugateSpanBy (setup T H C z).U C ≤ H)
    (hTN : (T : Subgroup G) ≤ normalizer
      (conjugateSpanBy (setup T H C z).U C : Set G))
    (hK : centralizer ({z} : Set G) ≤ normalizer (residual H : Set G)) :
    ((conjugateSpanBy (conjugateSpanBy (setup T H C z).U C) H).subgroupOf
      (centralizer ({z} : Set G))).map (SpanAction.projection s) =
    ((conjugateSpanBy (setup T H C z).U C).subgroupOf
      (centralizer ({z} : Set G))).map (SpanAction.projection s) := by
  let N := conjugateSpanBy (setup T H C z).U C
  let R := conjugateSpanBy N H
  let E := ⁅R,residual H⁆
  have hHC : H ≤ centralizer ({z} : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  obtain ⟨_,_,hEQ,_,hker⟩ := d.local_cubic_hull_residual_core s he hNH hK
  have hEC : E ≤ centralizer ({z} : Set G) := hEQ.trans (pCoreIn_le 2 _)
  let π : centralizer ({z} : Set G) →* SpanAction.Actor s := SpanAction.projection s
  have hh := congrArg (fun Y : Subgroup G =>
    (Y.subgroupOf (centralizer ({z} : Set G))).map π)
      (d.local_cubic_hull_residual_generation hTN)
  change (R.subgroupOf (centralizer ({z} : Set G))).map π =
    ((N ⊔ E).subgroupOf (centralizer ({z} : Set G))).map π at hh
  change (E.subgroupOf (centralizer ({z} : Set G))).map π = ⊥ at hker
  rw [subgroupOf_sup (hNH.trans hHC) hEC,Subgroup.map_sup,hker,sup_bot_eq] at hh
  exact hh

/-- Residual normality locates the kernel growth without any projected
invariance premise; the moving kernel subgroup cannot be C-normal. -/
theorem LocalData.local_cubic_residual_kernel_growth (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (setup T H C z).U C))
    (hNH : conjugateSpanBy (setup T H C z).U C ≤ H)
    (hTN : (T : Subgroup G) ≤ normalizer
      (conjugateSpanBy (setup T H C z).U C : Set G))
    (hK : centralizer ({z} : Set G) ≤ normalizer (residual H : Set G)) :
    let N := conjugateSpanBy (setup T H C z).U C
    let R := conjugateSpanBy N H
    let E := ⁅R,residual H⁆
    (∃ x ∈ E, x ∉ N ⊔ ⁅R,H.pCoreIn 2⁆ ∧
      ∀ u ∈ (setup T (centralizer ({z} : Set G)) C z).U, ⁅u,x⁆ ∈ zpowers z) ∧
      ¬ C ≤ normalizer (E : Set G) := by
  intro N R E
  obtain ⟨hHE,hEcore,hEglobal,hidem,hker⟩ :=
    d.local_cubic_hull_residual_core s he hNH hK
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans d.g2.local_le
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hNR : N < R := by
    apply lt_of_le_of_ne (le_conjugateSpanBy _ _)
    intro hh
    apply (d.local_cubic_span_escape he hNH).2
    change H ≤ normalizer (N : Set G)
    rw [hh]
    exact le_normalizer_conjugateSpanBy _ _
  have hRQ : R ≤ H.pCoreIn 2 :=
    (d.local_cubic_hull_le_common_core he hNH).trans inf_le_left
  have hnot : ¬ E ≤ N ⊔ ⁅R,H.pCoreIn 2⁆ := by
    intro hcover
    have hRcover : R ≤ N ⊔ ⁅R,H.pCoreIn 2⁆ :=
      (d.local_cubic_hull_residual_generation hTN).le.trans (sup_le le_sup_left hcover)
    exact (not_le_of_gt hNR) (le_of_le_sup_commutator_of_isNilpotent
      (H.pCoreIn 2) R N (H.pCoreIn 2) (isPGroup_pCoreIn 2 H).isNilpotent
      hRQ ((le_conjugateSpanBy N H).trans hRQ) le_rfl (hQT.trans hTN) hRcover)
  obtain ⟨x,hx,hxN⟩ := SetLike.not_le_iff_exists.mp hnot
  have hEC : E ≤ centralizer ({z} : Set G) := hEglobal.trans (pCoreIn_le 2 _)
  change (E.subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s) = ⊥ at hker
  have hxker : SpanAction.projection s (⟨x,hEC hx⟩ : centralizer ({z} : Set G)) = 1 := by
    have hh := mem_map_of_mem (SpanAction.projection s)
      (show (⟨x,hEC hx⟩ : centralizer ({z} : Set G)) ∈
        E.subgroupOf (centralizer ({z} : Set G)) from hx)
    rw [hker,mem_bot] at hh
    exact hh
  refine ⟨⟨x,hx,hxN,(SpanAction.projection_eq_one_iff s _).mp hxker⟩,?_⟩
  intro hCE
  let J := (actor T C ⊔ (T : Subgroup G)) ⊔ H
  have hJE : J ≤ normalizer (E : Set G) := by
    apply sup_le (sup_le ?_ (hTH.trans hHE)) hHE
    exact conjugateSpanBy_le hCE ((hTH.trans hHE).trans (normalizer _).le_normalizer)
  have hEH : E ≤ H := (hEcore.trans inf_le_left).trans
    ((pCoreIn_le 2 (residual H)).trans (map_subtype_le _))
  have hEJ : E ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 (residual H)).to_le (hEcore.trans inf_le_left))
    (hEH.trans le_sup_right) hJE
  have hJ : J.pCoreIn 2 = ⊥ := by
    change (pCore 2 J).map J.subtype = ⊥
    rw [d.generated_core,Subgroup.map_bot]
  have hxone : x = 1 := by simpa only [hJ,mem_bot] using hEJ hx
  exact hxN (hxone ▸ one_mem _)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
