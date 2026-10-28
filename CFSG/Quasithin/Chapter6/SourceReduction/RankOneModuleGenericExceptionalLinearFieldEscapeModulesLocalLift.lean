module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalInvariant
public import Theory.GroupTheory.Commutator.NilpotentSaturation
public import Theory.GroupTheory.ConjugateSpanKernel
public import Theory.GroupTheory.SubgroupTransport

/-!
# Lifting the cubic image and locating its residual kernel

Write U₀ for the original H-span and N for its elementary cubic closure.
The original kernel condition puts C_H(U₀) in O₂(H); the Sylow centralizer
identity also puts it in O₂(L₂T). Thus R = ⟨Nᴴ⟩ lies in both cores.
If the image of N in the centralizer-span action is H-invariant, R has
exactly the same image, although N < R by the generated-core condition.

The growth survives modulo [R,O₂(H)]: otherwise nilpotent commutator
saturation would give R = N. Since T normalizes N and H = O²(H)T, the
growth comes from [R,O²(H)]. If the projected N centralizes the residual
image, this commutator lies in the literal kernel on U/⟨z⟩. The result
therefore supplies a new residual kernel element, not an unjustified
lift of projected invariance to N. The Chapter12 application discharges
all the image and containment premises using the original geometry.

Source: Aschbacher--Smith G.2.2--3, 5.1.21--23 and the kernel condition
at the end of 5.1.14, printed pp.332--334,644--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {H C : Subgroup G} {z : G}

/-- The exact centralizer of the original span lies in both local two-cores. -/
theorem LocalData.local_span_centralizer_le_common_core (d : LocalData T H C z) :
    H ⊓ centralizer ((setup T H C z).U : Set G) ≤
      H.pCoreIn 2 ⊓ (actor T C ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let U₀ := (setup T H C z).U
  have hQ : H ⊓ centralizer (U₀ : Set G) ≤ H.pCoreIn 2 := by
    intro x hx
    have hk : (⟨x,hx.1⟩ : H) ∈ (SpanAction.projection d.g2).ker := by
      apply (SpanAction.projection_eq_one_iff d.g2 _).mpr
      intro u hu
      have he : ⁅u,x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 u hu)
      rw [he]
      exact one_mem _
    rw [d.local_projection_kernel] at hk
    exact mem_map_of_mem H.subtype hk
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans d.g2.local_le
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  refine le_inf hQ ?_
  rw [← d.centralizer_eq]
  exact le_inf (hQ.trans hQT)
    (inf_le_right.trans (centralizer_le (le_conjugateSpanBy _ _)))

/-- The H-closure of an elementary cubic closure is an actual common-core subgroup. -/
theorem LocalData.local_cubic_hull_le_common_core (d : LocalData T H C z)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (setup T H C z).U C))
    (hNH : conjugateSpanBy (setup T H C z).U C ≤ H) :
    conjugateSpanBy (conjugateSpanBy (setup T H C z).U C) H ≤
      H.pCoreIn 2 ⊓ (actor T C ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let N := conjugateSpanBy (setup T H C z).U C
  let : IsElementaryAbelian 2 N := he
  have hNC : N ≤ centralizer ((setup T H C z).U : Set G) :=
    N.le_centralizer.trans (centralizer_le (le_conjugateSpanBy _ _))
  have hHN : H ≤ normalizer
      (H ⊓ centralizer ((setup T H C z).U : Set G) : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  exact (conjugateSpanBy_le (le_inf hNH hNC) hHN).trans
    d.local_span_centralizer_le_common_core

omit [Finite G] in
private theorem subgroupOf_span {N H X : Subgroup G} (hNX : N ≤ X) (hHX : H ≤ X) :
    (conjugateSpanBy N H).subgroupOf X =
      conjugateSpanBy (N.subgroupOf X) (H.subgroupOf X) := by
  apply map_injective X.subtype_injective
  rw [map_subgroupOf_eq_of_le (conjugateSpanBy_le hNX (hHX.trans X.le_normalizer)),
    map_conjugateSpanBy, map_subgroupOf_eq_of_le hNX, map_subgroupOf_eq_of_le hHX]

/-- Lifting invariance by taking the H-closure preserves the literal projected image. -/
theorem LocalData.local_cubic_hull_image (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (hNH : conjugateSpanBy (setup T H C z).U C ≤ H)
    (hInv : (H.subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s) ≤
      normalizer ((((conjugateSpanBy (setup T H C z).U C).subgroupOf
        (centralizer ({z} : Set G))).map (SpanAction.projection s)) :
          Set (SpanAction.Actor s))) :
    ((conjugateSpanBy (conjugateSpanBy (setup T H C z).U C) H).subgroupOf
      (centralizer ({z} : Set G))).map (SpanAction.projection s) =
    ((conjugateSpanBy (setup T H C z).U C).subgroupOf
      (centralizer ({z} : Set G))).map (SpanAction.projection s) := by
  have hHC : H ≤ centralizer ({z} : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  let π : centralizer ({z} : Set G) →* SpanAction.Actor s := SpanAction.projection s
  change ((conjugateSpanBy (conjugateSpanBy (setup T H C z).U C) H).subgroupOf
    (centralizer ({z} : Set G))).map π =
      ((conjugateSpanBy (setup T H C z).U C).subgroupOf
        (centralizer ({z} : Set G))).map π
  rw [subgroupOf_span (hNH.trans hHC) hHC, map_conjugateSpanBy]
  exact le_antisymm (conjugateSpanBy_le le_rfl hInv) (le_conjugateSpanBy _ _)

/-- Residual growth in the literal kernel survives modulo the local-core
commutators, so the projected invariance does not remove the ambient obstruction. -/
theorem LocalData.local_cubic_hull_kernel_escape (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (setup T H C z).U C))
    (hNH : conjugateSpanBy (setup T H C z).U C ≤ H)
    (hTN : (T : Subgroup G) ≤ normalizer
      (conjugateSpanBy (setup T H C z).U C : Set G))
    (hInv : (H.subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s) ≤
      normalizer ((((conjugateSpanBy (setup T H C z).U C).subgroupOf
        (centralizer ({z} : Set G))).map (SpanAction.projection s)) :
          Set (SpanAction.Actor s)))
    (hCent : ((conjugateSpanBy (setup T H C z).U C).subgroupOf
      (centralizer ({z} : Set G))).map (SpanAction.projection s) ≤
        centralizer ((((residual H).subgroupOf (centralizer ({z} : Set G))).map
          (SpanAction.projection s)) : Set (SpanAction.Actor s))) :
    let N := conjugateSpanBy (setup T H C z).U C
    let R := conjugateSpanBy N H
    N < R ∧ ∃ x ∈ ⁅R,residual H⁆, x ∉ N ⊔ ⁅R,H.pCoreIn 2⁆ ∧
      ∀ u ∈ (setup T (centralizer ({z} : Set G)) C z).U, ⁅u,x⁆ ∈ zpowers z := by
  intro N R
  have hHC : H ≤ centralizer ({z} : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  have hRH : R ≤ H := conjugateSpanBy_le_self hNH
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
    exact le_normalizer_conjugateSpanBy N H
  let π : centralizer ({z} : Set G) →* SpanAction.Actor s := SpanAction.projection s
  have him : (R.subgroupOf (centralizer ({z} : Set G))).map π =
      (N.subgroupOf (centralizer ({z} : Set G))).map π :=
    d.local_cubic_hull_image s hNH hInv
  have hRQ : R ≤ H.pCoreIn 2 :=
    (d.local_cubic_hull_le_common_core he hNH).trans inf_le_left
  have hnot : ¬ R ≤ N ⊔ ⁅R,H.pCoreIn 2⁆ := by
    intro hcover
    exact (not_le_of_gt hNR) (le_of_le_sup_commutator_of_isNilpotent
      (H.pCoreIn 2) R N (H.pCoreIn 2) (isPGroup_pCoreIn 2 H).isNilpotent
      hRQ ((le_conjugateSpanBy N H).trans hRQ) le_rfl (hQT.trans hTN) hcover)
  have hHR : H ≤ normalizer (R : Set G) := le_normalizer_conjugateSpanBy N H
  have hTK : (T : Subgroup G) ≤ normalizer (residual H : Set G) :=
    hTH.trans (le_normalizer_residual H)
  have hTC : (T : Subgroup G) ≤ normalizer ((⁅R,residual H⁆ : Subgroup G) : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hHR (hTH ht)),
      mem_normalizer_iff_map_conj_eq.mp (hTK ht)]
  have hTspan : conjugateSpanBy N (T : Subgroup G) = N :=
    le_antisymm (conjugateSpanBy_le le_rfl hTN) (le_conjugateSpanBy _ _)
  have hgen : R = N ⊔ ⁅R,residual H⁆ := by
    have hh := conjugateSpanBy_sup_eq_span_sup_commutator N (residual H) (T : Subgroup G)
      (by simpa only [residual_sup_sylow T H hTH] using hTC)
    simpa only [residual_sup_sylow T H hTH,hTspan] using hh
  have hcommNot : ¬ ⁅R,residual H⁆ ≤ N ⊔ ⁅R,H.pCoreIn 2⁆ := by
    intro hh
    exact hnot (hgen.le.trans (sup_le le_sup_left hh))
  obtain ⟨x,hx,hxN⟩ := SetLike.not_le_iff_exists.mp hcommNot
  have hKR : ⁅R,residual H⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans hHR)
  have hmap : ((⁅R,residual H⁆ : Subgroup G).subgroupOf
      (centralizer ({z} : Set G))).map π = ⊥ := by
    rw [SubgroupTransport.subgroupOf_commutator R (residual H)
      (hRH.trans hHC) ((map_subtype_le _).trans hHC),map_commutator,him]
    exact commutator_eq_bot_iff_le_centralizer.mpr hCent
  let x' : centralizer ({z} : Set G) := ⟨x,hHC (hRH (hKR hx))⟩
  have hk : π x' = 1 := by
    have hh : π x' ∈ ((⁅R,residual H⁆ : Subgroup G).subgroupOf
        (centralizer ({z} : Set G))).map π := mem_map_of_mem _ hx
    simpa only [hmap,mem_bot] using hh
  exact ⟨hNR,x,hx,hxN,(SpanAction.projection_eq_one_iff s x').mp hk⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
