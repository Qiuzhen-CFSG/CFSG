module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesResidualKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalLift

/-!
# The original residual core carries the surviving kernel movement

The maximal nonfaithful residual geometry supplies O²(H) normal in C_G(z).
For the contrary nonabelian centralizer span, the elementary cubic closure
N and its H-closure R therefore satisfy R = N[R,O²(H)], and their literal
projected images agree. The entire residual commutator E lies in the
original residual two-core, the cubic local two-core and O₂(C_G(z)).

The residual acts idempotently on E, and E contains an element outside
N[R,O₂(H)]. It is H-normal but not C-normal, so its C-closure strictly
enlarges E while staying in O₂(L₂T). Both opposite-image factors remain
allowed. Exclusion of this ambient kernel growth and the abelian-span
conclusion remain open; the original strict-ratio endpoint is unchanged.
Final assembly remains qt-d-1222-linear-field-cubic-escape, with earlier
cubic local data at its existing producer.

Source: Aschbacher--Smith 5.1.14(2), 5.1.21--23 and the end of 5.1.14,
printed pp.638,644--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The original source geometry locates all residual kernel growth, with
its actual normalities, the literal projection, and the escaping cubic. -/
theorem linear_cubic_nonabelian_residual_kernel_growth
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z) (hn : 1 < n)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) :
    let S := setup T (centralizer ({z} : Set G)) C z
    let s := linear_cubic_centralizer_setup h d
    let N := conjugateSpanBy (setup T H C z).U C
    let R := conjugateSpanBy N H
    let E := ⁅R,residual H⁆
    R = N ⊔ E ∧ H ≤ normalizer (E : Set G) ∧
      E ≤ (residual H).pCoreIn 2 ⊓
        (actor T C ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      E ≤ S.H.pCoreIn 2 ∧ ⁅E,residual H⁆ = E ∧
      (E.subgroupOf S.H).map (SpanAction.projection s) = ⊥ ∧
      (R.subgroupOf S.H).map (SpanAction.projection s) =
        (N.subgroupOf S.H).map (SpanAction.projection s) ∧
      E < conjugateSpanBy E C ∧
      conjugateSpanBy E C ≤ (actor T C ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ∃ x ∈ E, x ∉ N ⊔ ⁅R,H.pCoreIn 2⁆ ∧ ∀ u ∈ S.U, ⁅u,x⁆ ∈ zpowers z := by
  intro S s N R E
  obtain ⟨he,hNQ⟩ := linear_cubic_nonabelian_local_cubic_span
    D h hH hK hnf hlinear hpsl c d hn hne
  have hNH : N ≤ H := hNQ.trans (pCoreIn_le 2 H)
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) :=
    le_sup_right.trans (d.local_cubic_span_join_normalized
      c D.sylow_normalizes_component hpsl)
  have hKnormal := point_centralizer_le_residual_normalizer
    h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne
  obtain ⟨hHE,hEcores,hEglobal,hidem,hker⟩ :=
    d.local_cubic_hull_residual_core s he hNH hKnormal
  obtain ⟨hx,hnot⟩ := d.local_cubic_residual_kernel_growth s he hNH hTN hKnormal
  have hstrict : E < conjugateSpanBy E C := by
    apply lt_of_le_of_ne (le_conjugateSpanBy _ _)
    intro hh
    apply hnot
    change C ≤ normalizer (E : Set G)
    rw [hh]
    exact le_normalizer_conjugateSpanBy _ _
  have hCJ : C ≤ actor T C ⊔ (T : Subgroup G) :=
    (le_conjugateSpanBy C (T : Subgroup G)).trans le_sup_left
  have hCQ : C ≤ normalizer
      ((actor T C ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    (hCJ.trans (actor T C ⊔ (T : Subgroup G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  exact ⟨d.local_cubic_hull_residual_generation hTN,hHE,hEcores,hEglobal,hidem,hker,
    d.local_cubic_hull_image_of_normal_residual s he hNH hTN hKnormal,hstrict,
    conjugateSpanBy_le (hEcores.trans inf_le_right) hCQ,hx⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
