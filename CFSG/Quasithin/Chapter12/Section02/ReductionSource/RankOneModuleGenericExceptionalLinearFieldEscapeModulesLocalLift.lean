module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalLift
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalInvariant

/-!
# The residual kernel in the H-invariant cubic lift

Under the contrary nonabelian-span hypothesis, take the original elementary
cubic closure N and form R = ⟨Nᴴ⟩. This is an H-normal subgroup of both
O₂(H) and O₂(L₂T), strictly larger than N, with the same nontrivial quadratic
image on the original centralizer span modulo ⟨z⟩. Residual generation and
nilpotent saturation locate an element of [R,O²(H)] in that action's kernel
outside N[R,O₂(H)]. Both opposite-image factors remain allowed.

This isolates residual movement invisible to the projected quadratic action.
Its exclusion, and hence the full abelian-span theorem, remain open in this
owner. The original strict-ratio endpoint remains proved in EscapeModules.
Final source assembly remains qt-d-1222-linear-field-cubic-escape; the earlier
cubic local-data construction retains its existing producer.

Source: Aschbacher--Smith 5.1.21--23 and the end of 5.1.14,
printed pp.644--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The H-invariant lift of the surviving quadratic image has genuine
kernel growth inside the two original local cores. -/
theorem linear_cubic_nonabelian_local_hull_kernel
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
    let F₀ := (N.subgroupOf S.H).map (SpanAction.projection s)
    H ≤ normalizer (R : Set G) ∧
      R ≤ H.pCoreIn 2 ⊓ (actor T C ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      (R.subgroupOf S.H).map (SpanAction.projection s) = F₀ ∧
      N < R ∧ ∃ x ∈ ⁅R,residual H⁆, x ∉ N ⊔ ⁅R,H.pCoreIn 2⁆ ∧
        ∀ u ∈ S.U, ⁅u,x⁆ ∈ zpowers z := by
  intro S s N R F₀
  obtain ⟨g,hg,hgn⟩ := d.exists_moving_cubic
  obtain ⟨he,hNQ⟩ := linear_cubic_nonabelian_local_cubic_span
    D h hH hK hnf hlinear hpsl c d hn hne
  obtain ⟨hlocal,_,_,hInv,_⟩ := linear_cubic_nonabelian_local_closure_quadratic
    D h hH hK hnf hlinear hpsl c d hn hne g hg hgn
  have hNH : N ≤ H := hNQ.trans (pCoreIn_le 2 H)
  obtain ⟨_,_,_,_,_,_,_,hFE⟩ := linear_cubic_nonabelian_local_closure_constraints
    D h hH hK hnf hlinear hpsl c d hn hne g hg hgn
  exact ⟨le_normalizer_conjugateSpanBy N H,
    d.local_cubic_hull_le_common_core he hNH,
    d.local_cubic_hull_image s hNH hInv,
    d.local_cubic_hull_kernel_escape s he hNH (le_sup_right.trans hlocal) hInv
      (hFE.trans inf_le_right)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
