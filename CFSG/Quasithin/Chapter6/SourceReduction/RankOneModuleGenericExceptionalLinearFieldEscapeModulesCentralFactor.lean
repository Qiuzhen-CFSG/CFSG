module
public import Theory.Representation.BinaryOffender.NonfixedLineCubic
public import Theory.Representation.BinaryConjugationSection.FixedMoving
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscape
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesFiltration

/-!
# Cubicity of the actual opposite centralizer factor

The plane quotient is not fixed by the original residual: otherwise that
normal residual lies in the normal core of the seed centralizer, hence in
O₂(H), forcing H to equal the Sylow subgroup. The source kernel condition
proves this directly, without an irreducible-module choice.

The opposite action's third displacements lie in this binary line. On its
residual-centralizer intersection they commute with the residual, so they
vanish. Thus this surviving factor is cubic even when both opposite factors
are nontrivial, without assuming fixedness of S₂ modulo the original point.

Source: Aschbacher--Smith G.2.3 and 5.1.23, printed pp.333--334,645--646,
refs/quasithin.pdf. The Chapter12 consumer supplies the original groups.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {H C : Subgroup G} {z : G}

/-- The original kernel condition prevents the residual from fixing the plane quotient. -/
theorem LocalData.plane_image_not_residual_fixed
    (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (hHT : ¬ H ≤ (T : Subgroup G)) :
    ¬ (SpanAction.conjugationSection s).imageSpace (plane C z) ≤
      fixedSpace (SpanAction.representation s)
        (((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)) := by
  intro hf
  let S := setup T (centralizer ({z} : Set G)) C z
  let q := SpanAction.conjugationSection s
  have hHC : H ≤ S.H := by
    change H ≤ centralizer ({z} : Set G)
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans d.g2.local_le
  have hseed : pResidual 2 H ≤ ChapterF.Section08.Setup.quotientCentralizer
      (setup T H C z) d.g2.H_le (plane C z) := by
    intro a ha
    apply (ChapterF.Section08.Setup.mem_quotientCentralizer_iff _ _ _
      (d.g2.V_le_T.trans (hTH.trans d.g2.H_le)) a).mpr
    intro v hv
    let v' : S.U := ⟨v,le_conjugateSpanBy _ _ hv⟩
    let a' : S.H := inclusion hHC a
    have hK : SpanAction.projection s a' ∈
        ((residual H).subgroupOf S.H).map (SpanAction.projection s) :=
      ⟨a',⟨a,ha,rfl⟩,rfl⟩
    exact (q.fixed_coordinate_iff_commutator_mem a' v').mp
      (hf ((q.mem_imageSpace_iff _ _).mpr ⟨v',hv,rfl⟩) ⟨_,hK⟩)
  have hres : pResidual 2 H ≤ pCore 2 H :=
    (normal_le_normalCore.mpr hseed).trans d.kernel_core
  have hcoreT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  apply hHT
  rw [← residual_sup_sylow T H hTH]
  exact sup_le ((map_mono hres).trans hcoreT) le_rfl

/-- The residual-centralizer factor is cubic even when both opposite factors survive. -/
theorem LocalData.opposite_centralizer_cubic
    (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (b : (setup T (centralizer ({z} : Set G)) C z).BinaryNaturalData)
    (hHT : ¬ H ≤ (T : Subgroup G))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := setup T (centralizer ({z} : Set G)) C z
    let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
    let K := ((residual H).subgroupOf S.H).map (SpanAction.projection s)
    IsCubic (SpanAction.representation s) (E ⊓ centralizer (K : Set (SpanAction.Actor s))) := by
  intro S E K
  let q := SpanAction.conjugationSection s
  have hcard : Nat.card (q.imageSpace (plane C z)) = 2 := by
    change Nat.card (q.imageSpace S.V) = 2
    rw [q.imageSpace_card_eq_relIndex S.V (le_conjugateSpanBy _ _)]
    change (zpowers z).relIndex (plane C z) = 2
    have hi := ((zpowers z).subgroupOf (plane C z)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show zpowers z ≤ plane C z from d.g2.point_le)).toEquiv,
      d.point_card,d.plane_card] at hi
    change 2 * (zpowers z).relIndex (plane C z) = 4 at hi
    omega
  apply cubic_centralizer_of_third_displacement_line (SpanAction.representation s)
    K E (q.imageSpace (plane C z)) hcard (d.plane_image_not_residual_fixed s hHT)
  exact SpanAction.binary_opposite_third_displacement s b g
    (le_conjugateSpanBy C (T : Subgroup G) hg) hgn

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape

