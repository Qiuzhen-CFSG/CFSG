module
public import Theory.GroupTheory.GeneralizedFitting.CenterlessSylowJoin
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesResidualDisplacement

/-!
# The surviving opposite factor and the original local core

Inside the original H-image, the centralizer of the PSL₃(4) residual
is exactly the image of O₂(H). Thus the surviving opposite-image factor
is its intersection with that image and fixes the original H-span modulo
⟨z⟩. Its proved nontriviality forces O₂(H) outside O₂(C_G(z)) and forces
the H-span to be strictly smaller than the centralizer span.

Consequently normalization of O₂(H) by C_G(z) suffices for the original
abelian-span conclusion. This condition is explicit and is not asserted
as a source consequence. The unconditional ambient exclusion, including
configurations with both opposite factors, remains open. The original
strict quadratic-ratio endpoint remains proved in EscapeModules.

Source: Aschbacher--Smith 5.1.23, printed pp.645--646, refs/quasithin.pdf.
Final source assembly remains qt-d-1222-linear-field-cubic-escape; existence
of the earlier local cubic data retains its separate producer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- Inside the original H-image, the residual centralizer is exactly the local core image. -/
theorem linear_cubic_local_core_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z) :
    let s := linear_cubic_centralizer_setup h d
    let J := (H.subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    J ⊓ centralizer (K : Set (SpanAction.Actor s)) =
      ((H.pCoreIn 2).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s) := by
  intro s J K
  let P := ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
  have hHC : H ≤ centralizer ({z} : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans d.g2.local_le
  let π : centralizer ({z} : Set G) →* SpanAction.Actor s := SpanAction.projection s
  have hJP : J = K ⊔ P := by
    have hKC : residual H ≤ centralizer ({z} : Set G) := (map_subtype_le _).trans hHC
    have hh := congrArg (fun Y : Subgroup G =>
      (Y.subgroupOf (centralizer ({z} : Set G))).map π)
      (residual_sup_sylow T H hTH)
    rw [subgroupOf_sup hKC (hTH.trans hHC),Subgroup.map_sup] at hh
    exact hh.symm
  obtain ⟨hN,hm⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let : K.Normal := hN
  obtain ⟨hq,hz,_⟩ := ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm
  let : IsQuasisimple K := hq
  rw [hJP,centralizer_inf_sup_eq_twoCore K P hz
    (T.isPGroup'.comap_subtype.map (SpanAction.projection s)),← hJP]
  exact (d.local_core_image s).symm

/-- Both opposite factors retain their original lifts; the centralizer factor
is exactly the part of the opposite image coming from O₂(H). -/
theorem linear_cubic_nonabelian_opposite_local_core
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
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    let s := linear_cubic_centralizer_setup h d
    let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
    let K := ((residual H).subgroupOf S.H).map (SpanAction.projection s)
    let Q := ((H.pCoreIn 2).subgroupOf S.H).map (SpanAction.projection s)
    E ⊓ centralizer (K : Set (SpanAction.Actor s)) = E ⊓ Q ∧ E ⊓ Q ≠ ⊥ ∧
      (SpanAction.conjugationSection s).imageSpace (setup T H C z).U ≤
        fixedSpace (SpanAction.representation s) (E ⊓ Q) := by
  intro S s E K Q
  let J := (H.subgroupOf S.H).map (SpanAction.projection s)
  obtain ⟨_,_,_,hEP,_,_⟩ :=
    linear_cubic_nonabelian_opposite_involutions D h hpsl c d hn hne g hg hgn
  have hEJ : E ≤ J := hEP.trans (map_mono (comap_mono
    (show (T : Subgroup G) ≤ H from le_sup_right.trans d.g2.local_le)))
  have he : E ⊓ centralizer (K : Set (SpanAction.Actor s)) = E ⊓ Q := by
    have hc : J ⊓ centralizer (K : Set (SpanAction.Actor s)) = Q :=
      linear_cubic_local_core_centralizer h hH hK hnf hlinear d
    rw [← hc,← inf_assoc,inf_eq_left.mpr hEJ]
  exact ⟨he,he ▸ linear_cubic_nonabelian_opposite_centralizer_ne_bot
    D h hH hK hnf hlinear hpsl c d hn hne g hg hgn,
    (d.local_core_image_fixes_local_span s).trans
      (fixedSpace_antitone (SpanAction.representation s) inf_le_right)⟩


/-- The contrary source span requires a local two-core escaping the larger
point-centralizer two-core, and a strictly larger span in that centralizer. -/
theorem linear_cubic_nonabelian_local_core_escape
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
    ¬ H.pCoreIn 2 ≤ (centralizer ({z} : Set G)).pCoreIn 2 ∧
      ¬ centralizer ({z} : Set G) ≤ normalizer (H.pCoreIn 2 : Set G) ∧
      conjugateSpanBy (CubicEscape.plane C z) H <
        conjugateSpanBy (CubicEscape.plane C z) (centralizer ({z} : Set G)) := by
  let s := linear_cubic_centralizer_setup h d
  let Q := ((H.pCoreIn 2).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
  obtain ⟨g,hg,hgn⟩ := d.exists_moving_cubic
  obtain ⟨_,hneQ,_⟩ := linear_cubic_nonabelian_opposite_local_core
    D h hH hK hnf hlinear hpsl c d hn hne g hg hgn
  have hQne : Q ≠ ⊥ := by
    intro he
    exact hneQ (bot_unique (inf_le_right.trans he.le))
  have hescape : ¬ H.pCoreIn 2 ≤ (centralizer ({z} : Set G)).pCoreIn 2 := by
    intro hle
    apply hQne
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    apply SpanAction.core_le_projection_kernel s
    obtain ⟨q,hq,hqe⟩ := hle hx
    exact (show q = x from Subtype.ext hqe) ▸ hq
  have hHC : H ≤ centralizer ({z} : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  refine ⟨hescape,?_,?_⟩
  · intro hnorm
    exact hescape (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
      ((pCoreIn_le 2 H).trans hHC) hnorm)
  · apply lt_of_le_of_ne (conjugateSpanBy_mono le_rfl hHC)
    intro he
    exact hQne (d.local_core_image_eq_bot_of_span_eq s he)

/-- A sufficient ambient normalization condition now completes the original
abelian-span conclusion, with no additional module or ratio premise. Its
normalization hypothesis remains to be supplied in unconditional assembly. -/
theorem linear_cubic_abelian_span_of_local_core_normalized
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z) (hn : 1 < n)
    (hnorm : centralizer ({z} : Set G) ≤ normalizer (H.pCoreIn 2 : Set G)) :
    IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))) := by
  by_contra hne
  exact (linear_cubic_nonabelian_local_core_escape
    D h hH hK hnf hlinear hpsl c d hn hne).2.1 hnorm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
