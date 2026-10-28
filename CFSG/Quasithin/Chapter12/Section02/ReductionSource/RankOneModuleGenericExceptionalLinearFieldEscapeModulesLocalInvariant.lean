module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalInvariant
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalClosure

/-!
# A quadratic invariant subgroup in the surviving centralizer factor

The original elementary cubic closure N is normalized by all of L₂T.
Its nontrivial image F₀ on the centralizer span modulo ⟨z⟩ is quadratic
and normalized by the original Sylow image. The residual image centralizes
F₀, so the full H-image normalizes F₀ as well. All maps are the original
span-action projection, including when both opposite factors survive.

The ambient N is not normalized by H: the generated-core condition rules
that out. Minimality of H outside N_G(L) consequently places N_H(N) in
N_G(L). Invariance of F₀ alone does not lift to invariance of N, so this
does not yet prove the centralizer-span assertion of 5.1.23. Its exclusion
remains here; final source assembly remains qt-d-1222-linear-field-cubic-escape,
with earlier cubic local data at its existing producer. The strict-ratio
endpoint is already proved in EscapeModules.

Source: Aschbacher--Smith 3.1.3, G.2.3 and 5.1.23, and the end of 5.1.14,
printed pp.333--334,645--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The concrete surviving closure is quadratic and invariant under the
original H-image, while its ambient normalization by H remains impossible. -/
theorem linear_cubic_nonabelian_local_closure_quadratic
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
    let N := conjugateSpanBy (setup T H C z).U C
    let J := (H.subgroupOf S.H).map (SpanAction.projection s)
    let F₀ := (N.subgroupOf S.H).map (SpanAction.projection s)
    actor T C ⊔ (T : Subgroup G) ≤ normalizer (N : Set G) ∧
      IsElementaryTwo F₀ ∧ IsQuadratic (SpanAction.representation s) F₀ ∧
      J ≤ normalizer (F₀ : Set (SpanAction.Actor s)) ∧
      H ⊓ normalizer (N : Set G) ≤ normalizer (L : Set G) := by
  intro S s N J F₀
  obtain ⟨he,hNQ,hSN,hstrict,hnot,hmid,hF,hFE⟩ :=
    linear_cubic_nonabelian_local_closure_constraints
      D h hH hK hnf hlinear hpsl c d hn hne g hg hgn
  have hJN := d.local_cubic_span_join_normalized c D.sylow_normalizes_component hpsl
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) := le_sup_right.trans hJN
  let : IsElementaryAbelian 2 N := he
  have hHC : H ≤ S.H := by
    change H ≤ centralizer ({z} : Set G)
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  let : IsElementaryAbelian 2 (N.subgroupOf S.H) :=
    IsElementaryAbelian.subgroupOf
      ((hNQ.trans inf_le_right).trans ((pCoreIn_le 2 H).trans hHC))
  have hel : IsElementaryAbelian 2 F₀ := IsElementaryAbelian.map (SpanAction.projection s)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans d.g2.local_le
  let P := ((T : Subgroup G).subgroupOf S.H).map (SpanAction.projection s)
  let K := ((residual H).subgroupOf S.H).map (SpanAction.projection s)
  have hPN : P ≤ normalizer (F₀ : Set (SpanAction.Actor s)) :=
    (map_mono ((comap_mono hTN).trans (N.le_normalizer_comap S.H.subtype))).trans
      ((N.subgroupOf S.H).le_normalizer_map (SpanAction.projection s))
  have hKN : K ≤ normalizer (F₀ : Set (SpanAction.Actor s)) :=
    (le_centralizer_iff.mp (hFE.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hJ : J = K ⊔ P := by
    have hh := congrArg (fun Y : Subgroup G =>
      (Y.subgroupOf S.H).map (SpanAction.projection s)) (residual_sup_sylow T H hTH)
    rw [subgroupOf_sup ((map_subtype_le _).trans hHC) (hTH.trans hHC),Subgroup.map_sup] at hh
    exact hh.symm
  refine ⟨hJN,⟨hF,hel⟩,
    d.local_cubic_span_image_quadratic c D.sylow_normalizes_component hpsl s he,
    hJ ▸ sup_le hKN hPN,?_⟩
  apply Chapter3.HStar.proper_overgroup_le T hH (le_inf hTH hTN)
  apply lt_of_le_of_ne inf_le_left
  intro hh
  exact hnot (hh.ge.trans inf_le_right)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
