module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalClosure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalPair

/-!
# A specific surviving subgroup from the original cubic closure

Under the contrary nonabelian-span hypothesis, the proved elementary cubic
closure N of the H-span lies in O₂(H) and the opposite core S. It is
normalized by S, C and the right Cartan B. The generated-core condition
forces strict enlargement of the H-span and rules out normalization of N
by H. The exact opposite kernel also forces a nontrivial image of N in
the residual-centralizer factor of the original span action.

This retains configurations where both opposite factors survive and gives
a specific subgroup whose exclusion remains necessary. It does not prove
full centralizer-span abelianness; the strict-ratio endpoint remains proved
in EscapeModules. Final source assembly remains with
qt-d-1222-linear-field-cubic-escape, and the earlier cubic local-data choice
retains its existing producer.

Source: Aschbacher--Smith G.2.3 and 5.1.23, and the end of 5.1.14,
printed pp.333--334,645--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The original cubic closure is a strict elementary enlargement inside O₂(H),
normalized by the opposite core, cubic and right Cartan, but not by H. Its actual
image is a nontrivial subgroup of the surviving centralizer factor. -/
theorem linear_cubic_nonabelian_local_closure_constraints
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
    let U₀ := (setup T H C z).U
    let N := conjugateSpanBy U₀ C
    let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
    let K := ((residual H).subgroupOf S.H).map (SpanAction.projection s)
    let F₀ := (N.subgroupOf S.H).map (SpanAction.projection s)
    IsElementaryAbelian 2 N ∧ N ≤ S.S g ⊓ H.pCoreIn 2 ∧
      S.S g ⊔ C ⊔ B ≤ normalizer (N : Set G) ∧
      U₀ < N ∧ ¬ H ≤ normalizer (N : Set G) ∧
      ¬ U₀ ≤ S.S₂ g ∧ F₀ ≠ ⊥ ∧
      F₀ ≤ E ⊓ centralizer (K : Set (SpanAction.Actor s)) := by
  intro S s U₀ N E K F₀
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  have hle : U₀ ≤ S.W g :=
    linear_cubic_nonabelian_local_span_le_W D h hH hK hnf hlinear hpsl c d hn hne g hg hgn
  obtain ⟨he,hNQ⟩ :=
    linear_cubic_nonabelian_local_cubic_span D h hH hK hnf hlinear hpsl c d hn hne
  obtain ⟨hNS,hNorm⟩ := d.local_cubic_span_normalizers c s b g hg hgn hle
  obtain ⟨hstrict,hescape⟩ := d.local_cubic_span_escape he (hNQ.trans (pCoreIn_le 2 H))
  have hmid := d.local_span_not_le_middle s b g hg hgn
  have hmove := d.moving_local_span_image_ne_bot s b g hg hgn hle
  have hconj : conjugate U₀ g ≤ N := by
    rintro _ ⟨u,hu,rfl⟩
    exact subset_closure ⟨g⁻¹,C.inv_mem hg,u,hu,by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hF : F₀ ≠ ⊥ := by
    intro hz
    apply hmove
    exact bot_unique ((map_mono (comap_mono hconj)).trans hz.le)
  obtain ⟨_,_,hE,_,_,_⟩ :=
    linear_cubic_nonabelian_opposite_involutions D h hpsl c d hn hne g hg hgn
  have hFE : F₀ ≤ E := by
    change E = ((S.S g).subgroupOf S.H).map (SpanAction.projection s) at hE
    rw [hE]
    exact map_mono (comap_mono hNS)
  obtain ⟨hFQ,_,_⟩ :=
    linear_cubic_nonabelian_opposite_local_core D h hH hK hnf hlinear hpsl c d hn hne g hg hgn
  change E ⊓ centralizer (K : Set (SpanAction.Actor s)) =
    E ⊓ ((H.pCoreIn 2).subgroupOf S.H).map (SpanAction.projection s) at hFQ
  refine ⟨he,le_inf hNS hNQ,hNorm,hstrict,hescape,hmid,hF,?_⟩
  rw [hFQ]
  exact le_inf hFE (map_mono (comap_mono hNQ))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
