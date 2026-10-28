module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.Source
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuComplete

/-!
# The actual overcomponent obstructing the linear-shadow argument

Start with a counterexample to 11.3.2 on the original chosen module and flag.
The paired-component exclusion makes the selected source component normal in
H, identifying it with the literal embedded O²(H). The rank-one branch already
implies the full shadow conclusion and is therefore impossible. The remaining
source catalogue constructs a faithful maximal overcomponent J containing this
same residual, with its genuine chosen module and 12.2.3 hypotheses.

The complete parameter, common-core and compatible-field argument shows that
normalized 7.0.1 must fail for that selected chosen orbit. Thus the orbit is
non-FF. Source 3.2.5 either supplies its actual marked doubled configuration or
identifies the seed with the orbit. In the latter case the genuine Chapter K
hypotheses and the completed non-Mathieu theorem leave the Mathieu alternative.
Every containing subgroup, action and residual map remains the original one.

The last theorem applies the two independent source exits only to maximal
overcomponents containing O²(H), rather than requiring normalized 7.0.1 on
all chosen modules in G. The doubled and Mathieu inputs still belong to
qt-d-1222-nonff-doubled and qt-d-1222-nonff-mathieu. Odd-kernel control still
belongs to qt-d-1222-natural-odd-kernel-normalizer. These inputs are not
preceding geometry hidden in Preceding1132. Their final discharge remains
with qt-d-1222-shadow-linear-geometry and qt-d-1222-natural-shadow-reduction;
this is not Proposition 11.3.2 with only preceding-source inputs.

Source: Aschbacher--Smith, refs/quasithin.pdf, 3.2.5, 7.0.1 and 11.3.4--9,
printed pp.580--581,695--696,771--775. The imported common-core construction
retains the q=4 cover obstruction, odd degree and the sections V₂ and P/V₂.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
open ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- A remaining counterexample selects an actual faithful maximal overcomponent
of the original residual at which normalized 7.0.1 fails. -/
theorem exists_overcomponent_source_failure_of_counterexample
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (hc : ¬ Proposition1132At D S (c.binarySubspace (f.space 0)) H) :
    Source.NormalComponentIn H (residual H) ∧
      ∃ J W : Subgroup G, ∃ E : ChosenModule T J W,
        ComponentSeed T H (residual H) ∧ residual H ≤ J ∧
        J ∈ Chapter1.LStar G (T : Subgroup G) ∧
        J ∈ MainForward.faithfulLocalComponents T ∧
        ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ ∧
        Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
        ¬ Chapter7.NormalizedSource.Alternatives G E.orbitRepresentation E.orbitComponent := by
  have hs := (source_marking_and_parameter s p.preceding hc c p.global_s p.generation).2.1
  obtain ⟨K,J,d,hKJ,hJ,hfaith,hout,hmove,hcases⟩ :=
    exists_componentSeed_with_quasisimple_higher_rank_source s p.preceding hc hs.symm.le
  have hn := d.normal_of_source_odd_kernel s p.preceding hc f rfl p.global_s
    hcontrol p.prime_residual p.cubic
  have he := d.normal_iff_eq_residual.mp hn
  have hsrc : Hypothesis1223 KnownSimple.IsKnownSimple T J := by
    rcases hcases with ⟨hlow,_⟩ | ⟨_,_,_,hsrc,_⟩
    · rcases hlow with ⟨a,ha,_,hm⟩ | ⟨hsrc,_⟩
      · exact (hc (proposition1132_of_parameter_component c f hu s p
          (d.conclusion_of_linear_odd_kernel s p.preceding hc f rfl p.global_s
            hcontrol ha hm p.prime_residual p.cubic).2.2)).elim
      · exact hsrc
    · exact hsrc
  obtain ⟨W,⟨E⟩⟩ := d.exists_chosen_overcomponent_of_normal s hn hJ.1 hKJ
  have hfail : ¬ Chapter7.NormalizedSource.Alternatives G E.orbitRepresentation E.orbitComponent := by
    intro hexit
    exact hc (proposition1132_of_parameter_component c f hu s p
      (d.conclusion_of_overcomponent_source_exit s p.preceding hc f rfl p.global_s
        hcontrol hJ hKJ E hsrc hexit p.prime_residual p.cubic).2)
  subst K
  exact ⟨⟨d.component,hn⟩,J,W,E,d,hKJ,hJ,hfaith,hout,hmove,hsrc,hfail⟩

/-- Remaining literal source alternatives on a selected chosen orbit. This is
an output specification; it supplies no source theorem or classification. -/
@[expose] def SelectedNonFFObstruction {J W : Subgroup G} (E : ChosenModule T J W) : Prop :=
  ¬ IsFFModule E.sourceOrbitNormalizerRepresentation ∧
    (E.MarkedDoubled ∨
      (W = E.sourceOrbit ∧
        ChapterK.RankOne.SourceHypotheses E.orbitRepresentation E.orbitComponent ∧
        Chapter7.NormalizedSource.HasMathieuCentralQuotient E.orbitComponent))

private theorem selectedNonFFObstruction_of_failure {J W : Subgroup G}
    (E : ChosenModule T J W)
    (hsrc : Hypothesis1223 KnownSimple.IsKnownSimple T J)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfail : ¬ Chapter7.NormalizedSource.Alternatives G E.orbitRepresentation E.orbitComponent) :
    SelectedNonFFObstruction E := by
  classical
  have hnon : ¬ IsFFModule E.sourceOrbitNormalizerRepresentation :=
    fun hff => hfail (.inl hff)
  refine ⟨hnon,?_⟩
  by_cases hd : E.MarkedDoubled
  · exact .inl hd
  have hW : W = E.sourceOrbit := by
    rcases E.source325_of_many hsrc hmany with ⟨hW,_⟩ | ⟨hW,_,_⟩ | hd'
    · exact hW.symm.trans E.sourceOrbit_eq.symm
    · exact hW.symm.trans E.sourceOrbit_eq.symm
    · exact (hd hd').elim
  have hK := E.sourceOrbit_chapterK_of_many hsrc hmany hnon hW
  have hmathieu : Chapter7.NormalizedSource.HasMathieuCentralQuotient E.orbitComponent := by
    by_contra hnm
    exact hfail (.inr (.inl
      (E.sourceOrbit_orthogonal_of_nonMathieu_of_many hsrc hmany hW hK hnm hnon)))
  exact .inr ⟨hW,hK,hmathieu⟩

/-- The selected obstruction is a literal doubled orbit or the unchanged
Mathieu orbit with its genuine Chapter K hypotheses. -/
theorem exists_selected_nonff_obstruction_of_counterexample
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (hc : ¬ Proposition1132At D S (c.binarySubspace (f.space 0)) H) :
    Source.NormalComponentIn H (residual H) ∧
      ∃ J W : Subgroup G, ∃ E : ChosenModule T J W,
        ComponentSeed T H (residual H) ∧ residual H ≤ J ∧
        J ∈ Chapter1.LStar G (T : Subgroup G) ∧
        J ∈ MainForward.faithfulLocalComponents T ∧
        ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ ∧
        Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
        SelectedNonFFObstruction E := by
  obtain ⟨hn,J,W,E,d,hKJ,hJ,hfaith,hout,hmove,hsrc,hfail⟩ :=
    exists_overcomponent_source_failure_of_counterexample (D := D) (S := S) c f hu s p hcontrol hc
  exact ⟨hn,J,W,E,d,hKJ,hJ,hfaith,hout,hmove,hsrc,
    selectedNonFFObstruction_of_failure E hsrc S.many hfail⟩

/-- Original four-clause application of the two selected non-FF exclusions.
Only maximal overcomponents containing the actual O²(H) are tested. -/
theorem proposition1132_of_selected_source_exits
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (hdoubled : ∀ (J W : Subgroup G) (E : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      residual H ≤ J → J ∈ Chapter1.LStar G (T : Subgroup G) →
      E.MarkedDoubled → ¬ IsFFModule E.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : ∀ (J W : Subgroup G) (E : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      residual H ≤ J → J ∈ Chapter1.LStar G (T : Subgroup G) →
      W = E.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses E.orbitRepresentation E.orbitComponent →
      Chapter7.NormalizedSource.HasMathieuCentralQuotient E.orbitComponent →
      ¬ IsFFModule E.sourceOrbitNormalizerRepresentation → Nonempty (G ≃* Janko4.Model)) :
    Proposition1132At D S (c.binarySubspace (f.space 0)) H := by
  classical
  by_contra hc
  obtain ⟨_,hd⟩ :=
    exists_selected_nonff_obstruction_of_counterexample (D := D) (S := S) c f hu s p hcontrol hc
  obtain ⟨J,hd⟩ := hd
  obtain ⟨W,hd⟩ := hd
  obtain ⟨E,hd⟩ := hd
  obtain ⟨_,hKJ,hJ,_,_,_,hsrc,hobs⟩ := hd
  obtain ⟨hnon,hcases⟩ := hobs
  rcases hcases with hd | ⟨hW,hK,hm⟩
  · exact hdoubled J W E hsrc hKJ hJ hd hnon
  · exact S.source.no_J4 (hmathieu J W E hsrc hKJ hJ hW hK hm hnon)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
