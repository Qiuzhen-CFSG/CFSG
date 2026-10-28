module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Statements
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Cartan
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Escape

/-!
# The actual H-star Hall witness for 11.2.1

The original chosen module gives the Fundamental Setup with unchanged seed
and M=N_G(L). The proved E.2.2 construction therefore supplies a full odd Hall
subgroup of H intersect M, together with its cyclic subgroup and Sylow
permutation. The numerical statement is n(H) ≤ f at the marked exponent f;
no equality through a two-core quotient is used.

Source: Aschbacher--Smith, E.2.2 and 11.2.1, pp.215--216,766--767.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterB
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The original FSU maximal local is exactly N_G(L). -/
theorem maximalLocal_eq :
    (D.fundamentalSetup S.source.toHypothesis1221).maximalLocal =
      normalizer (L : Set G) := by
  change normalizer (Chapter3.Section02.localOrbit T L : Set G) = _
  rw [D.localOrbit_eq]

/-- Construct the intrinsic minimal parabolic and the complete Hall witness. -/
theorem hall_data {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H) :
    ∃ (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) (f : ℕ),
      IsEGenerated f H ∧ generationParameter H ≤ f ∧
      ∃ d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f,
        minimalParabolicMax (T.subtype hH.1.1.2) hP =
          (normalizer (L : Set G)).subgroupOf H ∧
        (d.witness.abelianGroup.map H.subtype : Set G) * (T : Set G) =
          (T : Set G) * (d.witness.abelianGroup.map H.subtype : Set G) := by
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G)
      (D.fundamentalSetup S.source.toHypothesis1221).maximalLocal :=
    (maximalLocal_eq D S).symm ▸ hH
  obtain ⟨hP,f,hg,hb,d,hm,hperm,_⟩ :=
    Chapter10.source_hstar_cartan_data_of_generation_gt_one
      (D.fundamentalSetup S.source.toHypothesis1221) hH' hlarge
  refine ⟨hP,f,hg,hb,d,?_,hperm⟩
  simpa only [maximalLocal_eq D S] using hm

/-- Every elementary subgroup of the specified Hall actor has the original
4.4.13 escape property, with the ambient embedding H → G unchanged. -/
theorem elementary_hall_escape {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    {p : ℕ} (hp : p.Prime) (A : Subgroup H) (he : IsElementaryAbelian p A)
    (hA : A ≤ d.witness.abelianGroup)
    (hperm : (A.map H.subtype : Set G) * (T : Set G) =
      (T : Set G) * (A.map H.subtype : Set G)) :
    ¬ normalizer (A.map H.subtype : Set G) ≤ normalizer (L : Set G) := by
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G)
      (D.fundamentalSetup S.source.toHypothesis1221).maximalLocal :=
    (maximalLocal_eq D S).symm ▸ hH
  simpa only [maximalLocal_eq D S] using
    Chapter10.source_hstar_elementary_hall_escape
      (D.fundamentalSetup S.source.toHypothesis1221) hH' hlarge hP d hp A he hA hperm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
