module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.LocalCores
public import Theory.SpecificGroups.LeechRelated.HSRecognition.RankThreeData

/-!
# Separating the local construction from permutation recognition

The source route first constructs a faithful degree-100 action with M₂₂
point stabilizer and subdegrees 1, 22, 77. A separate permutation-group
uniqueness theorem then identifies its image with the specified HS carrier.
Composition with the faithful range equivalence gives I.4.8.

Both substantial inputs remain explicit here. Their producers are
`qt-i48-hs-rank-three-construction` and `qt-i48-hs-rank-three-uniqueness`;
final discharge belongs to `qt-i48-hs-recognition`. Neither this conditional
reduction nor the local core calculations assert the source recognition.

Source: Aschbacher--Smith, I.4.8, printed p.418; Aschbacher, J. Algebra
260 (2003), 16--32; Wales, Pacific J. Math. 30 (1969), 271--276.
-/

public section
namespace CFSG.Quasithin.HigmanSims
open Sporadic.LeechRelated.HS
universe u

/-- The faithful action identifies the original group with its actual range;
permutation uniqueness supplies the second equivalence. -/
theorem recognition_of_rank_three
    (construct : ∀ (G : Type u) [Group G] [Finite G],
      IsType G → HasRankThreeAction G)
    (recognize : ∀ P : Subgroup (Equiv.Perm (Fin 100)),
      RankThreeData P → Nonempty (P ≃* Carrier)) : Recognition.{u} := by
  intro G _ _ hG
  obtain ⟨f, hf, hP⟩ := construct G hG
  obtain ⟨e⟩ := recognize f.range hP
  exact ⟨(MonoidHom.ofInjective hf).trans e⟩

end CFSG.Quasithin.HigmanSims
