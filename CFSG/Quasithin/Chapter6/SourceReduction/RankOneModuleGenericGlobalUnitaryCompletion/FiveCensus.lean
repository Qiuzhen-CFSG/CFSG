module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryFive
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveCensus

/-!
# The fixed unitary-five census on the original normalizer pair

The actual prepared comparison, accepted in either orientation, forces
n = 4 by the already proved local-factor theorem. A compatible full DGS
extension and the ambient order bound then give the native 65/17 degrees,
17425/66625 coset bounds and a collision of nonbacktracking four-walks in
the literal join of N_G(L) and N_G(residual H), from either root type.
The original whole overlap and both maps are retained. No generation of G,
geodesicity or unitary recognition is assumed or concluded here.

Source: Aschbacher–Smith 5.2.6–7,5.3.1–4 and F.4.24,
printed pp.650–651,658–659 and287. The eventual PSU₅(4) GlobalExit uses
exponent two, distinct from this local binary PSL₂ exponent n = 4.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo SimpleGraph
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion

namespace UnitaryCompletion
/-- Both markings of the original fixed-parameter PSU₅(4) comparison. -/
@[expose] def FiveLocalComparison {G : Type*} [Group G] (L R S : Subgroup G)
    (U : ChapterF.GreenBook.UnitaryFive.Model 4) : Prop :=
  Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] S) U.amalgam) ∨
    Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] S) U.amalgam.reverse)
end UnitaryCompletion

/-- The prepared fixed model determines n = 4. The full original normalizer
completion has the 65/17 census and a four-walk collision at either root. -/
theorem Preparation.unitaryFive_completion_census
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : FiveLocalComparison L (residual H) (sourceS L H) U)
    (E : FiveExtension U) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    n = 4 ∧ ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
        (G := NormalizerJoin L (residual H)),
      c.left.range ⊓ c.right.range = c.middle.range ∧
      (∀ i : Bool, Nat.card (NormalizerJoin L (residual H) ⧸ c.cosetFamily i) ≤ fiveCosetCount i) ∧
      (∀ v : Vertex c.cosetFamily,
        Nat.card ((graph c.cosetFamily).neighborSet v) = fiveDegree v.type) ∧
      ∀ i : Bool, ∃ p q : BasedWalk (graph c.cosetFamily) 4 (base c.cosetFamily i),
        p.Nonbacktracking ∧ q.Nonbacktracking ∧ p.endpoint = q.endpoint ∧ p ≠ q := by
  have hn : n = 4 := by
    rcases hc with hc | hc
    · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U hc).elim
    · exact (d.unitaryFive_local_structure h hH.1.1.2 hp U hc.some).1
  obtain ⟨c,ho,hcard⟩ := five_normalizer_completion L H U E he horder
  exact ⟨hn,c,ho,five_completion_card_coset_le U E c hcard,
    five_completion_card_neighbors U E c ho,five_completion_four_path_collision U E c ho hcard⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
