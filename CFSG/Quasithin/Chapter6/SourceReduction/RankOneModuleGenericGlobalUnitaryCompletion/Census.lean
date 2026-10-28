module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Census

/-!
# Numerical obstruction to large original unitary completions

For the literal original normalizer pair, the prepared ordinary or degree-two
comparison supplies m > 1 and n = 2m. The compatible DGS extension and ambient
order bound then give the native valencies, numerical coset bounds, and two
distinct nonbacktracking four-walks with equal endpoints in the normalizer join.
This proves the counting part of F.4.24 on the actual consumer. Geodesicity,
smallness, Hermitian recognition and GlobalExit remain to be established.

Source: Aschbacher–Smith 5.3.1–4 and F.4.24, printed pp.658–659 and287.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo SimpleGraph
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion

/-- The source order bound has an actual four-walk collision in the join of
its full normalizers, with the genuine unitary exponent and local marking. -/
theorem Preparation.unitary_completion_four_path_collision
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (E : FourExtension m hm) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    1 < m ∧ n = 2*m ∧
      ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
          (G := NormalizerJoin L (residual H)),
        c.left.range ⊓ c.right.range = c.middle.range ∧
        (∀ i : Bool, Nat.card (NormalizerJoin L (residual H) ⧸ c.cosetFamily i) ≤
          fourCosetCount m i) ∧
        (∀ v : Vertex c.cosetFamily,
          Nat.card ((graph c.cosetFamily).neighborSet v) = fourDegree m v.type) ∧
        ∃ p q : BasedWalk (graph c.cosetFamily) 4 (base c.cosetFamily false),
          p.Nonbacktracking ∧ q.Nonbacktracking ∧ p.endpoint = q.endpoint ∧ p ≠ q := by
  obtain ⟨hmgt, hn, c, hoverlap, hcard, _⟩ :=
    d.unitary_completion_input h hH hp m hm hc E he horder
  exact ⟨hmgt, hn, c, hoverlap, four_completion_card_coset_le m hm E c hcard,
    four_completion_card_neighbors m hm E c hoverlap,
    four_completion_four_path_collision m hm hmgt E c hoverlap hcard⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
