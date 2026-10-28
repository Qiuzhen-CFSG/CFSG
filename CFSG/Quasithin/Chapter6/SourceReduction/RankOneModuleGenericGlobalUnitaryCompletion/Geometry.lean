module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FourOrder

/-!
# Quadrangle geometry of the original unitary normalizer completion

The prepared comparison gives the strict unitary exponent. The native
five-path action, the exact whole overlap, and the full extension order
bound then force smallness and quadrangle geometry in the literal join
of the original normalizers. Their orders then force the join to be G. Ordinary and degree-two comparisons and both
orientations are retained. Hermitian identification is a further step.

Source: Aschbacher–Smith 5.3.1–4 and F.4.6,13,24, pp.658–659,276–280,287.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo SimpleGraph
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion

/-- The order bound gives a genuine generalized quadrangle on the original
normalizer completion, without an ambient generation premise. -/
theorem Preparation.unitary_completion_quadrangle
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
        (∀ v (p : (graph c.cosetFamily).Walk v v), p.IsCycle → 8 ≤ p.length) ∧
        (∀ v w, (graph c.cosetFamily).dist v w ≤ 4) ∧
        (∃ v, ∃ p : (graph c.cosetFamily).Walk v v, p.IsCycle ∧ p.length = 8) := by
  obtain ⟨hmgt, hn, c, hoverlap, hcard, _⟩ :=
    d.unitary_completion_input h hH hp m hm hc E he horder
  exact ⟨hmgt, hn, c, hoverlap,
    four_completion_quadrangle m hm hmgt E c hoverlap hcard⟩

/-- The full original normalizers generate G, and its order equals that of
the realized extension, once the source producer supplies the genuine bound. -/
theorem Preparation.unitary_normalizers_generate_and_card
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
    1 < m ∧ n = 2*m ∧ NormalizerJoin L (residual H) = ⊤ ∧
      Nat.card G = Nat.card E.carrier := by
  obtain ⟨hmgt, hn, c, hoverlap, hcard, _⟩ :=
    d.unitary_completion_input h hH hp m hm hc E he horder
  have heq := four_completion_card_eq m hm hmgt E c hoverlap hcard
  refine ⟨hmgt,hn,normalizerJoin_eq_top_of_card L (residual H) E horder heq,?_⟩
  apply Nat.le_antisymm horder
  rw [← heq]
  exact Nat.card_le_card_of_injective (NormalizerJoin L (residual H)).subtype
    (NormalizerJoin L (residual H)).subtype_injective

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
