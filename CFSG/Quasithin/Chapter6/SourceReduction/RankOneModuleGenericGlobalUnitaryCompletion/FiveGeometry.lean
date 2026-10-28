module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.Inner
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveOrder

/-!
# The original PSU₅(4) normalizer quadrangle and ambient native completion

The literal original normalizers, marked by a genuine full extension,
have the 65/17 generalized quadrangle. The exact full-extension order
forces their join to be G. Simplicity then makes their native endpoint
images generate G as well. The prepared comparison retains n = 4 in
either orientation; this local exponent is distinct from the eventual
PSU₅(4) GlobalExit exponent two. No Hermitian group identification is
asserted here.

Source: Aschbacher–Smith 5.3.1–4 and F.4.6,13,17,24,
`refs/quasithin.pdf`, pp.658–659,276–283,287.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo SimpleGraph
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion

/-- The order bound gives a genuine generalized quadrangle on the original
normalizer completion, without an ambient generation premise. -/
theorem Preparation.unitaryFive_completion_quadrangle
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
    n = 4 ∧
      ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
          (G := NormalizerJoin L (residual H)),
        c.left.range ⊓ c.right.range = c.middle.range ∧
        (∀ v (p : (graph c.cosetFamily).Walk v v), p.IsCycle → 8 ≤ p.length) ∧
        (∀ v w, (graph c.cosetFamily).dist v w ≤ 4) ∧
        (∃ v, ∃ p : (graph c.cosetFamily).Walk v v, p.IsCycle ∧ p.length = 8) := by
  have hn : n = 4 := by
    rcases hc with hc | hc
    · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U hc).elim
    · exact (d.unitaryFive_local_structure h hH.1.1.2 hp U hc.some).1
  obtain ⟨c,ho,hcard⟩ := five_normalizer_completion L H U E he horder
  exact ⟨hn,c,ho,five_completion_quadrangle U E c ho hcard⟩

/-- The full original normalizers generate G, and its order equals that of
the realized extension, once the source producer supplies the genuine bound. -/
theorem Preparation.unitaryFive_normalizers_generate_and_card
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
    n = 4 ∧ NormalizerJoin L (residual H) = ⊤ ∧
      Nat.card G = Nat.card E.carrier := by
  have hn : n = 4 := by
    rcases hc with hc | hc
    · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U hc).elim
    · exact (d.unitaryFive_local_structure h hH.1.1.2 hp U hc.some).1
  obtain ⟨c,ho,hcard⟩ := five_normalizer_completion L H U E he horder
  have heq := five_completion_card_eq U E c ho hcard
  refine ⟨hn,normalizerJoin_eq_top_of_card L (residual H) E horder heq,?_⟩
  apply Nat.le_antisymm horder
  rw [← heq]
  exact Nat.card_le_card_of_injective (NormalizerJoin L (residual H)).subtype
    (NormalizerJoin L (residual H)).subtype_injective

/-- The native PSU₅(4) projective endpoint maps generate the original simple G.
This is an actual native amalgam completion, not yet its recognition. -/
theorem Preparation.unitaryFive_native_ambient_completion
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
    n = 4 ∧ ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := G),
      c.left.range ⊓ c.right.range = c.middle.range ∧ E.innerGenerated c = ⊤ ∧
      ∃ b : RankTwoAmalgam.FaithfulCompletion
          (SourceExtension.nativeAmalgam
            (P₀ := U.leftParabolic)
            (P₁ := U.rightParabolic)) (G := G),
        b.left = E.innerLeft c ∧ b.right = E.innerRight c ∧
        b.left.range ⊓ b.right.range = b.middle.range := by
  have hn : n = 4 := by
    rcases hc with hc | hc
    · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U hc).elim
    · exact (d.unitaryFive_local_structure h hH.1.1.2 hp U hc.some).1
  obtain ⟨c,ho,hcard⟩ := five_normalizer_completion L H U E he horder
  have ht := normalizerJoin_eq_top_of_card L (residual H) E horder
    (five_completion_card_eq U E c ho hcard)
  let cG := ambientCompletion E c ht
  have hoG := ambientCompletion_overlap E c ht ho
  let : IsSimpleGroup G := h.qtke.simple
  let : Nontrivial U.leftParabolic := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    have hh := Theory.SpecificGroups.UnitaryFive.card_lineParabolic_four U.form U.card U.conjugation U.matrix
    change 1 < Nat.card (Theory.SpecificGroups.UnitaryFive.lineParabolic U.form)
    rw [hh]
    decide
  have hN := E.innerGenerated_eq_top_of_simple cG (five_conj_injective U)
  exact ⟨hn,cG,hoG,hN,E.nativeCompletionOfTop cG (five_conj_injective U) hN,
    rfl,rfl,E.nativeCompletionOfTop_overlap cG (five_conj_injective U) hN hoG⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
