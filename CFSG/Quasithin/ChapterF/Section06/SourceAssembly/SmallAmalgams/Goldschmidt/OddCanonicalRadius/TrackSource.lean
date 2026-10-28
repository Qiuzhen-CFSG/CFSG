module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackCentralizer
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SourceIntervals

/-!
# Cubic track centralizers from the full source hypotheses

The first singular arc chooses one of the two vertex types. If it starts in
the second type, exchange the types of the literal coset graph and carry the
given track through that equivariant graph isomorphism. Its pointwise fixer
is unchanged, so the oriented centralizer theorem supplies the same cubic
element at the same track index in the original action.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.3),
printed p.395, as used for the new track in (6.11), printed p.402.
-/

@[expose] public section
open Subgroup SimpleGraph Theory.GroupAction.CubicTree Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private def swappedTrack (t : Track (RankTwo.graph F) G) :
    Track (RankTwo.graph (RankTwo.swapFamily F)) G where
  vertex i := RankTwo.swapVertex F (t.vertex i)
  injective := (RankTwo.swapVertexEquiv F).injective.comp t.injective
  adjacent i := (RankTwo.swapGraphIso F).map_rel_iff.mpr (t.adjacent i)
  translation := t.translation
  translate i := by
    rw [← RankTwo.swapVertex_smul, t.translate]

private theorem swappedTrack_fixer (t : Track (RankTwo.graph F) G) :
    (swappedTrack t).fixer = t.fixer := by
  ext g
  simp only [Track.mem_fixer]
  constructor
  · intro hg i
    apply (RankTwo.swapVertexEquiv F).injective
    change RankTwo.swapVertex F (g • t.vertex i) = RankTwo.swapVertex F (t.vertex i)
    simpa only [swappedTrack, RankTwo.swapVertex_smul] using hg i
  · intro hg i
    change g • RankTwo.swapVertex F (t.vertex i) = RankTwo.swapVertex F (t.vertex i)
    rw [← RankTwo.swapVertex_smul, hg i]

/-- Every track with nontrivial fixer in the original large source action
has an order-three centralizer of its entire fixer at one of its first two
vertices. The source singular arc need not have either prescribed type. -/
theorem LargeTreeSource.track_centralizer_exists_three (h : LargeTreeSource F s)
    (t : Track (RankTwo.graph F) G) (hQ : t.fixer ≠ ⊥) :
    ∃ (i : Fin 2) (q : G), orderOf q = 3 ∧
      q ∈ RankTwo.stabilizer F (t.vertex (i : ℤ)) ∧
      q ∈ centralizer (t.fixer : Set G) := by
  obtain ⟨v, p, hp, hn⟩ := h.singular
  cases hv : v.type with
  | false =>
    exact h.action.toCubicTreeAction.track_centralizer_exists_three h.five_le h.odd
      h.regular p hp hn hv t hQ
  | true =>
    obtain ⟨w, p', hw, hp', hn'⟩ := singular_swap p hv hp hn
    have hQ' : (swappedTrack t).fixer ≠ ⊥ := by rwa [swappedTrack_fixer]
    obtain ⟨i, q, hq, hfix, hcent⟩ :=
      h.swap.action.toCubicTreeAction.track_centralizer_exists_three h.five_le h.odd
        h.swap.regular p' hp' hn' hw (swappedTrack t) hQ'
    refine ⟨i, q, hq, ?_, ?_⟩
    · change q • t.vertex (i : ℤ) = t.vertex (i : ℤ)
      apply (RankTwo.swapVertexEquiv F).injective
      change RankTwo.swapVertex F (q • t.vertex (i : ℤ)) =
        RankTwo.swapVertex F (t.vertex (i : ℤ))
      change q • RankTwo.swapVertex F (t.vertex (i : ℤ)) =
        RankTwo.swapVertex F (t.vertex (i : ℤ)) at hfix
      simpa only [RankTwo.swapVertex_smul] using hfix
    · simpa only [swappedTrack_fixer] using hcent

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
