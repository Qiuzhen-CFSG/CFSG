module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry

/-!
# Earlier source inputs for the cover assembly

The uniform inputs are the actual earlier rank-two local conclusions. In
particular the matrix setup contains no centre, centralizer, marked cover or
transfer conclusion. The local-cover constructor discharges those conclusions.
Source: Aschbacher--Smith, proof of 15.3.38, printed pp.1135--1137.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel Candidates.LinearCore
variable {G : Type*} [Group G] [Finite G]

/-- Earlier conclusions, with their outside-family eligibility retained. -/
structure SourceInputs (d : CharacteristicTwo.LocalData G) : Prop where
  earlier : Earlier d
  setup : ∀ I L, Setup d I L → MatrixImage.SourceSetup d I L
  alternatives : ∀ J ∈ d.Hplus, ∀ K : Subgroup G,
    K ≤ J → IsComponent J (K.subgroupOf J) →
    d.Yplus ≤ localSpan K d.S ∨
      3 ^ (Nat.card (centralizingPart d.Yplus K)).factorization 3 = 3 ∨
      Candidates.RankTwoDiagonal d.Yplus K (localSpan K d.S)
  second_choice : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
    d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
    normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M
  residual_alternatives : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
    ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action
  residual_image : d.action.image d.Y =
    Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)
  central_omega : centralOmegaIn d.S ≤ d.V
  fixed_vectors : d.V ⊓ centralizer (d.Y : Set G) = ⊥

/-- Output of the first source paragraph, retaining the selected marking. -/
structure LocalResult (d : CharacteristicTwo.LocalData G) (I L : Subgroup G) where
  marking : ProjectiveMarking L 4
  actor : d.Yplus
  diagonal : marking.Diagonal (actor : G)
  cover : PrecentreData d I L (n := 2) marking actor
  product : (I : Set G) = (L : Set G) *
    (planeResidual d.M d.Y cover.borel.W₂ : Set G) * (d.S : Set G)

/-- Select the diagonal alternative and derive n=2 and the full local cover. -/
theorem local_result {d : CharacteristicTwo.LocalData G} (s : SourceInputs d)
    {I L : Subgroup G} (h : Setup d I L) : Nonempty (LocalResult d I L) := by
  obtain ⟨c, y, g, hy, hp⟩ := local_cover_of_rank_two (s.setup I L h) s.earlier h.not_le
    s.alternatives s.second_choice s.residual_alternatives s.residual_image
    s.central_omega s.fixed_vectors
  exact ⟨⟨c, y, hy, g, hp⟩⟩

omit [Finite G] in
/-- Each chosen centre plane is one of the original natural planes. -/
theorem LocalResult.plane {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (r : LocalResult d I L) : ∃ i : OrthogonalPlaneIndex, r.cover.borel.W₁ = d.action.plane i := by
  rcases r.cover.borel.planes with ⟨h₁, _⟩ | ⟨h₁, _⟩
  · exact ⟨1, h₁⟩
  · exact ⟨Multiplicative.ofAdd (1 : ZMod 2), h₁⟩

omit [Finite G] in
/-- The actual marked cover has the same order on every eligible overgroup. -/
theorem LocalResult.card {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (r : LocalResult d I L) : Nat.card L = 80640 := by
  obtain ⟨i, hi⟩ := r.plane
  have hc : Nat.card (center L) = 4 := by
    rw [← card_map_of_injective L.subtype_injective]
    change Nat.card (centerImage L) = 4
    rw [r.cover.center_plane, hi, d.action.card_plane]
  exact GlobalGeometry.CoverEmbeddingRigidity.card_marked_cover L r.cover.center_core hc r.marking

omit [Finite G] in
/-- The residual acts nontrivially on the selected central plane. -/
theorem LocalResult.noncentral {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (r : LocalResult d I L) :
    ¬ d.Yplus ≤ centralizer (r.cover.borel.W₁ : Set G) := by
  obtain ⟨i, hi⟩ := r.plane
  intro hc
  have hle : r.cover.borel.W₁ ≤ d.V ⊓ centralizer (d.Y : Set G) :=
    le_inf (hi ▸ d.action.plane_le i) (le_centralizer_iff.mp (r.cover.plus ▸ hc))
  have hb : r.cover.borel.W₁ = ⊥ := le_bot_iff.mp (hle.trans s.fixed_vectors.le)
  have hcard := d.action.card_plane i
  rw [← hi, hb] at hcard
  norm_num at hcard

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
