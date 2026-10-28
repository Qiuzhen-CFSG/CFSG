module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.PreGeometry.Source
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.OuterProduct

/-!
# The first local-cover paragraph of 15.3.38

The earlier source constructor proves the centre geometry without the full
15.3.37 product. After centre identification, the actual outer action embeds
I/L in Out(PSL₃(4)), whose order divides twelve. The opposite residual supplies
an outer cubic and the local Sylow supplies the full two-part. Consequently
the three source factors generate I; their normalization gives the literal
set product I=L Y_D S. No additional automorphism-coverage premise remains.

The marked constructor retains the original field, equivalence and actor.
The final rank-two constructor selects that marked branch using the uniformly
quantified earlier alternatives. Its output includes the genuine E₉ quotient,
Y₊=Y, the two-core identities, both local centralizers and the compatible
interchange of the original planes, through the constructed `PrecentreData`.
This is the first paragraph reduction, not the later contradiction of 15.3.38.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of 15.3.38,
printed pp.1135--1136, through I=L Y_D S.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
open Candidates.LinearCore
variable {G : Type*} [Group G] [Finite G]

/-- The constructed centre geometry gives the literal I-product, with the
outer-order calculation discharged for the originally marked field. -/
theorem PrecentreData.local_product
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G} {n : ℕ}
    {c : ProjectiveMarking L (2 ^ n)} {y : d.Yplus}
    (g : PrecentreData d I L c y) (h : MatrixImage.SourceSetup d I L) :
    (I : Set G) = (L : Set G) * (planeResidual d.M d.Y g.borel.W₂ : Set G) *
      (d.S : Set G) := by
  let : IsQuasisimple (L.subgroupOf I) := h.component.2
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal _ _)
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  have hYI : d.Y ≤ I := g.plus.ge.trans (le_sup_left.trans h.outside.1.2)
  have hSD : d.S ≤ normalizer (planeResidual d.M d.Y g.borel.W₂ : Set G) :=
    normalizes_planeResidual (hSM.trans d.M.le_normalizer) (hSM.trans hMY)
      g.borel.second_invariant
  have hcard : Nat.card c.F = 4 := by rw [c.card, g.parameter]; norm_num
  obtain ⟨P, hP⟩ := h.sylow
  exact product_of_marked_outer_order c g.center_core.ge h.component_le
    (((planeResidual_le _ _ _).trans inf_le_left).trans hYI)
    (le_sup_right.trans h.outside.1.2)
    ((normal_subgroupOf_iff_le_normalizer h.component_le).mp g.normal)
    (g.overgroup_centralizer ▸ g.center_plane ▸ centerImage_le L) P hP hSD
    (Matrix.PSL3Four.OuterThreeStructure.outer_card_dvd_twelve_of_card_four hcard)
    g.opposite_diagonal

/-- All first-paragraph conclusions in the selected original marking.
The root, central-cover and final product calculations have no remaining
model premises. Earlier source conclusions retain their exact hypotheses. -/
theorem local_cover_of_marked_source
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : MatrixImage.SourceSetup d I L) (e : SourceBorel.Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (y : d.Yplus) (hy : c.Diagonal (y : G))
    (hcase : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    ∃ g : PrecentreData d I L c y,
      (I : Set G) = (L : Set G) * (planeResidual d.M d.Y g.borel.W₂ : Set G) *
        (d.S : Set G) ∧
      ∃ hq : 2 ^ n = 4, (resizeMarking c hq).Diagonal (y : G) ∧
        ∃ z ∈ planeResidual d.M d.Y g.borel.W₂, (resizeMarking c hq).Diagonal z := by
  obtain ⟨g⟩ := precentre_of_marked_source h e hn heven c y hy hcase h7 himage7 hΩ hVY
  exact ⟨g, g.local_product h, g.toPreparedResiduals.marking_four hy⟩

/-- The genuine centralizer three-part in the split alternative contradicts
the three-prime centralizer bound. Thus no separate rank bound for the listed
rank-one models is needed to select the diagonal branch. -/
theorem marked_diagonal_of_source_three_part {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : MatrixImage.SourceSetup d I L)
    (hYL : ¬ d.Yplus ≤ L)
    (h37 : d.Yplus ≤ localSpan L d.S ∨
      3 ^ (Nat.card (centralizingPart d.Yplus L)).factorization 3 = 3 ∨
      Candidates.RankTwoDiagonal d.Yplus L (localSpan L d.S)) :
    ∃ n : ℕ, 0 < n ∧ Even n ∧ ∃ y ∈ d.Yplus,
      ∃ c : ProjectiveMarking L (2 ^ n), c.Diagonal y := by
  have hd : Candidates.RankTwoDiagonal d.Yplus L (localSpan L d.S) := by
    rcases h37 with hle | hc | hd
    · exact (hYL (hle.trans h.orbit_eq.ge)).elim
    · have hcop := Candidates.local_centralizer_three_coprime h.component_le h.component
        h.odd_core h.rank_component.ge h.rank_overgroup
      have hCI : centralizingPart d.Yplus L ≤ I ⊓ centralizer (L : Set G) :=
        (map_subtype_le _).trans (inf_le_inf (le_sup_left.trans h.outside.1.2) le_rfl)
      have h3 : 3 ∣ Nat.card (centralizingPart d.Yplus L) :=
        hc ▸ Nat.ordProj_dvd (Nat.card (centralizingPart d.Yplus L)) 3
      exact ((Nat.prime_three.coprime_iff_not_dvd.mp hcop)
        (h3.trans (card_dvd_of_le hCI))).elim
    · exact hd
  obtain ⟨n, hn, heven, y, hyY, c, hy, _⟩ := marking_of_rankTwoDiagonal hd
  exact ⟨n, hn, heven, y, hyY, c, hy⟩

/-- Select the diagonal branch and complete the local-cover reduction.
The earlier alternatives, odd-core and rank statements remain uniform over
eligible outside overgroups. Only the centralizer three-part of the second
alternative is used, as in the source-correct three-part reduction. The field-order-four marking is the selected
marking reindexed by the deduced equality n=2. -/
theorem local_cover_of_rank_two
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : MatrixImage.SourceSetup d I L) (e : SourceBorel.Earlier d)
    (hYL : ¬ d.Yplus ≤ L)
    (h37 : ∀ J ∈ d.Hplus, ∀ K : Subgroup G,
      K ≤ J → IsComponent J (K.subgroupOf J) →
      d.Yplus ≤ localSpan K d.S ∨
        3 ^ (Nat.card (centralizingPart d.Yplus K)).factorization 3 = 3 ∨
        Candidates.RankTwoDiagonal d.Yplus K (localSpan K d.S))
    (hcase : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    ∃ (c : ProjectiveMarking L 4) (y : d.Yplus) (g : PrecentreData d I L (n := 2) c y),
      c.Diagonal (y : G) ∧
      (I : Set G) = (L : Set G) * (planeResidual d.M d.Y g.borel.W₂ : Set G) *
        (d.S : Set G) := by
  obtain ⟨n, hn, heven, y, hyY, c, hy⟩ := marked_diagonal_of_source_three_part h hYL
    (h37 I h.outside L h.component_le h.component)
  obtain ⟨g, hp, _⟩ := local_cover_of_marked_source h e hn heven c ⟨y, hyY⟩ hy
    hcase h7 himage7 hΩ hVY
  have hn2 := g.parameter
  subst n
  exact ⟨c, ⟨y, hyY⟩, g, hy, hp⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
