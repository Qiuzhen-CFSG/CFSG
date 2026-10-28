module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.TwoCentral
public import Theory.GroupAction.Defs

/-!
# Exact quotient and Sylow targets for 16.5.2 and 16.5.7

The projection is the actual map from N_G(L) to N_G(L)/C_G(L).
`IsProjectedTwoCentral` tests its image in the image of L, using an actual
Sylow subgroup of that image. It does not test the original element of R
for membership in L.

The two alternatives below retain both relative Sylow assertions, relative
normality of R, the half-order formula and the actual normalizing conjugator.
They are specifications to be proved, not certificates of a source theorem.
Left conjugation by l is used throughout, reversing the exponent convention
of the book.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemmas
16.5.2(2) and 16.5.7, printed pp.1195 and 1197–1198.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowRank
open Subgroup
variable {G : Type*} [Group G]

/-- H/K, with the centralizer normal only in the normalizer of L. -/
abbrev CentralizerQuotient (L : Subgroup G) :=
  normalizer (L : Set G) ⧸
    (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G))

/-- The canonical projection to the source's H*. -/
def projection (L : Subgroup G) : normalizer (L : Set G) →* CentralizerQuotient L :=
  QuotientGroup.mk' _

/-- The image of X ∩ H in H/K. Source applications retain X ≤ H separately. -/
def projected (L X : Subgroup G) : Subgroup (CentralizerQuotient L) :=
  (X.subgroupOf (normalizer (L : Set G))).map (projection L)

/-- Two-centrality of the projected element, rather than of u in ambient L. -/
def IsProjectedTwoCentral (L : Subgroup G) (u : G) : Prop :=
  ∃ hu : u ∈ normalizer (L : Set G),
    IsTwoCentralIn (projected L L) (projection L ⟨u, hu⟩)

/-- Alternative (a) of 16.5.2(2), including normality inside the chosen T₁. -/
def FullSylowAlternative (L : Subgroup G) (g : G) (R : Subgroup G) : Prop :=
  ∃ T₁ : Subgroup G,
    SylowIn T₁ (normalizer (L : Set G)) ∧
    SylowIn T₁ (normalizer (L : Set G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G)) ∧
    R ≤ T₁ ∧ T₁ ≤ normalizer (R : Set G) ∧ R ⊓ centerIn T₁ ≠ ⊥

/-- Alternative (b), retaining the product, its order and a genuine conjugator. -/
def HalfSylowAlternative (T : Sylow 2 G) (L : Subgroup G) (g : G)
    (R : Subgroup G) : Prop :=
  ∃ l ∈ L,
    let T₀ := commutingSylow T L ⊔ (componentSylow T L).conjBy l
    SylowIn T₀ (normalizer (L : Set G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G)) ∧
    R ≤ T₀ ∧ T₀ ≤ normalizer (R : Set G) ∧ Nat.card T₀ = Nat.card T / 2 ∧
    ∃ a : G, a ∈ normalizer (T₀ : Set G) ∧
      (centralizer (L : Set G)).conjBy a = (centralizer (L : Set G)).conjBy g

/-- The full, unweakened disjunction in 16.5.2(2). -/
def SylowAlternatives (T : Sylow 2 G) (L : Subgroup G) (g : G)
    (R : Subgroup G) : Prop :=
  FullSylowAlternative L g R ∨ HalfSylowAlternative T L g R

/-- The source implication to be constructed by the Sylow-alternatives proof.
It is uniform in the chosen Sylow subgroup, as needed when 16.5.7 replaces T.
The omega containment retains the standing Δ₀ choice made on p.1192. -/
def SylowAlternativeRule (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (z : G) (L : Subgroup G) (g : G) (R : Subgroup G),
    IntersectionSetup T z L g R →
    omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L →
    (∃ u ∈ R, orderOf u = 2 ∧ IsProjectedTwoCentral L u) →
    IsProjectedTwoCentral (L.conjBy g) z →
    (commutingSylow T L ⊔ componentSylow T L).relIndex (T : Subgroup G) ≤ 2 →
    SylowAlternatives T L g R

/-- The precise centralizer and index assumptions of 16.5.7. -/
def RankHypotheses (T : Sylow 2 G) (L : Subgroup G) : Prop :=
  center L = ⊥ ∧
  Nat.card ↥(projected L (T : Subgroup G) ⊓
    centralizer (projected L (componentSylow T L) : Set (CentralizerQuotient L))) = 2 ∧
  (projected L (componentSylow T L)).relIndex (projected L (T : Subgroup G)) ≤ 2

/-- More than one actual L-conjugacy class of involutions. -/
def MultipleInvolutionClasses (L : Subgroup G) : Prop :=
  ∃ u v : L, orderOf u = 2 ∧ orderOf v = 2 ∧ ¬ IsConj u v

end CFSG.Quasithin.Chapter16.Intersections.SylowRank
