module

public import CFSG.Quasithin.Chapter12.Section08.Setup.Consumers
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Construction
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Parabolic
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Transport

/-!
# Constructed flag geometry for the Section 12.8 source setup

Assemble the invariant flag, its uniqueness, source two-rank, nonidentity
point generator and omitted-point conjugator from elementary abelianness,
seed order and the full flag-independent LT action. Full L action separately
gives subspace transitivity and the normalizer transporter.

The higher-rank source hypothesis supplies these action inputs. The actual
LocalKernel application now receives a constructed F and g; the NormalL1
application receives the proved plane transitivity and transporter inputs.
The three universal earlier implications and the original nonabelian and
relative-normality antecedents remain explicit. The parent setup owner
retains their final source discharge and the rank-two action construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Notation 12.8.2 and
Lemma 12.8.3, printed pp.849–850; the omitted-point parabolic on p.852;
and the applications in 12.8.5(2) and 12.8.10(5), pp.850 and 854,
of `refs/quasithin.pdf`.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section08
namespace SetupFlagGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Uniform source flag, uniqueness, source rank, point generator and parabolic
conjugator. The full actor is LT, including the rank-two source alternative. -/
theorem exists_flag_geometry [IsElementaryAbelian 2 V]
    (hn : 2 ≤ n) (hc : Nat.card V = 2 ^ n)
    (hLV : L ≤ normalizer (V : Set G)) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (setupSeedAction (L ⊔ (T : Subgroup G)) V (sup_le hLV hTV))) :
    primeRank 2 V = n ∧ ∃ F : InvariantFlag T V n,
      (∀ i, i ≤ n → ∀ A : Subgroup G, A ≤ V → Nat.card A = 2 ^ i →
        (T : Subgroup G) ≤ normalizer (A : Set G) → A = F.Vi i) ∧
      ∃ z : G, z ≠ 1 ∧ F.Vi 1 = zpowers z ∧ ∃ g : G, g ∈ F.P L ∧ g ∉ F.H := by
  refine ⟨primeRank_eq_of_card hc, ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  obtain ⟨F, β, b, hcuts, huniq⟩ := exists_marked_flag hc hLV hTV hfull
  obtain ⟨x, hxP, hxH, _⟩ := exists_adjacent_lift F (by omega) hLV hTV hfull β b hcuts
  obtain ⟨z, hz, he⟩ := exists_point_generator F (by omega)
  exact ⟨F, huniq, z, hz, he, x, hxP, hxH⟩

end SetupFlagGeometry

namespace HigherRankHypothesis
open InvariantFlag SetupFlagGeometry
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The order of the original seed follows from its given natural coordinates. -/
theorem seed_card (h : HigherRankHypothesis K T L V n) : Nat.card V = 2 ^ n := by
  let := h.chosen.elementary
  have hc := Nat.card_congr h.naturalMarking.coordinates.toEquiv
  rw [Nat.card_congr Additive.ofMul]
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_zmod] using hc

/-- Construct Notation 12.8.2 and the omitted-point conjugator from the source
higher-rank hypothesis and its universal structural predecessor. -/
theorem exists_flag_geometry (h : HigherRankHypothesis K T L V n)
    (structural : Section02.Structural1222 K) :
    primeRank 2 V = n ∧ ∃ F : InvariantFlag T V n,
      (∀ i, i ≤ n → ∀ A : Subgroup G, A ≤ V → Nat.card A = 2 ^ i →
        (T : Subgroup G) ≤ normalizer (A : Set G) → A = F.Vi i) ∧
      ∃ z : G, z ≠ 1 ∧ F.Vi 1 = zpowers z ∧ ∃ g : G, g ∈ F.P L ∧ g ∉ F.H := by
  let := h.chosen.elementary
  exact SetupFlagGeometry.exists_flag_geometry (by have := h.rank; omega) h.seed_card
    h.chosen.normalizes (h.sylow_normalizes_seed structural) (h.full_LT_action structural)

/-- Lemma 12.8.3(2) for the higher-rank source alternative. -/
theorem subspace_transitive (h : HigherRankHypothesis K T L V n)
    (A B : Subgroup G) (hA : A ≤ V) (hB : B ≤ V) (hc : Nat.card A = Nat.card B) :
    ∃ l ∈ L, conjugate A l = B := by
  let := h.chosen.elementary
  exact SetupFlagGeometry.subspace_transitive h.full_L_action A B hA hB hc

/-- Lemma 12.8.3(3) for the higher-rank source alternative. -/
theorem flag_transporter (h : HigherRankHypothesis K T L V n)
    (F : InvariantFlag T V n) (i : ℕ) (g : G) (hg : F.Vi i ≤ conjugate V g) :
    ∃ k ∈ F.Gi i, conjugate V g = conjugate V k :=
  transporter_of_subspace_transitive F h.chosen.normalizes i
    (fun A hA hc => h.subspace_transitive A (F.Vi i) hA (F.le_seed i) hc) g hg

/-- Supply both geometric inputs to the existing normal-L₁ consumer, retaining
all three universal earlier implications and the source relative-normality antecedent. -/
theorem normal_L1_geometry_of_source
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hL1 : ((F.Li L 1).subgroupOf F.H).Normal) :
    (∀ i, 1 < i → i < n →
      conjugateSpanBy (F.Li L 1) (L ⊓ F.Gi i) = L ∧
      (F.Gi i : Set G) = (centralizer (F.Vi i : Set G) : Set G) *
        (L ⊓ F.Gi i : Subgroup G) ∧
      F.Gi i ≤ normalizer (L : Set G) ∧
      F.Gi i ≤ seedNormalizer (normalizer (L : Set G)) V ∧
      ∀ g : G, F.Vi i ≤ conjugate V g → conjugate V g = V) ∧
    ∀ g : G, g ∉ seedNormalizer (normalizer (L : Set G)) V →
      primeRank 2 (V ⊓ conjugate V g : Subgroup G) ≤ 1 := by
  apply h.normal_L1_geometry earlier F hL1
  · intro W hW hc
    apply h.subspace_transitive W (F.Vi 2) hW (F.le_seed 2)
    rw [hc, F.card 2 (by have := h.rank; omega)]
    rfl
  · intro i _ _ g hg
    exact h.flag_transporter F i g hg

/-- Supply an actual constructed flag and parabolic conjugator to the existing
LocalKernel center-product theorem. Its nonabelian and Z(U)^g≤U antecedents remain. -/
theorem exists_localKernel_center_product
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K) :
    ∃ (F : InvariantFlag T V n) (z g : G),
      z ≠ 1 ∧ F.Vi 1 = zpowers z ∧ g ∈ F.P L ∧ g ∉ F.H ∧
      (∀ i, i ≤ n → ∀ A : Subgroup G, A ≤ V → Nat.card A = 2 ^ i →
        (T : Subgroup G) ≤ normalizer (A : Set G) → A = F.Vi i) ∧
      (¬ IsMulCommutative F.U → conjugate F.ZU g ≤ F.U →
        (F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
          Disjoint (centerIn (F.I₂ L)) (F.Vi 1) ∧
          ∃ e : centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
            ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
        ⁅L, centerIn (F.I₂ L)⁆ = ⊥) := by
  obtain ⟨_, F, huniq, z, hz, he, g, hgP, hgH⟩ := h.exists_flag_geometry earlier.structural
  exact ⟨F, z, g, hz, he, hgP, hgH, huniq,
    fun hne => h.localKernel_center_product earlier F hne g hgP hgH⟩

end HigherRankHypothesis
end CFSG.Quasithin.Chapter12.Section08
