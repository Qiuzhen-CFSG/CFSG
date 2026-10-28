module

public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry
public import CFSG.Quasithin.Chapter12.Section08.Setup.RankTwoConstruction

/-!
# Both source setups and all clauses of Lemma 12.8.3

The full seed action factors through the literal centralizer quotient of M_V.
In higher rank its image is already the image of L. In dimension two its
image is the image of LT, while the L-image has order three. Subspace
transitivity then gives the normalizer transporter with right conjugation.
The constructed flag supplies the original point generator and a conjugator
in the omitted-point parabolic outside the point normalizer.

The LocalKernel, NormalL1 and SourceGeometry applications use these derived
facts. Only the higher-rank branch retains universal earlier implications:
12.2.2(3), 1.2.7 and the full 12.2.13. The Section 12.8 assembly owner must
prove them; the dimension-two branch uses only Hypothesis 12.8.1(2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis 12.8.1, Notation 12.8.2, Lemma 12.8.3, printed pp.849–850;
LocalKernel application 12.8.10(5), p.854, in refs/quasithin.pdf.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The action denominator, included in G, is precisely the source C_M(V).
Centralizing V already implies membership in N_G(V). -/
theorem setupSeedNormalizer_centralizer_image (M V : Subgroup G) :
    ((centralizer (V : Set G)).subgroupOf (seedNormalizer M V)).map
      (seedNormalizer M V).subtype = M ⊓ centralizer (V : Set G) := by
  rw [subgroupOf_map_subtype]
  apply le_antisymm
  · exact le_inf (inf_le_right.trans inf_le_left) inf_le_left
  · exact le_inf inf_le_right (le_inf inf_le_left
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))

namespace HigherRankHypothesis
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
variable (h : HigherRankHypothesis K T L V n)
include h

/-- L already gives all automorphisms of the elementary abelian seed. -/
theorem seed_action_surjective :
    Function.Surjective (setupSeedAction L V h.chosen.normalizes) := by
  intro a
  obtain ⟨l, hl, he⟩ := h.full_L_action a
  refine ⟨⟨l, hl⟩, ?_⟩
  ext v
  exact he v

/-- The literal M_V action is full because it contains the original L-action. -/
theorem full_seedNormalizer_action : Function.Surjective
    (setupSeedAction (seedNormalizer (normalizer (L : Set G)) V) V inf_le_right) := by
  intro a
  obtain ⟨l, hl⟩ := h.seed_action_surjective a
  exact ⟨⟨l, L.le_normalizer l.property, h.chosen.normalizes l.property⟩, hl⟩

/-- First alternative of 12.8.3(1), as equality of the literal action images. -/
theorem seedNormalizer_action_range :
    (setupSeedAction (seedNormalizer (normalizer (L : Set G)) V) V inf_le_right).range =
      (setupSeedAction L V h.chosen.normalizes).range := by
  rw [MonoidHom.range_eq_top.mpr h.full_seedNormalizer_action,
    MonoidHom.range_eq_top.mpr h.seed_action_surjective]

omit h [Finite G] in
instance seedNormalizerCentralizer_normal :
    ((centralizer (V : Set G)).subgroupOf
      (seedNormalizer (normalizer (L : Set G)) V)).Normal := by
  rw [← setupSeedAction_ker _ V (show seedNormalizer (normalizer (L : Set G)) V ≤
    normalizer (V : Set G) from inf_le_right)]
  infer_instance

/-- M_V/C_M(V) is the full automorphism group of the actual seed. -/
noncomputable def seedNormalizerQuotientEquiv :
    (seedNormalizer (normalizer (L : Set G)) V ⧸
      (centralizer (V : Set G)).subgroupOf (seedNormalizer (normalizer (L : Set G)) V)) ≃*
        MulAut V :=
  (QuotientGroup.quotientMulEquivOfEq
    (setupSeedAction_ker (seedNormalizer (normalizer (L : Set G)) V) V
      inf_le_right).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ h.full_seedNormalizer_action)

/-- The quotient isomorphism induces the given ambient conjugation action. -/
theorem seedNormalizerQuotientEquiv_mk
    (x : seedNormalizer (normalizer (L : Set G)) V) (v : V) :
    (h.seedNormalizerQuotientEquiv (QuotientGroup.mk' _ x) v : G) =
      (x : G) * (v : G) * (x : G)⁻¹ := rfl

/-- All four clauses of 12.8.3 in the higher-rank branch. The earlier
universal implications remain explicit, rather than local output assumptions. -/
theorem lemma1283 (earlier : EarlierSetupResults K) (F : InvariantFlag T V n) :
    ((setupSeedAction (seedNormalizer (normalizer (L : Set G)) V) V inf_le_right).range = ⊤ ∧
      (setupSeedAction (seedNormalizer (normalizer (L : Set G)) V) V inf_le_right).range =
        (setupSeedAction L V h.chosen.normalizes).range) ∧
    (∀ A B : Subgroup G, A ≤ V → B ≤ V → Nat.card A = Nat.card B →
      ∃ l ∈ L, conjugate A l = B) ∧
    (∀ i g, F.Vi i ≤ conjugate V g →
      ∃ k ∈ F.Gi i, conjugate V g = conjugate V k) ∧
    ¬ F.H ≤ normalizer (L : Set G) :=
  ⟨⟨MonoidHom.range_eq_top.mpr h.full_seedNormalizer_action,
      h.seedNormalizer_action_range⟩, h.subspace_transitive,
    h.flag_transporter F, h.flag_escape F earlier.alternatives⟩

/-- The three abelian-span alternatives of SourceGeometry now have their
transitivity and escape premises discharged from the source setup. -/
theorem abelian_source_geometry (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) :
    ((∀ J ∈ F.Hz L (normalizer (L : Set G)), IsMulCommutative (F.UH J)) ↔
      IsMulCommutative F.U) ∧
    (IsMulCommutative F.U ↔ ∀ g : G,
      V ⊓ conjugate V g ≠ ⊥ → ⁅V, conjugate V g⁆ = ⊥) := by
  refine ⟨F.all_local_spans_abelian_iff (by have := h.rank; omega) L _
    (h.flag_escape F earlier.alternatives), ?_⟩
  obtain ⟨z, hz, he⟩ := SetupFlagGeometry.exists_point_generator F (by have := h.rank; omega)
  apply F.abelian_U_iff_intersections_commute (by have := h.rank; omega) z he hz
  intro x hx hx1
  obtain ⟨l, hl, hconj⟩ := h.vector_transitive
    (F.le_seed 1 (he ▸ mem_zpowers z)) hx hz hx1
  exact ⟨l, h.chosen.normalizes hl, hconj⟩

/-- The original parabolic receives its SourceGeometry containment application. -/
theorem parabolic_seed_geometry (F : InvariantFlag T V n)
    (g : G) (hg : g ∈ F.P L) :
    V ≤ F.E g ∧ conjugate F.ZU g ≤ centralizer (V : Set G) := by
  let := h.chosen.elementary
  exact F.parabolic_seed_geometry L h.chosen.normalizes g hg

end HigherRankHypothesis

namespace RankTwoHypothesis
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L M : Subgroup G}
variable (h : RankTwoHypothesis K T L M)
include h

/-- In dimension two M_V and LT have the same full S₃ action. -/
theorem seedNormalizer_action_range :
    (setupSeedAction (seedNormalizer M (rankTwoSeed T M)) (rankTwoSeed T M) inf_le_right).range =
      (setupSeedAction (L ⊔ (T : Subgroup G)) (rankTwoSeed T M)
        ((sup_le h.L_le h.sylow_le).trans M_normalizes_seed)).range := by
  rw [MonoidHom.range_eq_top.mpr h.full_seedNormalizer_action,
    MonoidHom.range_eq_top.mpr h.full_LT_action]

omit h [Finite G] in
/-- The source note M_i ≤ M_V follows from the normality of the actual seed. -/
theorem flag_normalizer_le (F : InvariantFlag T (rankTwoSeed T M) 2) (i : ℕ) :
    F.Mi M i ≤ seedNormalizer M (rankTwoSeed T M) := by
  rw [seedNormalizer_eq]
  exact inf_le_left

/-- The C₃ subspace action supplies the A.1.7 normalizer transporter. -/
theorem flag_transporter (F : InvariantFlag T (rankTwoSeed T M) 2)
    (i : ℕ) (g : G) (hg : F.Vi i ≤ conjugate (rankTwoSeed T M) g) :
    ∃ k ∈ F.Gi i, conjugate (rankTwoSeed T M) g = conjugate (rankTwoSeed T M) k :=
  SetupFlagGeometry.transporter_of_subspace_transitive F h.L_normalizes_seed i
    (fun A hA hc => h.subgroup_transitive A (F.Vi i) hA (F.le_seed i) hc) g hg

/-- All four clauses of 12.8.3 in dimension two, without any Chapter 12.2 input.
The order-three L-image is kept distinct from the full LT-image. -/
theorem lemma1283 (F : InvariantFlag T (rankTwoSeed T M) 2) :
    ((setupSeedAction (seedNormalizer M (rankTwoSeed T M)) (rankTwoSeed T M) inf_le_right).range = ⊤ ∧
      (setupSeedAction (seedNormalizer M (rankTwoSeed T M)) (rankTwoSeed T M) inf_le_right).range =
        (setupSeedAction (L ⊔ (T : Subgroup G)) (rankTwoSeed T M)
          ((sup_le h.L_le h.sylow_le).trans M_normalizes_seed)).range) ∧
    (∀ A B : Subgroup G, A ≤ rankTwoSeed T M → B ≤ rankTwoSeed T M →
      Nat.card A = Nat.card B → ∃ l ∈ L, conjugate A l = B) ∧
    (∀ i g, F.Vi i ≤ conjugate (rankTwoSeed T M) g →
      ∃ k ∈ F.Gi i, conjugate (rankTwoSeed T M) g = conjugate (rankTwoSeed T M) k) ∧
    ¬ F.H ≤ M :=
  ⟨⟨MonoidHom.range_eq_top.mpr h.full_seedNormalizer_action,
      h.seedNormalizer_action_range⟩, h.subgroup_transitive,
    h.flag_transporter F, h.flag_escape F⟩

/-- Construct Notation 12.8.2 and the omitted-point conjugator from precisely
the second source alternative. Only the full LT action is used. -/
theorem exists_flag_geometry :
    primeRank 2 (rankTwoSeed T M) = 2 ∧
      ∃ F : InvariantFlag T (rankTwoSeed T M) 2,
        (∀ i, i ≤ 2 → ∀ A : Subgroup G, A ≤ rankTwoSeed T M → Nat.card A = 2 ^ i →
          (T : Subgroup G) ≤ normalizer (A : Set G) → A = F.Vi i) ∧
        ∃ z : G, z ≠ 1 ∧ F.Vi 1 = zpowers z ∧ ∃ g : G, g ∈ F.P L ∧ g ∉ F.H := by
  let := rankTwoSeed_elementary h
  exact SetupFlagGeometry.exists_flag_geometry (by decide) (rankTwoSeed_card h)
    h.L_normalizes_seed (h.sylow_le.trans M_normalizes_seed) h.full_LT_action

/-- The constructed rank-two flag and conjugator supply every setup input to
LocalKernel. The original nonabelian branch and Z(U)^g≤U antecedent remain. -/
theorem exists_localKernel_center_product :
    ∃ (F : InvariantFlag T (rankTwoSeed T M) 2) (z g : G),
      z ≠ 1 ∧ F.Vi 1 = zpowers z ∧ g ∈ F.P L ∧ g ∉ F.H ∧
      (∀ i, i ≤ 2 → ∀ A : Subgroup G, A ≤ rankTwoSeed T M → Nat.card A = 2 ^ i →
        (T : Subgroup G) ≤ normalizer (A : Set G) → A = F.Vi i) ∧
      sylowOmega T = F.Vi 1 ∧ F.Li L 1 = ⊥ ∧
      (¬ IsMulCommutative F.U → conjugate F.ZU g ≤ F.U →
        (F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
          Disjoint (centerIn (F.I₂ L)) (F.Vi 1) ∧
          ∃ e : centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
            ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
        ⁅L, centerIn (F.I₂ L)⁆ = ⊥) := by
  obtain ⟨_, F, huniq, z, hz, he, g, hgP, hgH⟩ := h.exists_flag_geometry
  exact ⟨F, z, g, hz, he, hgP, hgH, huniq, h.sylowOmega_eq_point F,
    h.Li_one_eq_bot F, fun hne => h.localKernel_center_product F hne g hgP hgH⟩

end RankTwoHypothesis
end CFSG.Quasithin.Chapter12.Section08
