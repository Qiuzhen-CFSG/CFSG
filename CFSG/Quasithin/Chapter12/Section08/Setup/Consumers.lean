module

public import CFSG.Quasithin.Chapter12.Section08.Setup.Escape
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.LocalKernel

/-!
# The original higher-rank assumptions applied to the local proofs

The source hypothesis and the three universal earlier implications discharge
the natural marking, normalization, uniqueness, centralizer, escape, full-action
and LT-core inputs of the existing LocalKernel theorem. The original flag and
parabolic conjugator are explicit here; their construction is separate geometry.
The nonabelian branch and the original antecedent Z(U)^g ≤ U are preserved.

The NormalL1 application similarly supplies its marking, residual, normalizer
and TI inputs. Its independent relative-normality antecedent is retained, as
are the subspace and transporter inputs supplied by the flag construction.
These are conditional consumer applications, not a claim that all of Section
12.8 or its flag construction is complete.

Source: Aschbacher–Smith, Lemmas 12.8.3–5 and 12.8.10(5), pp.849–854.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section08.HigherRankHypothesis
open Section02 InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- All nongeneric geometry inputs to the existing LocalKernel center-product
consumer are derived from the original higher-rank source alternative. -/
theorem localKernel_center_product
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate F.ZU g ≤ F.U →
      (F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
        Disjoint (centerIn (F.I₂ L)) (F.Vi 1) ∧
        ∃ e : centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
          ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
      ⁅L, centerIn (F.I₂ L)⁆ = ⊥ := by
  let := h.chosen.elementary
  exact F.localKernel_source_center_product h.source.simpleQTKE L (normalizer (L : Set G))
    ⟨by have := h.rank; omega, h.rank.2⟩ h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual
    (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique earlier.structural earlier.uniqueness).2
    (h.seed_centralizer_le earlier.structural earlier.uniqueness)
    h.centralizer_L (h.flag_escape F earlier.alternatives)
    (h.binarySeedAction_surjective F) (fun _ => h.full_L_action)
    (h.centralizer_LT earlier.structural) hne g hgP hgH

/-- Application to every clause of the existing normal-L₁ geometry theorem.
The actual subspace/transporter conclusions are supplied independently by the
flag construction, and L₁-normality is the original antecedent of 12.8.5(2). -/
theorem normal_L1_geometry
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n)
    (hL1 : ((F.Li L 1).subgroupOf F.H).Normal)
    (hplanes : ∀ W : Subgroup G, W ≤ V → Nat.card W = 4 →
      ∃ l ∈ L, conjugate W l = F.Vi 2)
    (htrans : ∀ i, 1 < i → i < n → ∀ g : G, F.Vi i ≤ conjugate V g →
      ∃ k ∈ F.Gi i, conjugate V g = conjugate V k) :
    (∀ i, 1 < i → i < n →
      conjugateSpanBy (F.Li L 1) (L ⊓ F.Gi i) = L ∧
      (F.Gi i : Set G) = (centralizer (F.Vi i : Set G) : Set G) *
        (L ⊓ F.Gi i : Subgroup G) ∧
      F.Gi i ≤ normalizer (L : Set G) ∧
      F.Gi i ≤ seedNormalizer (normalizer (L : Set G)) V ∧
      ∀ g : G, F.Vi i ≤ conjugate V g → conjugate V g = V) ∧
    ∀ g : G, g ∉ seedNormalizer (normalizer (L : Set G)) V →
      primeRank 2 (V ⊓ conjugate V g : Subgroup G) ≤ 1 := by
  let := h.chosen.elementary
  exact F.normal_Li_one_geometry_of_ambient_natural h.naturalMarking
    h.rank.1 h.residual rfl hL1
    (fun g hg => h.seed_TI earlier.structural g⁻¹
      ((normalizer (L : Set G)).inv_mem hg))
    (h.seed_normalizer_le earlier.structural earlier.uniqueness) hplanes htrans

end CFSG.Quasithin.Chapter12.Section08.HigherRankHypothesis
