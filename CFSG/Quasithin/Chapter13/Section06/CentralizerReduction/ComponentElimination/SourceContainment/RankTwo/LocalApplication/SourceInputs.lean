module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.Maps
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Preliminaries
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.MainForward.SourceFamilies
public import CFSG.Quasithin.Chapter6.SourceDefs
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# Exact source inputs for the rank-two local application

The standing record retains all four clauses of Hypothesis 13.3.1,
using the full known-simple catalogue and actual excluded group models,
and specializes to the A₅ counterexample of §13.6. Local inputs are the
genuine Sylow, normalization and reduced-module conclusions before
13.6.14, together with the reduced list following 13.6.18–19.

The reduced-module condition is transferred from its relative centralizer
quotient to the literal plus-action quotient. Thus O₂(G+)=1 is derived;
none of the requested local component or comparison conclusions is an
input. The enclosing source owners must construct these earlier inputs.

Source: Aschbacher–Smith, combined manuscript, Hypothesis 13.3.1,
p.884; §13.6, pp.926–931; Definition B.2.11 and B.2.14.
The even-field exclusion follows the same actual-carrier conventions as
Chapter13.Section08.TransvectionRecognition.Component.ModelExtension.SourceSetup.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Full Hypothesis 13.3.1, specialized to the A₅ counterexample setting
of §13.6. Every excluded family is represented by an actual carrier. -/
structure SourceHypothesis (T : Sylow 2 G) (L : Subgroup G) : Prop where
  qtke : IsSimpleQTKE KnownSimple.IsKnownSimple G
  local_component : L ∈ MainForward.faithfulLocalComponents T
  no_larger_field : ∀ f : ℕ, 1 < f → ¬
    ((∃ n : ℕ, ClassicalGroup.IsPSL G n (2 ^ f) ∨
      ClassicalGroup.IsPSU G n (2 ^ f) ∨ ClassicalGroup.IsPSp G n (2 ^ f) ∨
      ClassicalGroup.IsPOmegaPlus G n (2 ^ f) ∨
      ClassicalGroup.IsPOmegaOdd G n (2 ^ f) ∨
      ClassicalGroup.IsPOmegaMinus G n (2 ^ f)) ∨
    ClassificationModels.IsG2At G (2 ^ f) ∨
    ExceptionalGroup.IsF4 G (2 ^ f) ∨ ExceptionalGroup.IsE6 G (2 ^ f) ∨
    ExceptionalGroup.IsE7 G (2 ^ f) ∨ ExceptionalGroup.IsE8 G (2 ^ f) ∨
    ExceptionalGroup.IsTwistedE6 G (2 ^ f) ∨
    Triality.Standard.IsTrialityGroupAt (2 ^ f) G ∨
    (∃ m : ℕ, f = 2 * m + 1 ∧
      (Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∨
       Nonempty (G ≃* ReeF4.Model m))))
  no_linear : ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL G n 2
  no_alternating_nine : ¬ Nonempty (G ≃* alternatingGroup (Fin 9))
  no_sporadic : ∀ s : KnownSimple.SporadicName,
    s = .m22 ∨ s = .m23 ∨ s = .m24 ∨ s = .he ∨ s = .j4 →
      ¬ Nonempty (G ≃* s.Carrier)
  five_minimal : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ K ∈ MainForward.faithfulLocalComponents T,
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
  a5 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  counterexample : IsA5Counterexample G

/-- The literal earlier local conclusions consumed by the application.
The Sylow condition and cubic quotient precede 13.6.4; W_K is reduced
by B.2.14 in the paragraph preceding 13.6.14; normalization is 13.6.14.
The last field is the seven actual models following 13.6.18–19. -/
structure SourceInputs (T : Sylow 2 G) (K L : Subgroup G) (z v : G) : Prop where
  standing : SourceHypothesis T L
  involution : orderOf v = 2
  selected : K ∈ Yz L (T : Subgroup G) z v
  rank_two : primeRank 3 K = 2
  sylow_centralizer : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v)
  normalizes_component : Tv (T : Subgroup G) v ≤ normalizer (K : Set G)
  normalizes_residual : Tv (T : Subgroup G) v ≤ normalizer (Lv L v : Set G)
  centralizes_z : Tv (T : Subgroup G) v ≤ centralizer ({z} : Set G)
  cubic_quotient : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3
  reduced_module : WK K L (T : Subgroup G) z v ∈
    Chapter6.Source.reducedFamily (plusActor K L (T : Subgroup G) v)
  reduced_model : ReducedModel (plusImage K L (T : Subgroup G) z v
    normalizes_residual centralizes_z K)

omit [Finite G] in
/-- The earlier reduced-module conclusion gives the actual plus two-core condition. -/
theorem plus_twoCore_eq_bot_of_reduced (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hred : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v)) :
    pCore 2 (Gplus K L T z v hL hz) = ⊥ := by
  obtain ⟨hle, _, hn, hc⟩ := hred
  let W := WK K L T z v
  let A := plusActor K L T v
  let := hn
  have he : centralizer (W.subgroupOf A : Set A) = (plusConjugation K L T z v hL hz).ker := by
    rw [plusConjugation_ker]
    ext a
    change a ∈ centralizer (W.subgroupOf A : Set A) ↔ (a : G) ∈ centralizer (W : Set G)
    simp only [mem_centralizer_iff]
    constructor
    · intro h w hw
      exact congrArg Subtype.val (h ⟨w, hle hw⟩ hw)
    · intro h w hw
      exact Subtype.ext (h w hw)
  let e : (A ⧸ centralizer (W.subgroupOf A : Set A)) ≃* Gplus K L T z v hL hz :=
    QuotientGroup.quotientMulEquivOfEq he
  rw [← pCore_map_iso 2 e, hc, Subgroup.map_bot]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
