module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.Ree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.BinaryTriality
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.Linear
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.Symplectic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.G2
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.G2Derived
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.Triality
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.Tits
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.BinaryThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.EvenDegree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.CarrierReduction
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Reducing the rank-two containing carriers

The linear-three common-centralizer result contradicts the original moved
normalizer. Symplectic placement supplies both literal markings to the
scalar obstruction. The binary derived symplectic carrier is A₆, which
cannot contain the nonzero fully moved elementary image. These arguments
remove all classical rank-two rows from the actual escaping configuration.

The nonbinary G₂ and triality comparisons also exclude their actual
containing configurations. The Tits full-Sylow overgroups are solvable,
excluding that carrier too. The refined reduction retains binary triality,
Ree and derived binary G₂ at the existing interface. The new binary-derived
comparison removes its last row, leaving only binary triality and Ree.
The general moved-image comparison now excludes binary triality for every
original quotient and module row. Only Ree remains at this sharper boundary.
The embedded linear-residual comparison now excludes Ree whenever three
divides the original quotient. In particular this completes the rank-two
comparison for every binary PSL₂ quotient, alongside the earlier L₃(2)
comparison, retaining all module rows and fixed vectors.
Source: Aschbacher--Smith 10.2.9, printed pp.750--751.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
open Chapter3.Section02
universe u

/-- The exceptional rank-two carriers not discharged by the classical
inspection. Each alternative retains an actual model isomorphism. -/
def RemainingModel (H : Type*) [Group H] : Prop :=
  (∃ n, 2 ≤ n ∧ ClassificationModels.IsG2At H (2 ^ n)) ∨
  (∃ n, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2 ^ n) H) ∨
  (∃ m, 1 ≤ m ∧ Nonempty (H ≃* ReeF4.Model m)) ∨
  Nonempty (H ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
  Nonempty (H ≃* Tits.ParrottGroup)

/-- The remaining rank-two carriers after the core-center comparisons.
The original `RemainingModel` boundary remains available above. -/
def ResidualModel (H : Type*) [Group H] : Prop :=
  Nonempty (H ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) ∨
  (∃ m, 1 ≤ m ∧ Nonempty (H ≃* ReeF4.Model m)) ∨
  Nonempty (H ≃* commutator (Atlas.G2.Model (ZMod 2)))

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The actual linear-three common-centralizer conclusion contradicts
the original moved-normalizer bound in the point-control consumer. -/
theorem not_linear [Group.IsPerfect I] {n : ℕ} (hn : 1 ≤ n)
    (hm : ClassicalGroup.IsPSL (I ⧸ center I) 3 (2 ^ n)) : False :=
  source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer I
    c.escapes (linear_common_centralizer D c hn hm)

/-- The binary derived symplectic endpoint is excluded by the actual
A₆ equivalence and the fully moved elementary image. -/
theorem not_binary_symplectic [Group.IsPerfect I]
    (e : (I ⧸ center I) ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) : False := by
  have h := Other.alternating_degree D c (by decide : 6 ≤ 8)
    (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
  omega

/-- The exact unresolved part of the rank-two catalogue on the original
escaping component, after applying every classical endpoint. -/
theorem remaining_models [Group.IsPerfect I]
    (hm : ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) :
    RemainingModel (I ⧸ center I) := by
  obtain ⟨n,hm⟩ := hm
  cases hm with
  | linear hn hm => exact (not_linear D c hn hm).elim
  | symplectic hn hm => exact (not_symplectic D c hn hm).elim
  | g2 hn hm => exact .inl ⟨n,hn,hm⟩
  | triality hn hm => exact .inr (.inl ⟨n,hn,hm⟩)
  | ree_f4 m hm _ he => exact .inr (.inr (.inl ⟨m,hm,he⟩))
  | symplectic_derived _ he => exact (not_binary_symplectic D c he.some).elim
  | g2_derived _ he => exact .inr (.inr (.inr (.inl he)))
  | tits _ he => exact .inr (.inr (.inr (.inr he)))

/-- Apply the G₂ and triality comparisons to the literal source catalogue.
In particular the triality field of order two is retained explicitly. -/
theorem remaining_exceptional_models [IsQuasisimple I]
    (hm : ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) :
    ResidualModel (I ⧸ center I) := by
  rcases remaining_models D c hm with hg | ht | hr | hb | hs
  · obtain ⟨n,hn,hm⟩ := hg
    exact (not_g2 D c hn hm).elim
  · obtain ⟨n,hn,hm⟩ := ht
    by_cases he : n = 1
    · subst n
      exact .inl ((Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp hm)
    · exact (not_triality_large D c (by omega) hm).elim
  · exact .inr (.inl hr)
  · exact .inr (.inr hb)
  · exact (not_tits D c hs.some).elim

/-- Both the ordinary and binary-derived G₂ branches are now excluded.
The binary triality and Ree embeddings remain source obligations. -/
theorem remaining_triality_or_ree [IsQuasisimple I]
    (hm : ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) :
    Nonempty ((I ⧸ center I) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) ∨
    (∃ m, 1 ≤ m ∧ Nonempty ((I ⧸ center I) ≃* ReeF4.Model m)) := by
  rcases remaining_exceptional_models D c hm with ht | hr | hg
  · exact .inl ht
  · exact .inr hr
  · exact (not_binary_g2 D c hg.some).elim

/-- The general binary triality comparison leaves only an actual Ree
isomorphism, for every original quotient and module row. -/
theorem remaining_ree_models [IsQuasisimple I]
    (hm : ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) :
    ∃ m, 1 ≤ m ∧ Nonempty ((I ⧸ center I) ≃* ReeF4.Model m) := by
  rcases remaining_triality_or_ree D c hm with ht | hr
  · exact (not_binary_triality D c ht.some).elim
  · exact hr

/-- Every rank-two containing carrier is excluded for the original binary-three
quotient. All its module rows, including four-natural, remain covered. -/
theorem not_rank_two_of_binary_three [IsQuasisimple I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (hm : ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) : False := by
  rcases remaining_triality_or_ree D c hm with ht | hr
  · exact not_binary_triality_of_binary_three D c dL ht.some
  · obtain ⟨m,hm,⟨e⟩⟩ := hr
    exact not_ree_of_binary_three D c dL hm e

/-- The complete rank-two exclusion for every even-degree binary rank-one
quotient, using only the original point-component hypotheses. -/
theorem not_rank_two_of_even_binary_quotient [IsQuasisimple I]
    {n : ℕ} (hn : 0 < n) (he : Even n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hm : ∃ r, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) r) : False := by
  rcases remaining_triality_or_ree D c hm with ht | hr
  · exact not_binary_triality_of_even_binary_quotient D c hn he hL ht.some
  · obtain ⟨m,hm,⟨e⟩⟩ := hr
    exact not_ree_of_even_binary_quotient D c hn he hL hm e

/-- Three-divisibility of the intrinsic original quotient excludes every
rank-two containing carrier on the literal escaping configuration. -/
theorem not_rank_two_of_three [IsQuasisimple I]
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (hm : ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) : False := by
  obtain ⟨m,hm,⟨e⟩⟩ := remaining_ree_models D c hm
  exact not_ree_of_three D c h3 hm e

/-- Complete rank-two exclusion for the binary rank-one quotient, with
no parity restriction and no irreducibility assumption on the module. -/
theorem not_rank_two_of_binary_quotient [IsQuasisimple I]
    {n : ℕ} (hn : 0 < n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hm : ∃ r, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) r) : False := by
  obtain ⟨m,hm,⟨e⟩⟩ := remaining_ree_models D c hm
  exact not_ree_of_binary_quotient D c hn hL hm e

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
