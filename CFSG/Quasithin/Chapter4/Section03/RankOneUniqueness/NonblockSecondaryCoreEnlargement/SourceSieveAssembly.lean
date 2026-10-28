module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveFrontier
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveOddFieldActions
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveTrialitySplit
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveTriality
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveSmallModels
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoverage
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionSmall
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionDegrees
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionCentralCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionCubicSylows
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionOddCentralizer

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionLinear
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionLinearNormalizer
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionJankoFour

/-!
# Source assembly with the natural-action generation proof

The corrected source record carries the literal normal-quotient action, while
the natural coordinates prove generation for the whole secondary radical.  This
module is the narrow consumer that transports that identity to the source sieve
and discharges its generation premise. The four small quotient models also
supply their degree-two clauses by the literal secondary section. The final
exports discharge the model alternatives, while the earlier conditional
interfaces retain their statements.

The prime-restriction assembly consumes the literal Ree and triality
field-action exclusions, including the nonsplit seven-actor. The final export
therefore supplies the complete rank-or-diagonal clause in every source degree.
The reduced catalogue additionally excludes alternating, Bender and higher
binary linear rows on the actual inner image. Odd, rank-two and sporadic
local rows remain for the proper two-local model inspection. The further
reduction excludes odd PSL₂ and seven sporadic rows. Odd ternary rows have
degree two or three; M₂₄, J₂ and Ru have degree three, while J₄ has odd degree.
The central-core analysis further forces degree two in the odd ternary rows
and excludes J₂. The odd ternary alternatives now describe the full component
quotient. The cubic Sylow obstruction then excludes M₂₄ and Ru and restricts
J₄ to degree five. Cyclic centralizers of perfect subgroups then exclude every
odd ternary row, using generation and the original core movement. Binary
rank-two inspection now forces the full quotient to be PSL₃(4), with its
original outer torus clause. The marked F₃₂ root plane and the single factor
31 in the J₄ order exclude the final degree-five branch. Thus the final
exceptional-model conclusion has no model-selection callback. The MS and
secondary source witnesses and their original parabolic/Sylow markings remain
the independent earlier inputs of the nonblock construction owner.
The earlier partial frontiers
retain their original statements.

Source: Aschbacher--Smith, 4.3.10--16, printed pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels
open ChapterA.Section03.OddPrime.SourceModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The source witness and its natural coordinates provide the exact
whole-radical generation premise required by the corrected exceptional sieve. -/
theorem SecondaryActionData.exceptional_of_coordinates_and_models
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hm : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n ∨
      ExceptionalModel (s.component ⧸ pCore 2 s.component) n) :
    (n = 2 ∧ (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)) ∧
      (s.torus.subgroupOf (rootNormalizer c)).map s.action ⊓
        MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥ := by
  exact SecondaryActionData.exceptional_of_source_inputs s D h hn
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) hm

/-- In even degree, the same coordinates provide the complete source-facing
local-image and prime-rank inputs for the remaining two-local inspection. -/
theorem SecondaryActionData.even_degree_inputs_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1 < n) (heven : Even n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    SecondaryActionData.LocalImageData s ∧
      ChapterA.Section02.IsTheoremCModel (SecondaryActionData.componentImage s) ∧
      ∀ p : ℕ, p.Prime → Odd p → p ∣ 2^n - 1 →
        primeRank p s.component = 1 ∨
          (p = 3 ∧ ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
            IsPSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q ∧
            ∃ x : rootNormalizer c, (x : G) ∈ s.torus ∧ orderOf x = 3 ∧
              IsProjectiveDiagonalSign (s.component ⧸ pCore 2 s.component)
                unitary q (s.action x) ∧
              s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component)) := by
  apply SecondaryActionData.even_degree_inspection_inputs s
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) D h heven

/-- Natural coordinates and any of the four small actual quotient models
discharge both generation and degree recognition in the source sieve. The
remaining model classification is still an explicit mathematical premise. -/
theorem SecondaryActionData.exceptional_of_coordinates_and_small_models
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hm : (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 5 ∨
      Nonempty ((s.component ⧸ pCore 2 s.component) ≃* Janko1.Model)) ∨
      (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 ∨
        ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)) :
    (n = 2 ∧ (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)) ∧
      (s.torus.subgroupOf (rootNormalizer c)).map s.action ⊓
        MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥ := by
  exact SecondaryActionData.exceptional_of_small_models s hn
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) D h hm

/-- Natural coordinates supply the actual generation identity. The corrected
inspection now has only the odd-degree triality prime restriction unresolved;
all field actors and subgroup images refer to the original quotient action. -/
theorem SecondaryActionData.inspection_inputs_of_coordinates_except_triality
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    SecondaryActionData.LocalImageData s ∧
      ChapterA.Section02.IsTheoremCModel (SecondaryActionData.componentImage s) ∧
      ∀ p : ℕ, p.Prime → Odd p → p ∣ 2^n-1 →
        primeRank p s.component = 1 ∨
          (p = 3 ∧ ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
            IsPSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q ∧
            ∃ x : rootNormalizer c, (x : G) ∈ s.torus ∧ orderOf x = 3 ∧
              IsProjectiveDiagonalSign (s.component ⧸ pCore 2 s.component)
                unitary q (s.action x) ∧
              s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component)) ∨
          (Odd n ∧ center (s.component ⧸ pCore 2 s.component)=⊥ ∧
            ∃ f : ℕ, 1≤f ∧ p ∣ f ∧ Triality.Standard.IsTrialityGroupAt (2^f)
              (s.component ⧸ pCore 2 s.component)) := by
  refine ⟨SecondaryActionData.localImageData s D,
    SecondaryActionData.componentImage_theoremC s D h,?_⟩
  intro p hp ho hd
  rcases SecondaryActionData.component_primeRank_one_or_two s D h hp ho hd with hr | hr
  · exact Or.inl hr
  · apply Or.inr
    by_cases hp3 : p=3
    · subst p
      exact Or.inl ⟨rfl,SecondaryActionData.cubic_rank_two_diagonal_actor s
        (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) D h hd hr.ge⟩
    · exact Or.inr (SecondaryActionData.noncubic_rank_two_triality s D h hn hp ho hd hp3 hr.ge)

/-- The natural coordinates supply generation, and the literal field action
excludes all split triality primes. The remaining triality alternative has
coprime degrees and a nonsplit prime dividing its base degree; its fixed-rank
exclusion and the proper two-local classification remain separate obligations. -/
theorem SecondaryActionData.inspection_inputs_of_coordinates_except_nonsplit_triality
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    SecondaryActionData.LocalImageData s ∧
      ChapterA.Section02.IsTheoremCModel (SecondaryActionData.componentImage s) ∧
      ∀ p : ℕ, p.Prime → Odd p → p ∣ 2^n-1 →
        primeRank p s.component = 1 ∨
          (p = 3 ∧ ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
            IsPSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q ∧
            ∃ x : rootNormalizer c, (x : G) ∈ s.torus ∧ orderOf x = 3 ∧
              IsProjectiveDiagonalSign (s.component ⧸ pCore 2 s.component)
                unitary q (s.action x) ∧
              s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component)) ∨
          (Odd n ∧ center (s.component ⧸ pCore 2 s.component)=⊥ ∧
            ∃ f : ℕ, 1≤f ∧ p ∣ f ∧ Nat.Coprime n f ∧ ¬ p ∣ 2^f-1 ∧
              Triality.Standard.IsTrialityGroupAt (2^f)
                (s.component ⧸ pCore 2 s.component)) := by
  refine ⟨SecondaryActionData.localImageData s D,
    SecondaryActionData.componentImage_theoremC s D h,?_⟩
  intro p hp ho hd
  rcases SecondaryActionData.component_primeRank_one_or_two s D h hp ho hd with hr | hr
  · exact Or.inl hr
  · apply Or.inr
    by_cases hp3 : p=3
    · subst p
      exact Or.inl ⟨rfl,SecondaryActionData.cubic_rank_two_diagonal_actor s
        (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) D h hd hr.ge⟩
    · exact Or.inr (SecondaryActionData.noncubic_rank_two_triality_nonsplit
        s D h hn hp ho hd hp3 hr.ge)

/-- Natural coordinates discharge generation, and the actual field actors
discharge both triality and Ree. These are the complete source prime-rank and
local-image inputs to the remaining proper two-local inspection. -/
theorem SecondaryActionData.inspection_inputs_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    SecondaryActionData.LocalImageData s ∧
      ChapterA.Section02.IsTheoremCModel (SecondaryActionData.componentImage s) ∧
      ∀ p : ℕ, p.Prime → Odd p → p ∣ 2^n-1 →
        primeRank p s.component = 1 ∨
          (p = 3 ∧ ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
            IsPSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q ∧
            ∃ x : rootNormalizer c, (x : G) ∈ s.torus ∧ orderOf x = 3 ∧
              IsProjectiveDiagonalSign (s.component ⧸ pCore 2 s.component)
                unitary q (s.action x) ∧
              s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component)) := by
  refine ⟨SecondaryActionData.localImageData s D,
    SecondaryActionData.componentImage_theoremC s D h,?_⟩
  intro p hp ho hd
  exact SecondaryActionData.prime_rank_or_diagonal s
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) D h hn hp ho hd

/-- The natural-action generation proof excludes all alternating, Bender and
higher binary linear rows on the actual inner image. The remaining three
catalogue families still require the proper two-local inspection. -/
theorem SecondaryActionData.inspection_remaining_models_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ChapterA.Section02.IsTheoremCOddModel (SecondaryActionData.componentImage s) ∨
      (∃ f : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel
        (SecondaryActionData.componentImage s) f) ∨
      ChapterA.Section02.IsTheoremCSporadicModel (SecondaryActionData.componentImage s) :=
  SecondaryActionData.inspection_remaining_models s hn
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) D h

/-- Natural coordinates discharge generation for the remaining local rows.
The literal inner models retain central covers, and no model-selection callback
is added to the original source hypotheses. The final two-local inspection remains. -/
theorem SecondaryActionData.inspection_remaining_rows_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ((n=2 ∨ n=3) ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧
      (ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 p ∨
        ClassicalGroup.IsPSU (SecondaryActionData.componentImage s) 3 p)) ∨
      (∃ f : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel
        (SecondaryActionData.componentImage s) f) ∨
      (Odd n ∧ ((n=3 ∧ ∃ name : ClassificationModels.SporadicName,
        (name = .m24 ∨ name = .j2 ∨ name = .ru) ∧
        Nonempty (SecondaryActionData.componentImage s ≃* name.Carrier)) ∨
        Nonempty (SecondaryActionData.componentImage s ≃* Janko4.Model))) :=
  SecondaryActionData.inspection_remaining_rows s hn
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) D h

/-- The natural-action generation proof excludes J₂ and removes degree three
from the odd ternary branch. Its remaining ternary models are on the full
quotient, while the other rows retain their actual inner-image isomorphisms. -/
theorem SecondaryActionData.inspection_remaining_rows_after_core_analysis_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (n=2 ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧
      (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 p ∨
        ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 p)) ∨
      (∃ f : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel
        (SecondaryActionData.componentImage s) f) ∨
      (Odd n ∧ ((n=3 ∧ ∃ name : ClassificationModels.SporadicName,
        (name = .m24 ∨ name = .ru) ∧
        Nonempty (SecondaryActionData.componentImage s ≃* name.Carrier)) ∨
        Nonempty (SecondaryActionData.componentImage s ≃* Janko4.Model))) :=
  SecondaryActionData.inspection_remaining_rows_after_core_analysis s hn
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) D h

/-- Natural coordinates supply generation for the remaining degree-two
odd ternary local analysis, including the nontrivial literal torus image. -/
theorem SecondaryActionData.odd_ternary_action_structure_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 p ∨
      ClassicalGroup.IsPSU (SecondaryActionData.componentImage s) 3 p) :
    SecondaryActionData.CoreImageCentral s ∧
      SecondaryActionData.torusImage s ≤ centralizer (SecondaryActionData.secondaryImage s : Set _) ∧
      SecondaryActionData.radicalImage s ≤ centralizer (SecondaryActionData.secondaryImage s : Set _) ∧
      SecondaryActionData.radicalImage s = SecondaryActionData.coreImage s ∧
      SecondaryActionData.torusImage s ≠ ⊥ :=
  SecondaryActionData.odd_ternary_action_structure s hn
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) hp ho hm

/-- Natural coordinates discharge generation in the catalogue with M₂₄ and Ru
excluded and J₄ restricted to degree five. The remaining local inspection
still has no model-selection or SourceAlternatives callback. -/
theorem SecondaryActionData.inspection_remaining_rows_after_sporadic_exponent_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (n=2 ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧
      (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 p ∨
        ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 p)) ∨
      (∃ f : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel
        (SecondaryActionData.componentImage s) f) ∨
      (n=5 ∧ Nonempty (SecondaryActionData.componentImage s ≃* Janko4.Model)) :=
  SecondaryActionData.inspection_remaining_rows_after_sporadic_exponent s hn
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) D h


/-- Natural coordinates discharge generation for the odd ternary exclusion.
The remaining actual inner models are binary rank-two or degree-five J₄. -/
theorem SecondaryActionData.inspection_remaining_rows_after_odd_ternary_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (∃ f : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel
      (SecondaryActionData.componentImage s) f) ∨
      (n=5 ∧ Nonempty (SecondaryActionData.componentImage s ≃* Janko4.Model)) :=
  SecondaryActionData.inspection_remaining_rows_after_odd_ternary s hn
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) D h
/-- Natural coordinates discharge generation after the binary rank-two
cover and order exclusions. Only larger PSL₃, odd-degree G₂ and degree-five
J₄ remain; the original quotient-action conventions are preserved. -/
theorem SecondaryActionData.inspection_remaining_rows_after_rank_two_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (∃ f : ℕ, 2≤f ∧ ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 (2^f)) ∨
      (Odd n ∧ ∃ f : ℕ, 2≤f ∧
        ClassificationModels.IsG2At (SecondaryActionData.componentImage s) (2^f)) ∨
      (n=5 ∧ Nonempty (SecondaryActionData.componentImage s ≃* Janko4.Model)) :=
  SecondaryActionData.inspection_remaining_rows_after_rank_two s hn
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) D h

/-- Natural coordinates discharge generation in the proper-parabolic G₂
exclusion, leaving only the binary PSL₃ and degree-five J₄ inspections. -/
theorem SecondaryActionData.inspection_remaining_rows_after_g2_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (∃ f : ℕ, 2≤f ∧ ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 (2^f)) ∨
      (n=5 ∧ Nonempty (SecondaryActionData.componentImage s ≃* Janko4.Model)) :=
  SecondaryActionData.inspection_remaining_rows_after_g2 s hn
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) D h

/-- Natural coordinates discharge generation in the refined source catalogue.
The binary linear branch is now on the full quotient with source degree two. -/
theorem SecondaryActionData.inspection_remaining_rows_after_linear_degree_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (n=2 ∧ ∃ f : ℕ, 2≤f ∧ Even f ∧
      ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 (2^f)) ∨
      (n=5 ∧ Nonempty (SecondaryActionData.componentImage s ≃* Janko4.Model)) :=
  SecondaryActionData.inspection_remaining_rows_after_linear_degree s hn
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) D h

/-- Natural coordinates discharge generation in the final linear reduction;
the degree-five J₄ proper-local case is the sole remaining model branch. -/
theorem SecondaryActionData.exceptional_or_jankoFour_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ((n=2 ∧ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4) ∧
      SecondaryActionData.torusImage s ⊓ MulAut.innerSubgroup
        (s.component ⧸ pCore 2 s.component) = ⊥) ∨
      (n=5 ∧ Nonempty (SecondaryActionData.componentImage s ≃* Janko4.Model)) :=
  SecondaryActionData.exceptional_or_jankoFour s D h hn
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq))

/-- The actual coordinate witness proves the original exceptional conclusion
whenever the source degree differs from five. -/
theorem SecondaryActionData.exceptional_of_coordinates_and_degree_ne_five
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) (hn5 : n≠5) :
    (n=2 ∧ (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)) ∧
      SecondaryActionData.torusImage s ⊓ MulAut.innerSubgroup
        (s.component ⧸ pCore 2 s.component) = ⊥ :=
  SecondaryActionData.exceptional_of_degree_ne_five s D h hn
    (s.action_generation_of_generation (m.radical_generation hn D s.core_eq)) hn5

/-- The complete coordinate sieve yields the binary linear model directly.
The literal outer torus clause is retained on the full component quotient. -/
theorem SecondaryActionData.linearFour_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (n=2 ∧ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4) ∧
      SecondaryActionData.torusImage s ⊓ MulAut.innerSubgroup
        (s.component ⧸ pCore 2 s.component) = ⊥ := by
  rcases SecondaryActionData.exceptional_or_jankoFour_of_coordinates s d m hn D h with
    ⟨⟨hn2,hm⟩,ho⟩ | ⟨hn5,⟨e⟩⟩
  · exact ⟨⟨hn2,hm⟩,ho⟩
  · subst n
    exact (SecondaryActionData.not_janko_four_inner_of_coordinates s d m D e).elim

/-- The corrected source sieve is complete on the original marked coordinates.
Both generation and every remaining model alternative are discharged. -/
theorem SecondaryActionData.exceptional_of_coordinates
    (s : SecondaryActionData c n) (d : MSData c n) (m : RootCoordinates d)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (n=2 ∧ (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)) ∧
      SecondaryActionData.torusImage s ⊓ MulAut.innerSubgroup
        (s.component ⧸ pCore 2 s.component) = ⊥ := by
  obtain ⟨⟨hn2,hm⟩,ho⟩ := SecondaryActionData.linearFour_of_coordinates s d m hn D h
  exact ⟨⟨hn2,Or.inl hm⟩,ho⟩

/-- The original parabolic and Sylow markings supply the coordinates for the
full-quotient exceptional conclusion, retaining the source torus action. -/
theorem SecondaryActionData.exceptional_of_marked_parabolic
    (s : SecondaryActionData c n) (d : MSData c n)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.linearThreeActor d.model) =
        Matrix.PSL3.LinearThree.lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.linearThreeActor d.model) =
        Matrix.PSL3.LinearThree.unipotentSL d.field.Carrier) :
    (n=2 ∧ (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)) ∧
      (s.torus.subgroupOf (rootNormalizer c)).map s.action ⊓ MulAut.innerSubgroup
        (s.component ⧸ pCore 2 s.component) = ⊥ := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  exact SecondaryActionData.exceptional_of_coordinates s d m hn D h

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
