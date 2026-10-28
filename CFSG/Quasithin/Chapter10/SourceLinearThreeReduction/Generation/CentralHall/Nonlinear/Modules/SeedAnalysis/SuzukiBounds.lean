module
public import Theory.Representation.Suzuki.CentralizerDisplacement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.RemainingCases

/-!
# The large-rank obstruction in the remaining original Suzuki branch

The exact quotient-action kernel is the original component centralizer.
Every nonidentity kernel element therefore has a faithful Suzuki displacement
module of degree at least 4(2m+1). A starred actor meeting this kernel has
rank at least 2(2m+1), and its kernel involution forces the unchanged moved
space W = [V_M,L] to have degree at least 8(2m+1).

Below either bound the actor is faithful, moves the original component,
and supplies moved minimality and both orientations of the separated seed.
The completed Hall calculations then give the exponent of the literal B.
The final original-context reduction retains the nonseparated even-linear
case and Suzuki support satisfying both bounds. Excluding those residual
cases and completing SeedAnalysisAt and SourceNonnormalCentralHallAt remain
with this source owner; no smallness premise is asserted unconditionally.
Source: Aschbacher--Smith D.3.9, 10.1.1 and10.2.3, printed pp.200--201,741,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance suzukiBoundsElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance suzukiBoundsFiniteDimensional :
    FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) := Module.Finite.of_finite

private theorem suzuki_component_fixed_eq_bot
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    fixedSpace (imageRepresentation (movedStabilizerAction D))
      (movedStabilizerComponentImage D) = ⊥ := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hsep := original_seed_separated_of_suzuki D c m hm e ht htn
  let ρ := movedStabilizerAction D
  let S := movedStabilizerComponentImage D
  let : Fact (0 < m) := ⟨hm⟩
  let : IsSimpleGroup S := ((originalMovedComponentEquiv D c.nonnormal).trans e).isSimpleGroup
  exact fixedSpace_eq_bot_of_normal_faithful_irreducible (imageRepresentation ρ)
    (imageRepresentation_injective ρ)
    (imageRepresentation_isIrreducible ρ (movedStabilizerAction_irreducible D c ht htn hsep))
    S ((Subgroup.nontrivial_iff_ne_bot S).mp inferInstance)

/-- Every nonidentity element of the literal Suzuki quotient-action kernel
moves at least the minimum faithful Suzuki degree. -/
theorem original_suzuki_kernel_displacement
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (a : actionImage (movedStabilizerAction D))
    (ha : a ∈ (originalMovedQuotientAction D c.nonnormal).ker) (hne : a ≠ 1) :
    4 * (2*m+1) ≤ fixedCodim (imageRepresentation (movedStabilizerAction D)) (zpowers a) :=
  Suzuki.centralizer_displacement_bound _ (imageRepresentation_injective _)
    (movedStabilizerComponentImage D) (suzuki_component_fixed_eq_bot D c m hm e) m hm
    ((originalMovedComponentEquiv D c.nonnormal).trans e) a
    ((originalMovedQuotientAction_kernel D c.nonnormal).le ha) hne

/-- A nontrivial starred actor kernel forces both a large actor and at least
twice the minimum Suzuki degree on the unchanged W = [V_M,L]. -/
theorem original_suzuki_starred_kernel_bounds
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hne : A ⊓ (originalMovedQuotientAction D c.nonnormal).ker ≠ ⊥) :
    2 * (2*m+1) ≤ rank A ∧
      8 * (2*m+1) ≤ Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) := by
  apply Suzuki.small_actor_centralizer_rank_bound _ (imageRepresentation_injective _)
    (movedStabilizerComponentImage D) (suzuki_component_fixed_eq_bot D c m hm e) m hm
    ((originalMovedComponentEquiv D c.nonnormal).trans e) A hA.1.2.1
  · exact (actionRatio_le_nat_iff _ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1)
  · rwa [←originalMovedQuotientAction_kernel D c.nonnormal]

/-- A small starred actor is faithful on the actual original Suzuki quotient.
The dimension alternative is on W itself, before any quotient or constituent. -/
theorem original_suzuki_starred_faithful_of_small
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hsmall : rank A < 2*(2*m+1) ∨
      Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) < 8*(2*m+1)) :
    Function.Injective ((originalMovedQuotientAction D c.nonnormal).comp A.subtype) := by
  have hker : A ⊓ (originalMovedQuotientAction D c.nonnormal).ker = ⊥ := by
    by_contra hn
    have hb := original_suzuki_starred_kernel_bounds D c m hm e A hA hn
    rcases hsmall with hsmall | hsmall <;> omega
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  apply Subtype.ext
  exact mem_bot.mp (hker.le ⟨a.property,ha⟩)

/-- The small-actor or small-degree branch constructs original moved minimality
without assuming a constituent, its invariance or its model. -/
theorem movedMinimal_of_suzuki_small_starred
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hsmall : rank A < 2*(2*m+1) ∨
      Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) < 8*(2*m+1)) :
    MovedMinimal D := by
  have hf := original_suzuki_starred_faithful_of_small D c m hm e A hA hsmall
  apply movedMinimal_of_suzuki_moving_starred_actor D c m hm e A hA
  intro hc
  apply hA.1.2.1.1
  apply bot_unique
  intro a ha
  have hker : originalMovedQuotientAction D c.nonnormal a = 1 :=
    (originalMovedQuotientAction_kernel D c.nonnormal).ge (hc ha)
  exact congrArg Subtype.val (hf (show
    ((originalMovedQuotientAction D c.nonnormal).comp A.subtype) ⟨a,ha⟩ =
      ((originalMovedQuotientAction D c.nonnormal).comp A.subtype) 1 from
    hker.trans (map_one _).symm))

/-- The same smallness criterion reconstructs every clause of the original
separated seed, retaining either orientation and the given exchanger. -/
theorem separatedSeed_of_suzuki_small_starred
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hsmall : rank A < 2*(2*m+1) ∨
      Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) < 8*(2*m+1))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    SeparatedSeed D t :=
  separatedSeed_of_separated_and_movedMinimal D
    (movedMinimal_of_suzuki_small_starred D c m hm e A hA hsmall) ht htn
    (original_seed_separated_of_suzuki D c m hm e ht htn)

/-- The literal Hall exponent follows whenever one starred actor has small
rank, or the original moved module has degree less than twice the Suzuki minimum. -/
theorem hall_exponent_of_suzuki_small_starred
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hsmall : rank A < 2*(2*m+1) ∨
      Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) < 8*(2*m+1)) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2^n+1 :=
  hall_exponent_of_suzuki_and_moved_minimal D c hnot m hm e
    (movedMinimal_of_suzuki_small_starred D c m hm e A hA hsmall)

/-- The original context constructs a starred actor, so a bound on the
literal moved dimension alone suffices for the Hall exponent. -/
theorem hall_exponent_of_suzuki_small_moved_degree
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hsmall : Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) <
      8*(2*m+1)) : ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2^n+1 := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hsep := original_seed_separated_of_suzuki D c m hm e ht htn
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff _).mpr
    (movedStabilizerAction_cubic_bound D c ht htn hsep)
  exact hall_exponent_of_suzuki_small_starred D c hnot m hm e A hA (Or.inr hsmall)

/-- The remaining Suzuki support retains its actual field parameter and
requires large rank for every starred actor, as well as large moved degree. -/
@[expose] def OriginalSuzukiLargeCentralizingSupport
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) : Prop :=
  ∃ (m : ℕ), 0 < m ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
    OriginalSuzukiCentralizingSupport D hn ∧
    8*(2*m+1) ≤ Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) ∧
    ∀ A : Subgroup (actionImage (movedStabilizerAction D)),
      A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) →
      2*(2*m+1) ≤ rank A

/-- Apply the displacement obstruction to the exact original Hall consumer.
Only the unchanged nonseparated even-linear case and large Suzuki support remain. -/
theorem original_hall_conclusion_or_large_remaining_cases
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      OriginalNonseparatedEvenCase D ∨ OriginalSuzukiLargeCentralizingSupport D c.nonnormal := by
  rcases original_hall_conclusion_or_remaining_cases D c with hh | he | hs
  · exact Or.inl hh
  · exact Or.inr (Or.inl he)
  · obtain ⟨m,hm,⟨e⟩⟩ := hs.1
    have hbound (A : Subgroup (actionImage (movedStabilizerAction D)))
        (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D))) :=
      original_suzuki_starred_kernel_bounds D c m hm e A hA
        (by rw [inf_eq_left.mpr (hs.2.1 A hA)]; exact hA.1.2.1.1)
    obtain ⟨A,J,hA,_⟩ := hs.2.2
    exact Or.inr (Or.inr ⟨m,hm,⟨e⟩,hs,(hbound A hA).2,fun A hA => (hbound A hA).1⟩)
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
