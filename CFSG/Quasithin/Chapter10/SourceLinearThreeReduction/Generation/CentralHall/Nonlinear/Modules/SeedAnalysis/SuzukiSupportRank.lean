module
public import CFSG.Quasithin.ChapterD.Section03.SuzukiSupportRank
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SuzukiPrime
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import Theory.GroupTheory.ElementaryPairActionRank

/-!
# Support-image ranks in the original Suzuki Hall branch

A starred actor in the exact original quotient-action kernel centralizes
its Suzuki component. On a homogeneous support orbit, the actor's pointwise
support kernel acts trivially. Thus the Suzuki displacement bound forces
rank at least 2(2m+1) in its actual conjugation image on every nontrivial
moved perfect support.

For a component exchanged by the elementary actor, the image rank is at
most the component automorphism two-rank plus one. This excludes all
odd-field PSL2 support, including exchanged support and outer actors.
Binary SL2 support has field degree at least 2(2m+1) when normalized, and
at least 2(2m+1)-1 when exchanged.

The last theorem applies these bounds to the literal Hall subgroup B,
retaining the actual component marking, both quotient-kernel containments,
and the three-divisible, five-free moved orbit. Large even-field support
and the nonseparated even-linear seed remain unresolved configurations;
these bounds do not prove their exclusion or SourceNonnormalCentralHallAt.
Source: Aschbacher--Smith D.3.9, 10.1.1--2 and 10.2.3,
printed pp.200--201,741--742,745; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules

universe u
variable {Γ : Type u} [Group Γ] [Finite Γ] {T : Sylow 2 Γ} {L : Subgroup Γ}
  (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance supportRankElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup Γ) :=
  source_original_full_moved_elementary D
local instance supportRankFiniteDimensional :
    FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup Γ)) := Module.Finite.of_finite

/-- The actual image on every normalized perfect support has large rank. -/
theorem original_suzuki_support_image_rank
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A X : Subgroup (actionImage (movedStabilizerAction D))) [Group.IsPerfect X]
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hXn : X ≠ ⊥) (hAX : A ≤ normalizer (X : Set _)) (hXA : ⁅X,A⁆ = X) :
    2 * (2*m+1) ≤ rank (X.normalizerMonoidHom.comp (inclusion hAX)).range := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hsep := original_seed_separated_of_suzuki D c m hm e ht htn
  let ρ := movedStabilizerAction D
  let K := movedStabilizerComponentImage D
  let : Fact (0 < m) := ⟨hm⟩
  let eK := (originalMovedComponentEquiv D c.nonnormal).trans e
  let : IsSimpleGroup K := eK.isSimpleGroup
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible (imageRepresentation ρ)
    (imageRepresentation_injective ρ)
    (imageRepresentation_isIrreducible ρ (movedStabilizerAction_irreducible D c ht htn hsep))
    K ((Subgroup.nontrivial_iff_ne_bot K).mp inferInstance)
  exact ChapterD.suzuki_centralizing_support_image_rank (imageRepresentation ρ)
    (imageRepresentation_injective ρ) K hfix m hm eK A X hA
    (hAc.trans (originalMovedQuotientAction_kernel D c.nonnormal).le) hXn hAX hXA

/-- Every normalized perfect support of a kernel actor has large automorphism
two-rank. The actor and quotient kernel are the original ones. -/
theorem original_suzuki_normalized_support_rank
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A X : Subgroup (actionImage (movedStabilizerAction D))) [Group.IsPerfect X]
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hXn : X ≠ ⊥) (hAX : A ≤ normalizer (X : Set _)) (hXA : ⁅X,A⁆ = X) :
    2 * (2*m+1) ≤ primeRank 2 (MulAut X) := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hsep := original_seed_separated_of_suzuki D c m hm e ht htn
  let ρ := movedStabilizerAction D
  let K := movedStabilizerComponentImage D
  let : Fact (0 < m) := ⟨hm⟩
  let eK := (originalMovedComponentEquiv D c.nonnormal).trans e
  let : IsSimpleGroup K := eK.isSimpleGroup
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible (imageRepresentation ρ)
    (imageRepresentation_injective ρ)
    (imageRepresentation_isIrreducible ρ (movedStabilizerAction_irreducible D c ht htn hsep))
    K ((Subgroup.nontrivial_iff_ne_bot K).mp inferInstance)
  exact ChapterD.suzuki_centralizing_support_rank (imageRepresentation ρ)
    (imageRepresentation_injective ρ) K hfix m hm eK A X hA
    (hAc.trans (originalMovedQuotientAction_kernel D c.nonnormal).le) hXn hAX hXA

/-- Odd-field PSL2 cannot be a normalized perfect support of an original
Suzuki kernel actor, including its diagonal and field automorphisms. -/
theorem original_suzuki_no_normalized_odd_linear_support
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A X : Subgroup (actionImage (movedStabilizerAction D))) [Group.IsPerfect X]
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hXn : X ≠ ⊥) (hAX : A ≤ normalizer (X : Set _)) (hXA : ⁅X,A⁆ = X)
    {F : Type*} [Field F] [Finite F]
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F)) (hlarge : 3 < Nat.card F)
    (eX : X ≃* PSL(2,F)) : False := by
  have hl := original_suzuki_normalized_support_rank D c m hm e A X hA hAc hXn hAX hXA
  rw [primeRank_equiv 2 (MulAut.congr eX)] at hl
  have hu := Theory.PSL2.odd_automorphism_two_rank F hF hlarge
  omega

/-- A normalized binary SL2 support must have degree at least twice the
original Suzuki field degree. -/
theorem original_suzuki_even_support_degree
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A X : Subgroup (actionImage (movedStabilizerAction D))) [Group.IsPerfect X]
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hXn : X ≠ ⊥) (hAX : A ≤ normalizer (X : Set _)) (hXA : ⁅X,A⁆ = X)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n) (eX : X ≃* SL(2,F)) :
    2*(2*m+1) ≤ n := by
  have hl := original_suzuki_normalized_support_rank D c m hm e A X hA hAc hXn hAX hXA
  rw [primeRank_equiv 2 (MulAut.congr eX)] at hl
  exact hl.trans (Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hF)

/-- The rank obstruction holds for the original component in both the
normalized and exchanged cases. No faithfulness on the support is assumed. -/
theorem original_suzuki_component_support_rank
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hJ : IsComponent _ J) (hXn : componentOrbit J A ≠ ⊥)
    (hXA : ⁅componentOrbit J A,A⁆ = componentOrbit J A) :
    2*(2*m+1) ≤ primeRank 2 (MulAut J)+1 := by
  let := hJ.2
  by_cases hAJ : A ≤ normalizer (J : Set _)
  · have heq : componentOrbit J A = J :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer J A J le_rfl hAJ) (le_componentOrbit J A)
    have hl := original_suzuki_normalized_support_rank D c m hm e A J hA hAc
      (heq ▸ hXn) hAJ (by simpa only [heq] using hXA)
    omega
  · let : IsElementaryAbelian 2 A := hA.1.2.1.2
    let : Group.IsPerfect (componentOrbit J A) := hJ.orbit_isPerfect A
    have hl := original_suzuki_support_image_rank D c m hm e A (componentOrbit J A)
      hA hAc hXn (le_normalizer_componentOrbit J A) hXA
    have hlay := movedStabilizerImage_semisimple_sqtk D
      (componentLayer (actionImage (movedStabilizerAction D))) componentLayer_idempotent
    exact hl.trans (elementary_component_exchanged_orbit_action_rank J A hJ
      hlay.stronglyQuasithin hAJ)

/-- Odd-field PSL2 support is excluded in both its normalized and exchanged
orientations, with every outer actor retained. -/
theorem original_suzuki_no_odd_linear_component_support
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hJ : IsComponent _ J) (hXn : componentOrbit J A ≠ ⊥)
    (hXA : ⁅componentOrbit J A,A⁆ = componentOrbit J A)
    {F : Type*} [Field F] [Finite F]
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F)) (hlarge : 3 < Nat.card F)
    (eJ : J ≃* PSL(2,F)) : False := by
  have hl := original_suzuki_component_support_rank D c m hm e A J hA hAc hJ hXn hXA
  rw [primeRank_equiv 2 (MulAut.congr eJ)] at hl
  have hu := Theory.PSL2.odd_automorphism_two_rank F hF hlarge
  omega

/-- The binary field degree is large even when the original support is exchanged. -/
theorem original_suzuki_even_component_support_degree
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hJ : IsComponent _ J) (hXn : componentOrbit J A ≠ ⊥)
    (hXA : ⁅componentOrbit J A,A⁆ = componentOrbit J A)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n) (eJ : J ≃* SL(2,F)) :
    2*(2*m+1) ≤ n+1 := by
  have hl := original_suzuki_component_support_rank D c m hm e A J hA hAc hJ hXn hXA
  rw [primeRank_equiv 2 (MulAut.congr eJ)] at hl
  have hu := Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hF
  omega

/-- The remaining original Suzuki configuration has a genuine support
component of large automorphism two-rank, even when exchanged. -/
@[expose] def OriginalSuzukiSupportRankCase
    (hn : ¬ (T : Subgroup Γ) ≤ normalizer (L : Set Γ)) : Prop :=
  ∃ (m : ℕ), 0 < m ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
    OriginalSuzukiLargeCentralizingSupport D hn ∧
    ∃ A J : Subgroup (actionImage (movedStabilizerAction D)),
      A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
      A ≤ (originalMovedQuotientAction D hn).ker ∧
      IsComponent _ J ∧ 3 ∣ Nat.card J ∧ Nat.Coprime 5 (Nat.card J) ∧
      J ≤ (originalMovedQuotientAction D hn).ker ∧
      componentOrbit J A ≤ (originalMovedQuotientAction D hn).ker ∧
      componentOrbit J A ≠ ⊥ ∧ ⁅componentOrbit J A,A⁆ = componentOrbit J A ∧
      2*(2*m+1) ≤ primeRank 2 (MulAut J)+1

/-- Apply the support rank obstruction to the literal Hall conclusion.
No small actor or constituent hypothesis has been added to the source context. -/
theorem original_hall_conclusion_or_support_rank_cases
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      OriginalNonseparatedEvenCase D ∨ OriginalSuzukiSupportRankCase D c.nonnormal := by
  rcases original_hall_conclusion_or_five_free_remaining_cases D c with hh | he | ⟨hs,hfive⟩
  · exact Or.inl hh
  · exact Or.inr (Or.inl he)
  · obtain ⟨m,hm,⟨e⟩,hsupport,hbounds⟩ := hs
    obtain ⟨A,J,hA,hJ,hthree,hJK,hXK,hXn,hXA⟩ := hsupport.2.2
    have hAC := hsupport.2.1 A hA
    have hJfive := hfive.of_dvd_right (card_dvd_of_le hJK)
    have hr := original_suzuki_component_support_rank D c m hm e A J hA hAC hJ hXn hXA
    exact Or.inr (Or.inr ⟨m,hm,⟨e⟩,⟨m,hm,⟨e⟩,hsupport,hbounds⟩,
      A,J,hA,hAC,hJ,hthree,hJfive,hJK,hXK,hXn,hXA,hr⟩)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
