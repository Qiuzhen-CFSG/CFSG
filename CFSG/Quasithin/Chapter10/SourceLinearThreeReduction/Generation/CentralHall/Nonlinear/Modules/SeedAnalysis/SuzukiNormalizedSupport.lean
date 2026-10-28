module
public import CFSG.Quasithin.ChapterD.Section03.SuzukiNormalizedSupport
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SuzukiSupportRank

/-!
# Excluding normalized binary support in the original Suzuki Hall branch

The original moved representation is faithful and irreducible; the exact
quotient-action kernel is the centralizer of its marked Suzuki component.
The normalized-support theorem excludes odd-degree binary SL2 components
moved by a starred kernel actor. Even degrees have order divisible by five,
which is already excluded from this literal kernel. No constituent, isotypy
or extra actor-faithfulness hypothesis is imposed on the original context.

The last theorem applies this exclusion to the literal Hall subgroup B.
The remaining Suzuki witness retains its component orbit, both kernel
containments and all rank/degree bounds. Its binary SL2 support must be
exchanged. Exchanged and other Suzuki support, and the nonseparated even-linear
seed, remain open; this is not an unconditional SourceNonnormalCentralHallAt.
Source: Aschbacher--Smith D.3.9 and10.1.1--2,10.2.3,
printed pp.200--201,741--742,745; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
universe u
variable {Γ : Type u} [Group Γ] [Finite Γ] {T : Sylow 2 Γ} {L : Subgroup Γ}
  (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance normalizedSupportElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup Γ) :=
  source_original_full_moved_elementary D
local instance normalizedSupportFiniteDimensional :
    FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup Γ)) := Module.Finite.of_finite

/-- An original Suzuki kernel actor cannot have normalized odd-degree binary
SL2 support. The actual quotient marking and full actor are preserved. -/
theorem original_suzuki_no_normalized_odd_binary_support
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hJ : IsComponent _ J) (hJc : J ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hAJ : A ≤ normalizer (J : Set _)) (hJA : ⁅J,A⁆ = J)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n) (hodd : Odd n)
    (eJ : J ≃* SL(2,F)) : False := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hsep := original_seed_separated_of_suzuki D c m hm e ht htn
  let ρ := movedStabilizerAction D
  let K := movedStabilizerComponentImage D
  let : Fact (0 < m) := ⟨hm⟩
  let eK := (originalMovedComponentEquiv D c.nonnormal).trans e
  let : IsSimpleGroup K := eK.isSimpleGroup
  have hi := imageRepresentation_isIrreducible ρ (movedStabilizerAction_irreducible D c ht htn hsep)
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible (imageRepresentation ρ)
    (imageRepresentation_injective ρ) hi K ((Subgroup.nontrivial_iff_ne_bot K).mp inferInstance)
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : IsSimpleGroup SL(2,F) := (Theory.PSL2.sl2QuotientEquiv F).isSimpleGroup
  let : IsSimpleGroup J := eJ.isSimpleGroup
  exact ChapterD.suzuki_no_normalized_odd_binary_support (imageRepresentation ρ)
    (imageRepresentation_injective ρ) hi K hfix m hm eK J A hJ
    (movedStabilizerImage_component_sqtk D J hJ) hA
    (le_centralizer_iff.mp (hJc.trans (originalMovedQuotientAction_kernel D c.nonnormal).le))
    (le_centralizer_iff.mp (hAc.trans (originalMovedQuotientAction_kernel D c.nonnormal).le))
    hAJ hJA eJ n hn hF hodd

/-- Five-freeness removes the even binary degrees; the multiplicity argument
removes the odd ones. Thus normalized binary SL2 support is impossible. -/
theorem original_suzuki_no_normalized_binary_support
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hJ : IsComponent _ J) (hJc : J ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hAJ : A ≤ normalizer (J : Set _)) (hJA : ⁅J,A⁆ = J)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n) (eJ : J ≃* SL(2,F)) : False := by
  by_cases ho : Odd n
  · exact original_suzuki_no_normalized_odd_binary_support D c m hm e A J hA hAc hJ hJc
      hAJ hJA n hn hF ho eJ
  · apply original_suzuki_no_five_support D c m hm e J hJc
    rw [Nat.card_congr eJ.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
    apply dvd_mul_of_dvd_right
    rw [←pow_mul]
    apply (by decide : 5 ∣ 2^4-1).trans
    apply Nat.pow_sub_one_dvd_pow_sub_one
    obtain ⟨k,hk⟩ := Nat.not_odd_iff_even.mp ho
    exact ⟨k,by omega⟩

/-- Every binary SL2 support in the remaining original Suzuki configuration
is exchanged by the starred actor, not merely large. -/
@[expose] def OriginalSuzukiNoNormalizedBinarySupport
    (hn : ¬ (T : Subgroup Γ) ≤ normalizer (L : Set Γ)) : Prop :=
  OriginalSuzukiSupportRankCase D hn ∧
  ∃ (m : ℕ), 0 < m ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
    ∃ A J : Subgroup (actionImage (movedStabilizerAction D)),
      A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
      A ≤ (originalMovedQuotientAction D hn).ker ∧
      IsComponent _ J ∧ 3 ∣ Nat.card J ∧ Nat.Coprime 5 (Nat.card J) ∧
      J ≤ (originalMovedQuotientAction D hn).ker ∧
      componentOrbit J A ≤ (originalMovedQuotientAction D hn).ker ∧
      componentOrbit J A ≠ ⊥ ∧ ⁅componentOrbit J A,A⁆ = componentOrbit J A ∧
      2*(2*m+1) ≤ primeRank 2 (MulAut J)+1 ∧
      (∀ n : ℕ, 2 ≤ n → Nonempty (J ≃* SL(2,GaloisField 2 n)) →
        ¬ A ≤ normalizer (J : Set _))

/-- The normalized binary-support exclusion is applied to the literal Hall
consumer, retaining both previous residual configurations and every bound. -/
theorem original_hall_conclusion_or_no_normalized_binary_support
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      OriginalNonseparatedEvenCase D ∨ OriginalSuzukiNoNormalizedBinarySupport D c.nonnormal := by
  rcases original_hall_conclusion_or_support_rank_cases D c with hh | he | hs
  · exact Or.inl hh
  · exact Or.inr (Or.inl he)
  · have hsave := hs
    obtain ⟨m,hm,⟨e⟩,_,A,J,hA,hAc,hJ,hthree,hfive,hJc,hXc,hXn,hXA,hr⟩ := hs
    refine Or.inr (Or.inr ⟨hsave,m,hm,⟨e⟩,A,J,hA,hAc,hJ,hthree,hfive,hJc,hXc,hXn,hXA,hr,?_⟩)
    intro n hn ⟨eJ⟩ hAJ
    have heq : componentOrbit J A = J :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer J A J le_rfl hAJ) (le_componentOrbit J A)
    exact original_suzuki_no_normalized_binary_support D c m hm e A J hA hAc hJ hJc hAJ
      (by simpa only [heq] using hXA) n hn (GaloisField.card 2 n (by omega)) eJ

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
