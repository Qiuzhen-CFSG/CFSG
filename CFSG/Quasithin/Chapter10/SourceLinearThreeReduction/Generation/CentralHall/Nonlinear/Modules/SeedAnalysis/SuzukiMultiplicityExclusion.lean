module
public import CFSG.Quasithin.ChapterD.Section03.SuzukiNaturalMultiplicity
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SuzukiCoprimeSupport

/-!
# Closing the original Suzuki central Hall branch

The remaining normal support has an invariant natural SL₃ constituent over
an odd-degree field. Its literal orbit under the original Suzuki component
supplies a faithful multiplicity action over that same field of dimension
at most four. The exact original quotient kernel makes the field degree
coprime to the Suzuki degree, so the existing primitive-divisor obstruction
requires dimension at least 4(2m+1). This excludes the remaining support.

The application retains the full starred actor, the original component orbit,
both exact quotient-kernel containments, and the original Hall subgroup B.
It proves the Hall exponent conclusion for every original Suzuki marking.
The complete Hall dichotomy now leaves only the nonseparated even-linear
seed; its exclusion and SourceNonnormalCentralHallAt assembly remain open.

Source: Aschbacher--Smith D.3.9,10.1.1--2 and the centralizing branch of
10.2.3, printed pp.200--201,741--742,745; refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open ChapterB.QuasisimpleSource
universe u
variable {Γ : Type u} [Group Γ] [Finite Γ] {T : Sylow 2 Γ} {L : Subgroup Γ}
  (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance naturalMultiplicityElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup Γ) :=
  source_original_full_moved_elementary D
local instance naturalMultiplicityFiniteDimensional :
    FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup Γ)) := Module.Finite.of_finite

/-- The actual small faithful multiplicity action excludes the last Suzuki support. -/
theorem original_suzuki_no_natural_linearThree_support
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hJ : IsComponent _ J) (hJc : J ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hXn : componentOrbit J A ≠ ⊥) (hXA : ⁅componentOrbit J A,A⁆ = componentOrbit J A)
    (F : BinaryField) (ho : Odd F.degree)
    (R : Submodule (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup Γ)))
    (hJR : J ≤ subspaceStabilizer (imageRepresentation (movedStabilizerAction D)) R)
    (hAR : A ≤ subspaceStabilizer (imageRepresentation (movedStabilizerAction D)) R)
    (a : ActionEquiv
      (invariantSubspace (imageRepresentation (movedStabilizerAction D)) J R hJR).toRepresentation
      (linearNatural F 3)) : False := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hsep := original_seed_separated_of_suzuki D c m hm e ht htn
  let ρ := movedStabilizerAction D
  let K := movedStabilizerComponentImage D
  let : Fact (0 < m) := ⟨hm⟩
  let ek := originalMovedComponentEquiv D c.nonnormal
  let eK := ek.trans e
  let : IsSimpleGroup K := eK.isSimpleGroup
  have hi := imageRepresentation_isIrreducible ρ (movedStabilizerAction_irreducible D c ht htn hsep)
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible (imageRepresentation ρ)
    (imageRepresentation_injective ρ) hi K ((Subgroup.nontrivial_iff_ne_bot K).mp inferInstance)
  let : J.Normal := original_suzuki_component_support_normal D c m hm e A J hA hAc hJ hJc hXn hXA
  let : IsQuasisimple J := hJ.2
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  let : Nontrivial J := (QuotientGroup.mk'_surjective (center J)).nontrivial
  have hJfix := fixedSpace_eq_bot_of_normal_faithful_irreducible (imageRepresentation ρ)
    (imageRepresentation_injective ρ) hi J ((Subgroup.nontrivial_iff_ne_bot J).mp inferInstance)
  have hAJ : A ≤ normalizer (J : Set _) := le_top.trans_eq J.normalizer_eq_top.symm
  have heq : componentOrbit J A = J :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer J A J le_rfl hAJ) (le_componentOrbit J A)
  have hJA : ⁅J,A⁆ = J := by simpa only [heq] using hXA
  have hiR := ExtensionConsequences.irreducible_of_equiv a
    (ExtensionConsequences.linearNatural_irreducible F (by decide : 2 ≤ 3))
  have hnot : ¬ R ≤ fixedSpace (imageRepresentation ρ) J := by
    intro hh
    exact ((Subrepresentation.irreducible_iff_isAtom _).mp hiR).ne_bot
      (Subrepresentation.toSubmodule_injective (bot_unique (hh.trans hJfix.le)))
  have hmove : ¬ R ≤ fixedSpace (imageRepresentation ρ) A := by
    intro hh
    exact hnot (hJA ▸ le_fixedSpace_commutator_of_invariant (imageRepresentation ρ) hJR hh)
  obtain ⟨r,hr,f,hf⟩ := ChapterD.suzuki_natural_support_small_faithful_action
    (imageRepresentation ρ) K hfix m hm eK J A hA
    (le_centralizer_iff.mp (hJc.trans (originalMovedQuotientAction_kernel D c.nonnormal).le))
    (le_centralizer_iff.mp (hAc.trans (originalMovedQuotientAction_kernel D c.nonnormal).le))
    F ho R hJR hAR hmove a
  exact original_suzuki_no_small_support_scalar_action D c m hm e J hJc F ho a.groupEquiv
    F (dvd_mul_left _ _) r (by omega) (f.comp ek.symm.toMonoidHom) (hf.comp ek.symm.injective)

/-- The literal Hall exponent for every original Suzuki field degree, without extra premises. -/
theorem hall_exponent_of_original_suzuki
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2^n+1 := by
  have hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) := by
    rintro ⟨j⟩
    apply BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m hm
    rw [←Nat.card_congr e.toEquiv,Nat.card_congr j.toEquiv,
      Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
    norm_num
  rcases hall_exponent_or_suzuki_centralizing_component_support D c hnot m hm e with hh | hs
  · exact hh
  · obtain ⟨hcentral,A,J,hA,hJ,_hJthree,hJc,_hXc,hXn,hXA⟩ := hs
    obtain ⟨F,ho,R,hJR,hAR,⟨a⟩⟩ := original_suzuki_support_natural_linearThree D c m hm e
      A J hA (hcentral A hA) hJ hJc hXn hXA
    exact (original_suzuki_no_natural_linearThree_support D c m hm e A J hA
      (hcentral A hA) hJ hJc hXn hXA F ho R hJR hAR a).elim

/-- All original Suzuki alternatives are discharged; only the even-linear seed remains. -/
theorem original_hall_conclusion_or_nonseparated_even
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨ OriginalNonseparatedEvenCase D := by
  rcases original_hall_conclusion_or_remaining_cases D c with hh | he | hs
  · exact Or.inl hh
  · exact Or.inr he
  · obtain ⟨⟨m,hm,⟨e⟩⟩,_⟩ := hs
    obtain ⟨n,_hn,hdiv⟩ := hall_exponent_of_original_suzuki D c m hm e
    exact Or.inl (Or.inr ⟨n,hdiv⟩)
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
