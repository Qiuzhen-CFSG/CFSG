module
public import CFSG.Quasithin.ChapterD.Section03.SuzukiStrongSupport
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SuzukiExchangedSupport

/-!
# Natural SL₃ support in the original Suzuki Hall configuration

The original quotient-action kernel has order prime to five, and its remaining
support components are normal in the full moved action image. A commuting
Suzuki component forces a strong offender on a constructed support--actor
constituent. The complete B.5.1 sieve and the SL₃ central-cover theorem identify
that constituent as natural SL₃ over a field of odd binary degree.

The application retains the literal Hall subgroup, both original kernel
containments, the full starred actor, its component orbit, and the earlier
rank and degree bounds. Excluding this natural SL₃ support and the
nonseparated even-linear seed remains necessary for the source theorem.

Source: Aschbacher--Smith B.5.1, D.3.9, and the module analysis for
10.1.1--2 and 10.2.3, printed pp.741--742,745 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open ChapterB.QuasisimpleSource
universe u
variable {Γ : Type u} [Group Γ] [Finite Γ] {T : Sylow 2 Γ} {L : Subgroup Γ}
  (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance linearThreeSupportElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup Γ) :=
  source_original_full_moved_elementary D
local instance linearThreeSupportFiniteDimensional :
    FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup Γ)) := Module.Finite.of_finite

/-- The remaining original Suzuki support has an actual invariant natural SL₃
constituent over an odd-degree field, with the full starred actor preserved. -/
theorem original_suzuki_support_natural_linearThree
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hJ : IsComponent _ J) (hJc : J ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hXn : componentOrbit J A ≠ ⊥) (hXA : ⁅componentOrbit J A,A⁆ = componentOrbit J A) :
    ∃ F : BinaryField, Odd F.degree ∧
      ∃ R : Submodule (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup Γ)),
      ∃ hJR : J ≤ subspaceStabilizer (imageRepresentation (movedStabilizerAction D)) R,
        A ≤ subspaceStabilizer (imageRepresentation (movedStabilizerAction D)) R ∧
        Nonempty (ActionEquiv
          (invariantSubspace (imageRepresentation (movedStabilizerAction D)) J R hJR).toRepresentation
          (linearNatural F 3)) := by
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
  let : J.Normal := original_suzuki_component_support_normal D c m hm e A J hA hAc hJ hJc hXn hXA
  let : IsQuasisimple J := hJ.2
  have hJ2 : pCore 2 J = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hJ.1,movedStabilizerImage_twoCore_eq_bot D c ht htn hsep]
    exact J.subtype.ker_eq_bot_iff.mpr J.subtype_injective
  have hAJ : A ≤ normalizer (J : Set _) := le_top.trans_eq J.normalizer_eq_top.symm
  have heq : componentOrbit J A = J :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer J A J le_rfl hAJ) (le_componentOrbit J A)
  exact ChapterD.suzuki_normal_support_natural_linearThree (imageRepresentation ρ)
    (imageRepresentation_injective ρ) hi K hfix m hm eK J A
    (movedStabilizerImage_component_sqtk D J hJ) hJ2
    (original_suzuki_no_five_support D c m hm e J hJc) hA
    (le_centralizer_iff.mp (hJc.trans (originalMovedQuotientAction_kernel D c.nonnormal).le))
    (le_centralizer_iff.mp (hAc.trans (originalMovedQuotientAction_kernel D c.nonnormal).le))
    (by simpa only [heq] using hXA)

/-- The normal support is now marked by a genuine natural SL₃ constituent.
Both exact kernel containments, the component orbit, and all earlier rank and
degree restrictions remain in the original configuration. -/
@[expose] def OriginalSuzukiNaturalLinearThreeSupport
    (hn : ¬ (T : Subgroup Γ) ≤ normalizer (L : Set Γ)) : Prop :=
  OriginalSuzukiNormalNonbinarySupport D hn ∧
  ∃ (m : ℕ), 0 < m ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
    ∃ A J : Subgroup (actionImage (movedStabilizerAction D)),
      A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
      A ≤ (originalMovedQuotientAction D hn).ker ∧
      IsComponent _ J ∧ J.Normal ∧ 3 ∣ Nat.card J ∧ Nat.Coprime 5 (Nat.card J) ∧
      J ≤ (originalMovedQuotientAction D hn).ker ∧
      componentOrbit J A ≤ (originalMovedQuotientAction D hn).ker ∧
      componentOrbit J A ≠ ⊥ ∧ ⁅componentOrbit J A,A⁆ = componentOrbit J A ∧
      ⁅J,A⁆ = J ∧ 2*(2*m+1) ≤ primeRank 2 (MulAut J) ∧
      (∀ n : ℕ, 2 ≤ n → ¬ Nonempty (J ≃* SL(2,GaloisField 2 n))) ∧
      ∃ F : BinaryField, Odd F.degree ∧
        ∃ R : Submodule (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup Γ)),
        ∃ hJR : J ≤ subspaceStabilizer (imageRepresentation (movedStabilizerAction D)) R,
          A ≤ subspaceStabilizer (imageRepresentation (movedStabilizerAction D)) R ∧
          Nonempty (ActionEquiv
            (invariantSubspace (imageRepresentation (movedStabilizerAction D)) J R hJR).toRepresentation
            (linearNatural F 3))

/-- For the literal Hall subgroup, the only Suzuki support still to exclude
is normal odd-degree natural SL₃ support. No constituent premise is added. -/
theorem original_hall_conclusion_or_natural_linearThree_support
    {H : Subgroup Γ} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      OriginalNonseparatedEvenCase D ∨ OriginalSuzukiNaturalLinearThreeSupport D c.nonnormal := by
  rcases original_hall_conclusion_or_normal_nonbinary_support D c with hh | he | hs
  · exact Or.inl hh
  · exact Or.inr (Or.inl he)
  · have hsave := hs
    obtain ⟨_,m,hm,⟨e⟩,A,J,hA,hAc,hJ,hnormal,hthree,hfive,hJc,hXc,hXn,hXA,hJA,hr,hnob⟩ := hs
    exact Or.inr (Or.inr ⟨hsave,m,hm,⟨e⟩,A,J,hA,hAc,hJ,hnormal,hthree,hfive,hJc,
      hXc,hXn,hXA,hJA,hr,hnob,
      original_suzuki_support_natural_linearThree D c m hm e A J hA hAc hJ hJc hXn hXA⟩)
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
