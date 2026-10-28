module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Escape
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.HallConjugacy
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OddCore
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.Reduction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OrdinarySource
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.HeldSource
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.CoveringClosure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SmallRankApplication
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.CatalogueExclusions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalGeometry
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.BinaryClosure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.HallInspection
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.QuotientFixation
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.PairImage
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.NonFFFixedSpan
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.NaturalRows

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.MovingApplication
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.RemainingApplication
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.ClassicalRemainder
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.UnitaryRemainder
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.HallApplication
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.QuietApplication
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.ReselectionApplication
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.LocalApplication
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.LocalConstraints
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.LocalSource

/-!
# The original nonnormal non-A₅ Hall-faithfulness theorem

`source_nonnormalHallFaithful` proves the exact arbitrary-Hall contract.
An intrinsic Cartan kernel supplies an elementary odd actor with escaping
normalizer. The moving-Thompson branch fixes the full module. In the quiet
branch the kernel fixes the nonzero Sylow-fixed orbit, which is fully moved
by L₀. Its local normalizer theorem now excludes every actual Theorem B
component, retaining the full centers and original quotient maps. Thus the
kernel is trivial; Hall conjugacy transfers this to every specified Hall
subgroup of the original overlap.

The absorbed full-module-fixation contract is also discharged, with the
original setup as witness. Earlier conditional interfaces remain available.
No fixed-space generation or irreducibility assumption is used in the quiet
branch, and no model or normalizer callback remains in the source theorem.

Source: Aschbacher--Smith 10.2.3(2), printed p.745, using
4.4.3, 4.4.13--14 and 10.1.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The exact arbitrary-Hall contract follows from module selection and the
nonnormal specialization of 4.4.3; 4.4.13 is discharged by its proved theorem. -/
theorem source_nonnormalHallFaithful_of_module_and_normalizer
    (hmodule : SourceNonnormalHallKernelModuleAt T)
    (hnormalizer : SourceNonnormalOddKernelNormalizerAt T) :
    SourceNonnormalHallFaithfulAt T := by
  intro hmany L D hmin hn ha H hH hlarge B hBM hB _ _
  obtain ⟨hP, f, _, _, d, he, hperm, _⟩ :=
    source_hstar_cartan_data_of_generation_gt_one D hH hlarge
  have hYM := he ▸ d.hall_le
  have hYHall := he ▸ d.hall
  obtain ⟨E, hE⟩ := hmodule hmany L D hmin hn ha H hH hlarge
    d.witness.abelianGroup hYM hYHall d.witness.abelian hperm
  have hfaith : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H = ⊥ := by
    by_contra hk
    obtain ⟨p, A, hp, ho, hA, hAe, hAY, hAC, hAT, hout⟩ :=
      source_hstar_hall_kernel_escaping_elementary D hH hlarge hP d hk
    exact hout (hnormalizer hmany L E hn ha p hp ho A hA hAe hAC
      ((le_inf hAY hAC).trans hE) hAT)
  exact source_hall_sectionKernel_faithful_of_hall_conjugacy
    (M := D.maximalLocal) (X := localOrbit T L) le_rfl
    (he ▸ d.maximal_solvable) hBM hB hYHall hfaith

/-- Conditional source assembly after discharging the complete moving-local-
Thompson branch. Fixed-space generation is needed only in the quiet branch;
the remaining normalizer theorem is still an independent source obligation. -/
theorem source_nonnormalHallFaithful_of_quiet_generation_and_normalizer
    (hgen : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        D.IsMinimalFullModule →
        ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
        Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
          centralizer (D.moduleSubgroup : Set G) →
        D.fullModule = conjugateSpanBy
          (D.fullModule ⊓ centralizer (T : Set G)) (localOrbit T L))
    (hnormalizer : SourceNonnormalOddKernelNormalizerAt T) :
    SourceNonnormalHallFaithfulAt T :=
  source_nonnormalHallFaithful_of_module_and_normalizer
    (source_nonnormalHallKernelModule_of_quiet_fixed_generation hgen) hnormalizer

/-- With the complete nonnormal normalizer theorem, only module selection remains. -/
theorem source_nonnormalHallFaithful_of_module
    (hmodule : SourceNonnormalHallKernelModuleAt T) : SourceNonnormalHallFaithfulAt T :=
  source_nonnormalHallFaithful_of_module_and_normalizer hmodule
    source_nonnormalOddKernelNormalizer

/-- Quiet Sylow-fixed generation is the sole remaining input to the exact source contract. -/
theorem source_nonnormalHallFaithful_of_quiet_generation
    (hgen : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        D.IsMinimalFullModule →
        ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
        Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
          centralizer (D.moduleSubgroup : Set G) →
        D.fullModule = conjugateSpanBy
          (D.fullModule ⊓ centralizer (T : Set G)) (localOrbit T L)) :
    SourceNonnormalHallFaithfulAt T :=
  source_nonnormalHallFaithful_of_module
    (source_nonnormalHallKernelModule_of_quiet_fixed_generation hgen)

/-- An alternative to fixed-space generation: it suffices to normalize the
actual displacement of each elementary odd kernel actor in the quiet branch.
All normalizer exclusions and the moving branch are discharged. -/
theorem source_nonnormalHallFaithful_of_quiet_elementary_displacement
    (hdisp : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        D.IsMinimalFullModule →
        ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
        Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
          centralizer (D.moduleSubgroup : Set G) →
        ∀ (p : ℕ), p.Prime → Odd p →
          Nat.Coprime p (Nat.card (L ⧸ pCore 2 L)) →
          ∀ A : Subgroup G, A ≠ ⊥ → IsElementaryAbelian p A →
            A ≤ sectionCentralizer (localOrbit T L) →
            A ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) →
            (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) →
            (T : Subgroup G) ≤ normalizer (⁅D.fullModule,A⁆ : Subgroup G)) :
    SourceNonnormalHallFaithfulAt T := by
  intro hmany L D hmin hn hna H hH hlarge B hBM hB _ _
  by_cases hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)
  · obtain ⟨hP,_,_,_,d,he,_,_⟩ :=
      source_hstar_cartan_data_of_generation_gt_one D hH hlarge
    have hfaith : d.witness.abelianGroup ⊓
        (sectionCentralizer (localOrbit T L)).subgroupOf H = ⊥ := by
      by_contra hk
      obtain ⟨p,A,hp,ho,hcop,hne,hA,hAB,hAC,hAT,_,_,hbad⟩ :=
        source_quiet_hall_kernel_escaping_displacement D hn hJ hH hlarge hP d hk
      exact hbad (hdisp hmany L D hmin hn hna hJ p hp ho hcop A hne hA hAC
        ((hAB.trans (map_subtype_le _)).trans
          (source_hstar_centralizes_omega_of_local_thompson_centralizes D hJ hH)) hAT)
    exact source_hall_sectionKernel_faithful_of_hall_conjugacy
      (M := D.maximalLocal) (X := localOrbit T L) le_rfl
      (he ▸ d.maximal_solvable) hBM hB (he ▸ d.hall) hfaith
  · exact source_nonnormal_hall_faithful_of_local_thompson D hmin hn hna hJ hH hlarge B hBM hB

end CFSG.Quasithin.Chapter10
