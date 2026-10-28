module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.QuietOddImage
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.HallApplication

/-!
# Displacement invariance in the original Hall-faithfulness application

The quiet intrinsic Hall kernel is trivial once its displacement in the
original full module is Sylow invariant. Hall conjugacy then gives the
unchanged arbitrary-Hall conclusion. Conversely a nontrivial intrinsic
kernel supplies an elementary odd actor whose displacement is nonzero and
is not normalized by T. The actor still lies in the literal section kernel,
permutes with T, and has an ambient normalizer escaping the original M.

This isolates the remaining quiet source obligation without an irreducibility
or fixed-generation assumption on an arbitrary setup. It does not assert
that permutation of A and T implies invariance of [V_M,A].
Source: Aschbacher--Smith 4.4.13--14 and 10.2.3(2), printed pp.623--625,745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A nontrivial quiet intrinsic kernel gives a genuine escaping odd actor
whose displacement in the original V_M is nonzero and fails T-invariance. -/
theorem source_quiet_hall_kernel_escaping_displacement
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hk : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧
      Nat.Coprime p (Nat.card (L ⧸ pCore 2 L)) ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ d.witness.abelianGroup.map H.subtype ∧
      A ≤ sectionCentralizer (localOrbit T L) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ D.maximalLocal ∧
      ⁅D.fullModule,A⁆ ≠ ⊥ ∧
      ¬ (T : Subgroup G) ≤ normalizer (⁅D.fullModule,A⁆ : Subgroup G) := by
  obtain ⟨p,A,hp,ho,hcop,hne,hA,hAB,hAC,hAT,hout⟩ :=
    source_hstar_hall_kernel_escaping_coprime D hn hH hlarge hP d hk
  let : Fact p.Prime := ⟨hp⟩
  let := hA
  have hodd : Odd (Nat.card A) := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hk]
    exact ho.pow
  have hnfix : ¬ A ≤ centralizer (D.fullModule : Set G) := fun hf =>
    hout (source_nonnormal_oddKernel_normalizer D hn ho A hne hA hAC hf hAT)
  refine ⟨p,A,hp,ho,hcop,hne,hA,hAB,hAC,hAT,hout,?_,?_⟩
  · exact fun he => hnfix (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp he))
  · intro hTW
    apply hnfix
    exact source_oddActor_fixes_of_sylow_normalizes_displacement D A
      ((le_sectionCentralizer_iff _ _).mp hAC).1 hodd
      ((hAB.trans (map_subtype_le _)).trans
        (source_hstar_centralizes_omega_of_local_thompson_centralizes D hJ hH)) hTW

/-- Sylow invariance for the intrinsic quiet kernel gives faithfulness of
every specified Hall subgroup, with all quotient maps unchanged. -/
theorem source_quiet_hall_faithful_of_intrinsic_displacement_normalized
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hTW : (T : Subgroup G) ≤ normalizer
      (⁅D.fullModule,d.witness.abelianGroup.map H.subtype ⊓
        sectionCentralizer (localOrbit T L)⁆ : Subgroup G))
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hB : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H))) :
    B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥ := by
  have he := source_hstar_parabolicMax_eq_overlap D hH hP
  have hfix := (source_quiet_hall_kernel_fixes_iff_displacement_normalized D hJ hH
    d.witness.abelianGroup (he ▸ d.hall_le) (he ▸ d.hall)).mpr hTW
  have hfaith := source_hstar_hall_kernel_eq_bot_of_full_fixation D hn hH hlarge hP d hfix
  exact source_hall_sectionKernel_faithful_of_hall_conjugacy
    (M := D.maximalLocal) (X := localOrbit T L) le_rfl
    (he ▸ d.maximal_solvable) hBM hB (he ▸ d.hall) hfaith

/-- Normalization of the intrinsic kernel's literal image is sufficient
for the original arbitrary-Hall faithfulness conclusion. -/
theorem source_quiet_hall_faithful_of_intrinsic_image_normalized
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hi : ((T : Subgroup G).subgroupOf D.maximalLocal).map
        (sourceFullModuleConjugation D) ≤
      normalizer (((d.witness.abelianGroup.map H.subtype ⊓
        sectionCentralizer (localOrbit T L)).subgroupOf D.maximalLocal).map
        (sourceFullModuleConjugation D) : Set (MulAut D.fullModule)))
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hB : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H))) :
    B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥ :=
  source_quiet_hall_faithful_of_intrinsic_displacement_normalized D hn hJ hH hlarge hP d
    (source_full_displacement_normalized_of_image D _
      (inf_le_right.trans ((le_sectionCentralizer_iff _ _).mp le_rfl).1) hi) B hBM hB

/-- An odd Sylow-normalized overgroup of the intrinsic kernel image suffices
for the arbitrary-Hall conclusion; no individual image-normality is assumed. -/
theorem source_quiet_hall_faithful_of_intrinsic_image_le_odd_normalized
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (P : Subgroup (MulAut D.fullModule)) (ho : Odd (Nat.card P))
    (hSP : ((T : Subgroup G).subgroupOf D.maximalLocal).map
      (sourceFullModuleConjugation D) ≤ normalizer (P : Set (MulAut D.fullModule)))
    (hBP : ((d.witness.abelianGroup.map H.subtype ⊓ sectionCentralizer (localOrbit T L)).subgroupOf
      D.maximalLocal).map (sourceFullModuleConjugation D) ≤ P)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hB : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H))) :
    B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥ := by
  have he := source_hstar_parabolicMax_eq_overlap D hH hP
  have hfix := source_quiet_hall_kernel_fixes_of_image_le_odd_normalized D hJ hH
    d.witness.abelianGroup P ho hSP hBP
  have hfaith := source_hstar_hall_kernel_eq_bot_of_full_fixation D hn hH hlarge hP d hfix
  exact source_hall_sectionKernel_faithful_of_hall_conjugacy
    (M := D.maximalLocal) (X := localOrbit T L) le_rfl
    (he ▸ d.maximal_solvable) hBM hB (he ▸ d.hall) hfaith

end CFSG.Quasithin.Chapter10
