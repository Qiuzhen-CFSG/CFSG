module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.LinearThree.Constituent
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.LinearThree.DoubleExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.LinearThree.NonblockExclusion

/-!
# The preliminary linear-three block reduction

The imported source construction proves the actual constituent centralizer,
its two-core QI, and the genuine MS pair XQI, including exchanged constituents.
The original radical R remains distinct from QI; their common intrinsic
commutator core transports module sections while preserving radical clauses.
The doubled-natural offender argument and the natural central-layer
omega-center comparison eliminate C.1.34(2)--(4). Escape excludes (5),
leaving exactly the natural L₃(2)-block (1).

`LinearThree.Branch.binary_isBlock` is the literal C.2.7(g) consumer.
The full universal C.1.34 implication remains explicit, owned by
qt-rank-two-ms93 and discharged by the enclosing plane-characteristic-two
and final E assembly. The earlier Kc orbit premise retains its geometry and
small-parabolic producers. The older conditional core-comparison APIs below
are preserved, but the new source endpoint supplies its local comparison.

Source: Aschbacher--Smith, C.1.34, pp.136--137, and preliminary 15.2.23,
pp.1115--1116, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The actual local MS alternatives retain the natural block or the precise
centralizer-core inequality. The full central-omega case is excluded. -/
theorem plane_linearThree_MS_cases
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X0 : Subgroup G} (hXI : X0 ≤ I) (hn : I ≤ normalizer (X0 : Set G))
    (hout : ¬ X0 ≤ Mc) {n : ℕ} {F : Type} [Field F] [Finite F]
    (hms : MSDescription KnownSimple.IsKnownSimple X0 (planeParabolicCore T H ZS) n F) :
    (ChapterC.IsBlock (X0.subgroupOf (X0 ⊔ planeParabolicCore T H ZS)) ∧
      ChapterC.IsSL3EvenBlock X0 n ∧
      ∃ e : Chapter1.XiQuotient X0 ≃* Matrix.SpecialLinearGroup (Fin 3) F,
        HasSectionModel X0 (msQ X0 (planeParabolicCore T H ZS)) ⊥
          (linearThreeActor e) (Representation.specialLinearNatural (k := F) 3)) ∨
    MSNotCentralizerCore X0 (planeParabolicCore T H ZS)
      (planeSylow T ZS ⊓ (X0 ⊔ planeParabolicCore T H ZS)) := by
  obtain ⟨e,hcases⟩ := hms.2 _ (d.plane_extension_sylow hI hXI hn)
    (le_inf (d.planeParabolicCore_le_plane hI) le_sup_right)
  rcases hcases with h | h | h | h | h
  · exact Or.inl ⟨h.1,h.2.1,e,h.2.2⟩
  · exact Or.inr h.2
  · exact Or.inr h.2.2
  · exact Or.inr h.2.2.2.2.2.2.2.2.2
  · exact (d.plane_extension_omega_not_central hI hfit hout h.2.2.2.1).elim

/-- The exact remaining local-omega core comparison suffices to retain case
(1). It is an explicit local obligation, not a proof of the full reduction. -/
theorem plane_linearThree_block_of_MS_core
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X0 : Subgroup G} (hXI : X0 ≤ I) (hn : I ≤ normalizer (X0 : Set G))
    (hout : ¬ X0 ≤ Mc) {n : ℕ} {F : Type} [Field F] [Finite F]
    (hms : MSDescription KnownSimple.IsKnownSimple X0 (planeParabolicCore T H ZS) n F)
    (hcore : ((X0 ⊔ planeParabolicCore T H ZS) ⊓ centralizer
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
        (planeSylow T ZS ⊓ (X0 ⊔ planeParabolicCore T H ZS)) : Set G)).pCoreIn 2 =
      planeParabolicCore T H ZS) :
    ChapterC.IsBlock (X0.subgroupOf (X0 ⊔ planeParabolicCore T H ZS)) ∧
      ChapterC.IsSL3EvenBlock X0 n := by
  rcases d.plane_linearThree_MS_cases hI hfit hXI hn hout hms with h | h
  · exact ⟨h.1,h.2.1⟩
  · exact (h hcore.symm).elim

/-- Specialization to the literal source orbit; no orbit identification or
centralizer-core comparison is silently supplied by this wrapper. -/
theorem plane_blockOrbit_linearThree_of_MS_core
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I}
    (hn : I ≤ normalizer (planeBlockOrbit T ZS X : Set G))
    (hout : ¬ planeBlockOrbit T ZS X ≤ Mc) {F : Type} [Field F] [Finite F]
    (hms : MSDescription KnownSimple.IsKnownSimple (planeBlockOrbit T ZS X)
      (planeParabolicCore T H ZS) 1 F)
    (hcore : ((planeBlockOrbit T ZS X ⊔ planeParabolicCore T H ZS) ⊓ centralizer
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
        (planeSylow T ZS ⊓ (planeBlockOrbit T ZS X ⊔ planeParabolicCore T H ZS)) : Set G)).pCoreIn 2 =
      planeParabolicCore T H ZS) :
    ChapterC.IsSL3EvenBlock (planeBlockOrbit T ZS X) 1 :=
  (d.plane_linearThree_block_of_MS_core hI hfit (d.blockOrbit_le_escape hI X)
    hn hout hms hcore).2

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
