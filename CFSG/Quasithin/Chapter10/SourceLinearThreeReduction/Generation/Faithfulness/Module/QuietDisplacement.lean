module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.MovingThompson
public import Theory.GroupTheory.CoprimeFixedDisplacement

/-!
# The quiet Hall kernel and its actual displacement subgroup

Every quiet H-star subgroup fixes the Sylow omega-center, hence the
Sylow-fixed part of the original full module. Coprime fixed/moved
disjointness now shows that the Hall kernel fixes the full module exactly
when T normalizes its displacement subgroup. This avoids imposing
generation of the full M-orbit by the L₀-orbit of its Sylow-fixed part.

The criterion retains the entire original full module and literal Hall
kernel. Sylow invariance of that displacement is still an obligation;
permutation of the Hall kernel with T does not assert this invariance.
Source: Aschbacher--Smith 4.4.14 and 10.2.3(2), printed pp.624--625,745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Odd actors fixing the Sylow omega-center fix V_M if their actual
displacement subgroup is T-invariant. -/
theorem source_oddActor_fixes_of_sylow_normalizes_displacement
    (A : Subgroup G) (hAM : A ≤ D.maximalLocal) (hodd : Odd (Nat.card A))
    (hz : A ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hTW : (T : Subgroup G) ≤ normalizer (⁅D.fullModule,A⁆ : Subgroup G)) :
    A ≤ centralizer (D.fullModule : Set G) := by
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  have hV := IsElementaryAbelian.isPGroup 2 D.fullModule
  have hVT := D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)
  have hZ : D.fullModule ⊓ centralizer (T : Set G) ≤
      Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    intro v hv
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hVT hv.1,elemPow_eq_one_of_isElementaryAbelian v hv.1,fun t ht => hv.2 t ht⟩
  have hcop : Nat.Coprime (Nat.card A) (Nat.card D.fullModule) := by
    obtain ⟨n,hn⟩ := hV.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_fixed_centralizer_of_normalizes_displacement
      D.fullModule A T hV T.isPGroup' (hAM.trans D.maximalLocal_normalizes_fullModule)
      hcop (hZ.trans (le_centralizer_iff.mp hz)) hTW))

/-- The precise remaining invariance criterion for the literal quiet Hall kernel. -/
theorem source_quiet_hall_kernel_fixes_iff_displacement_normalized
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hB : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H))) :
    (B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G)) ↔
    (T : Subgroup G) ≤ normalizer
      (⁅D.fullModule,B.map H.subtype ⊓ sectionCentralizer (localOrbit T L)⁆ : Subgroup G) := by
  constructor
  · intro hf
    rw [commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hf)]
    exact le_normalizer_of_normal
  · intro hn
    have ho : Odd (Nat.card B) := by
      rw [←Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv]
      exact OddHall.odd_hall_odd hB
    have hm : Odd (Nat.card (B.map H.subtype)) := by
      rwa [card_map_of_injective H.subtype_injective]
    apply source_oddActor_fixes_of_sylow_normalizes_displacement D _
      (inf_le_right.trans ((le_sectionCentralizer_iff _ _).mp le_rfl).1)
      (hm.of_dvd_nat (card_dvd_of_le inf_le_left)) _ hn
    exact (inf_le_left.trans (map_subtype_le B)).trans
      (source_hstar_centralizes_omega_of_local_thompson_centralizes D hJ hH)

end CFSG.Quasithin.Chapter10
