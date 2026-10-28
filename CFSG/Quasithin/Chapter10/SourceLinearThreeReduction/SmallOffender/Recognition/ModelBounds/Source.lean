module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.RankOne
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.CubicIntersections
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.DoubledExclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.DiagonalCore.Source

/-!
# The original small offender with a moving local Thompson subgroup

Minimal module selection leaves the two actual natural rows. In the SL₂ row,
field four is excluded by its genuine A₅ isomorphism; the larger fields are
excluded by the full local bounds and the proved cubic fixed-space geometry.
The surviving SL₃(2) row gives full/local equality and natural coordinates
on the original moved central quotient. The terminal TI contradiction then
forces w≥2 without changing the full module.

The final original small-offender consumer retains only recognition in the
quiet local Thompson branch and the earlier half-Sylow input. Quiet recognition
and final assembly remain with qt-d-10-nona5-small-offender; half-Sylow uniqueness
has its existing source producer, with ultimate discharge by point control.
This is not yet the unconditional SourceNonnormalSmallOffenderAt theorem.
Source: Aschbacher--Smith 10.1.1--2 and10.2.10--12, pp.741--742,753--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 ChapterE PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The genuine binary rank-one quotient has a cubic divisor. -/
theorem rank_one_quotient_three_dvd
    (_D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  rw [Nat.card_congr e.toEquiv]
  have h3 := Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := F) (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  exact (h3.trans (card_subgroup_dvd_card _)).trans
    (Subgroup.card_dvd_of_surjective (QuotientGroup.mk' (center SL(2,F)))
      (QuotientGroup.mk'_surjective _))

/-- The larger actual rank-one natural modules are impossible at corank two. -/
theorem no_rank_one_natural_of_small_offender
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (hnat : RankOneNatural D)
    (hcross : ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : False := by
  obtain ⟨n,hn,e,⟨mark⟩⟩ := hnat
  let : NeZero n := ⟨by omega⟩
  let : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
  by_cases hn2 : n = 2
  · subst n
    exact not_slTwo_of_not_alternatingFive c.notA5 (GaloisField.card 2 2 (by decide)) ⟨e⟩
  · obtain ⟨b⟩ := rank_one_large_bounds D e mark c.nonnormal hcross
      (by omega : 2 < n) (GaloisField.card 2 n (by omega))
    exact FixedSpaces.large_module_false_of_three D c b (rank_one_quotient_three_dvd D e) hNL

/-- The moving local Thompson branch recognizes the original natural three-space;
all rank-one fields, including four, have been excluded by actual markings. -/
theorem natural_geometry_of_local_thompson
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) :
    Nonempty (SourceLinearThreeGeometry T D) := by
  have hcross : ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
    fun _ ht htn => ModuleChoice.crossed_of_local_thompson D hJ ht htn
  rcases ModuleChoice.moving_local_natural_of_minimal D c.minimal c.nonnormal c.notA5 hJ with hr | hb
  · exact (no_rank_one_natural_of_small_offender D c hr hcross hNL).elim
  · obtain ⟨e,⟨mark⟩⟩ := hb
    exact ⟨⟨ModuleChoice.full_eq_local_of_binaryThreeNatural D c.nonnormal ⟨e,⟨mark⟩⟩,
      e,mark,hcross⟩⟩

/-- Apply the completed terminal construction using the bound for this very setup. -/
theorem natural_small_corank_false_of_normalizer
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1) : False := by
  obtain ⟨hone,hz,hti⟩ := NaturalCorank.natural_local_reduction c m hNL hsmall
  obtain ⟨w⟩ := NaturalCorank.terminalConstructionAt T L D g c m hone hz hti
  exact w.false_of_diagonal_core c m (NaturalCorank.diagonalCoreAt T) hz hti

/-- The literal survivor on the original setup in the moving local Thompson branch. -/
theorem survivor_of_local_thompson
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) :
    Nonempty (SourceLinearThreeGeometry T D) ∧
      2 ≤ globalW D.fullModule (T : Subgroup G) := by
  obtain ⟨m⟩ := natural_geometry_of_local_thompson D c hJ hNL
  refine ⟨⟨m⟩,?_⟩
  have hk : 2 ≤ subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) := by
    by_contra hn
    exact natural_small_corank_false_of_normalizer D c m hNL (by omega)
  rw [c.attained]
  exact_mod_cast hk

/-- The small-offender assembly is reduced to recognition in the quiet local
Thompson branch and the existing half-Sylow source input. Final discharge of
both premises remains with the small-offender owner and its live source producers. -/
theorem nonnormalSmallOffender_of_quiet_local_recognition_and_halfSylow
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hquiet : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g →
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
        E.fullModule ≤ D.fullModule ∧ Nonempty (SourceLinearThreeGeometry T E)) :
    SourceNonnormalSmallOffenderAt T := by
  apply NaturalCorank.nonnormalSmallOffender_of_recognition_halfSylow ?_ hhalf
  intro L D g c
  right
  by_cases hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)
  · exact hquiet L D g c hJ
  · exact ⟨D,le_rfl,natural_geometry_of_local_thompson D c hJ
      (PointControl.component_normalizer_le_of_halfSylowUnique D c.nonnormal
        (hhalf c.many L D c.nonnormal c.notA5))⟩

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
