module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalBinary
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.PositiveExclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.Recognized
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Cubic

/-!
# Preparing and recognizing original irreducible covers

The constrained context has no original fixed layer. An irreducible moved
cover therefore has zero kernel, and its nonzero local moved subgroup is
the whole original moved subgroup. Pair generation makes the local and
full modules equal; local Thompson fixedness then supplies full fixedness.
Thus the fixed-point orbit spans the original moved subgroup and prepares
the literal reduced FF action, without a quietness or cubic-order premise.
The containing-action analysis recognizes the original SL₃(2) quotient.
In particular, three-free and binary rank-one quotients are impossible on
such a cover. Concrete source rows are connected in QuietRows; arbitrary
row recognition and the retained four-natural row remain with the final
assembly owner qt-d-10-nona5-point-constrained.

Source: Aschbacher--Smith 10.1.1--2 and10.2.9, printed pp.741--742,751--752.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open ChapterB.QuasisimpleSource Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

omit [Finite G] in
private theorem cubic_of_linear
    {F : Type*} [Field F] [Finite F] [CharP F 2] {d : ℕ} (hd : 2 ≤ d)
    (e : (L ⧸ pCore 2 L) ≃* SL(d,F)) : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  have h := Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := F) (i := (⟨0,by omega⟩ : Fin d)) (j := (⟨1,by omega⟩ : Fin d))
    (Fin.ne_of_val_ne (by change (0:ℕ) ≠ 1; decide))
  rw [Nat.card_congr e.toEquiv]
  exact (h.trans (card_subgroup_dvd_card _)).trans
    (card_dvd_of_surjective (QuotientGroup.mk' (center SL(d,F))) (QuotientGroup.mk'_surjective _))

/-- The original moved fixed kernel vanishes without a model or cubic-order premise. -/
theorem Context.moved_fixed_eq_bot (c : Context D t v I) : sourceMovedFixed D = ⊥ := by
  rw [c.moved_fixed_eq_orbit_fixed]
  apply bot_unique
  apply (inf_le_inf_right _ ?_).trans_eq c.full_fixed_eq_bot
  exact le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)

/-- Every prepared containing action forces cubic original component order. -/
theorem Context.three_dvd_of_prepared (c : Context D t v I) (h : Prepared D v I) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  have a := c.actionFacts h
  cases c.recognized_containing_model a with
  | linearThree F _ e _ => exact cubic_of_linear (by decide) e
  | symplecticFour F _ e _ => exact cubic_of_linear (by decide) e
  | g2 F _ e _ => exact cubic_of_linear (by decide) e
  | alternatingSeven E =>
    exact cubic_of_linear (by decide) (c.binary_three_quotient_of_seven_actor a E).some
  | binaryLinear _ _ e _ => exact cubic_of_linear (by decide) e

/-- Preparation excludes the original three-free component branch outright. -/
theorem Context.no_prepared_of_three_free (c : Context D t v I)
    (hd : ¬ 3 ∣ Nat.card (L ⧸ pCore 2 L)) (h : Prepared D v I) : False :=
  hd (c.three_dvd_of_prepared h)

/-- A prepared full orbit recognizes the original binary-three quotient and
fixes the entire original full module under J(T). -/
theorem Context.binary_three_and_full_thompson_of_moved_le (c : Context D t v I)
    (h : Prepared D v I) (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I) :
    Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) :=
  ⟨c.binary_three_quotient_of_moved_le (c.actionFacts h) hspan,
    c.full_thompson_fixed_of_three (c.three_dvd_of_prepared h)⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) L V} [IsIrreducible ρ]

/-- Every original irreducible cover generates the full moved span: its
original fixed kernel has already been excluded by the constrained context. -/
theorem Context.moved_le_of_irreducible_cover (c : Context D t v I)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) :
    ⁅D.fullModule,L⁆ ≤ orbitModule D v I :=
  c.moved_le_of_irreducible (c.moved_fixed_eq_bot ▸ s)

/-- An irreducible original cover makes the local and full moved subgroups equal. -/
theorem Context.local_moved_eq_full_of_irreducible_cover (c : Context D t v I)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) :
    ⁅D.moduleSubgroup,L⁆ = ⁅D.fullModule,L⁆ := by
  have s' := c.moved_fixed_eq_bot ▸ s
  rcases s'.eq_kernel_or_section ⁅D.moduleSubgroup,L⁆ bot_le
      (commutator_mono (le_componentOrbit _ _) le_rfl)
      (normalizer_commutator_ge_right _ _) with hz | he
  · exact (Selection.ModuleChoice.local_moved_ne_bot D hz).elim
  · exact he

/-- Pair generation recovers the original full module from the local one. -/
theorem Context.full_eq_local_of_irreducible_cover (c : Context D t v I)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) :
    D.fullModule = D.moduleSubgroup := by
  have hW : ⁅D.fullModule,L⁆ ≤ D.moduleSubgroup := by
    rw [←c.local_moved_eq_full_of_irreducible_cover s]
    exact le_normalizer_iff_commutator_le_left.mp
      ((le_componentOrbit L T).trans D.orbit_normalizes_module)
  obtain ⟨u,hu,_,_,hgen,_⟩ := source_nonnormal_fullModule_pair D
    (fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem))
  apply le_antisymm _ (le_componentOrbit _ _)
  change D.fullModule ≤ D.moduleSubgroup
  rw [hgen]
  exact sup_le hW ((map_mono hW).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (D.sylow_normalizes_module hu)))

/-- Full Thompson fixedness follows on every original irreducible cover,
including the three-free source rows. -/
theorem Context.full_thompson_fixed_of_irreducible_cover (c : Context D t v I)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) := by
  rw [c.full_eq_local_of_irreducible_cover s]
  exact c.local_thompson_fixed

/-- Every irreducible cover supplies complete preparation of the original orbit. -/
theorem Context.prepared_of_irreducible_cover (c : Context D t v I)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) :
    Prepared D v I :=
  c.prepared_of_quiet_irreducible (c.moved_fixed_eq_bot ▸ s)
    (c.full_thompson_fixed_of_irreducible_cover s)

/-- The prepared irreducible cover feeds the literal reduced FF action. -/
theorem Context.actionFacts_of_irreducible_cover (c : Context D t v I)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) :
    ActionFacts c := c.actionFacts (c.prepared_of_irreducible_cover s)

/-- Irreducible original covers force an actual SL₃(2) quotient with no
quietness, fixed-kernel or cubic-order premise. -/
theorem Context.binary_three_of_irreducible_cover (c : Context D t v I)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) :
    Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) :=
  c.binary_three_quotient_of_moved_le (c.actionFacts_of_irreducible_cover s)
    (c.moved_le_of_irreducible_cover s)

/-- No three-free original quotient has an irreducible moved cover in the
constrained configuration. In particular this excludes the Suzuki row. -/
theorem Context.no_irreducible_cover_of_three_free (c : Context D t v I)
    (hd : ¬ 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) : False :=
  c.no_prepared_of_three_free hd (c.prepared_of_irreducible_cover s)

/-- Binary rank-one original quotients cannot carry any irreducible moved
cover in the constrained context, including the orthogonal row. -/
theorem Context.no_rankOne_irreducible_cover (c : Context D t v I)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) : False := by
  obtain ⟨f⟩ := c.binary_three_of_irreducible_cover s
  exact Matrix.SL2.binary_not_equiv_linear_three (F := F) (E := ZMod 2) (n := 1)
    (by decide) (by simp) (e.symm.trans f)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
