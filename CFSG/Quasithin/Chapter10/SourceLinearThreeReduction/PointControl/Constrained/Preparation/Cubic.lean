module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.NaturalDualCover
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Irreducible
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.ThompsonComparison

/-!
# Point Thompson equality at components of cubic order

When three divides the original component quotient order, local Thompson
fixedness extends to the full module through the actual cubic residual.
If local fixedness fails, the proved natural-cover preparation gives the
same point Thompson equality. Thus J(C_T(v)) = J(T) needs no source-row
marking or fixedness premise in this branch.

The orbit alternative now suffices by itself for preparation. In particular,
an irreducible cover of the original moved subgroup is prepared with its
entire fixed kernel retained: a positive kernel uses the fixed-layer
argument, and zero kernel gives full orbit generation. The conclusions feed
the literal reduced FF action and Preparation.Source's final assembly.
The remaining orbit recognition, three-free preparation, containing-model
recognition and four-natural exclusion belong to
qt-d-10-nona5-point-constrained.

Source: Aschbacher--Smith 10.1.2--3 and 10.2.9,
printed pp.742 and751.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The original point Thompson equality follows without an action marking. -/
theorem Context.thompson_eq_of_three (c : Context D t v I)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) :
    elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G) := by
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)
  · exact c.thompson_eq_of_fullModule_centralized
      (Selection.ModuleChoice.full_thompson_centralizes_of_local_three D
        (fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem)) hd hJ)
  · exact (c.prepared_of_local_thompson_moves hJ).thompson_eq

/-- At cubic component order, ambient centralizer control completes preparation. -/
theorem Context.prepared_of_centralizer_of_three (c : Context D t v I)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (hc : centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal) :
    Prepared D v I :=
  c.prepared_of_centralizer_of_thompson_eq hc (c.thompson_eq_of_three hd)

/-- The original orbit alternative supplies the remaining geometric input. -/
theorem Context.prepared_of_orbit_alternative_of_three (c : Context D t v I)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (ha : ⁅D.fullModule,L⁆ ≤ orbitModule D v I ∨
      ⁅D.fullModule,L⁆ ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    Prepared D v I :=
  c.prepared_of_centralizer_of_three hd (c.centralizer_le_of_orbit_alternative ha)

/-- Apply the orbit alternative to the literal reduced module and centralizer quotient. -/
theorem Context.actionFacts_of_orbit_alternative_of_three (c : Context D t v I)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (ha : ⁅D.fullModule,L⁆ ≤ orbitModule D v I ∨
      ⁅D.fullModule,L⁆ ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    ActionFacts c := c.actionFacts (c.prepared_of_orbit_alternative_of_three hd ha)

omit [Finite G] in
private theorem three_dvd_binary_linear
    {F : Type*} [Field F] [Finite F] [CharP F 2] {d : ℕ} (hd : 2 ≤ d)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin d) F) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  have h3 := Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := F) (i := (⟨0, by omega⟩ : Fin d)) (j := (⟨1, by omega⟩ : Fin d))
    (Fin.ne_of_val_ne (by change (0 : ℕ) ≠ 1; decide))
  rw [Nat.card_congr e.toEquiv]
  exact (h3.trans (card_subgroup_dvd_card _)).trans
    (Subgroup.card_dvd_of_surjective (QuotientGroup.mk' (center
      (Matrix.SpecialLinearGroup (Fin d) F))) (QuotientGroup.mk'_surjective _))

/-- A genuine binary linear quotient supplies the cubic-order premise. -/
theorem Context.thompson_eq_of_binary_linear (c : Context D t v I)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {d : ℕ} (hd : 2 ≤ d)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin d) F) :
    elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G) :=
  c.thompson_eq_of_three (three_dvd_binary_linear hd e)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) L V} [IsIrreducible ρ]

/-- An irreducible original cover needs neither a zero fixed kernel nor Thompson fixedness. -/
theorem Context.prepared_of_irreducible_cover_of_three (c : Context D t v I)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) :
    Prepared D v I := by
  by_cases hz : sourceMovedFixed D = ⊥
  · rw [hz] at s
    exact c.prepared_of_orbit_alternative_of_three hd (Or.inl (c.moved_le_of_irreducible s))
  · exact c.prepared_of_moved_fixed_ne_bot hz

/-- The same original cover supplies the faithful FF action used by model recognition. -/
theorem Context.actionFacts_of_irreducible_cover_of_three (c : Context D t v I)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) :
    ActionFacts c := c.actionFacts (c.prepared_of_irreducible_cover_of_three hd s)

/-- Irreducible covers at a binary linear quotient are prepared on the
original moved subgroup, with every fixed vector retained. -/
theorem Context.prepared_of_binary_linear_irreducible_cover (c : Context D t v I)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {d : ℕ} (hd : 2 ≤ d)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin d) F)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) :
    Prepared D v I :=
  c.prepared_of_irreducible_cover_of_three (three_dvd_binary_linear hd e) s

/-- Actual application of the binary linear quotient and original section
to the reduced FF action; no point Thompson premise remains. -/
theorem Context.actionFacts_of_binary_linear_irreducible_cover (c : Context D t v I)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {d : ℕ} (hd : 2 ≤ d)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin d) F)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) :
    ActionFacts c := c.actionFacts (c.prepared_of_binary_linear_irreducible_cover hd e s)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
