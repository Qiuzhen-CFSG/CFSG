module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Irreducible.Action
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Irreducible.Bounds
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.ScalarNaturals
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.AllIntersections
public import Theory.Representation.PSL3Two.IrreducibleCatalogue
public import Theory.Representation.PSL3Two.NaturalDualRank

/-!
# Recognition of the irreducible binary-three small-offender branch

The actual irreducible SL₃(2) catalogue gives natural, dual-natural or adjoint
coordinates on W/C_W(L). The inverse-transpose automorphism turns the dual
row into a natural marking. The adjoint row has dimension eight and full
normalizer two-rank at most three, so the proved fixed-space contradiction
excludes it. The surviving natural section gives full/local equality and
crossed centralization; the terminal TI argument forces w ≥ 2.

This proves the branch with irreducible original moved quotient. The quiet
classification still has to construct that condition or its other rows.
The component normalizer containment retains the genuine half-Sylow source
input, with its existing producer and final point-control discharge.
Source: Aschbacher–Smith H.6.1, 10.1.1 and 10.2.12, pp.386,741,754–755.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem steinberg_large_bounds
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (BinaryLinearThree.S.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    Nonempty (LargeModuleBounds D) := by
  let : Finite BinaryLinearThree.Steinberg := Module.finite_of_finite (ZMod 2)
  apply large_bounds_of_irreducible_marking D BinaryLinearThree.S
    BinaryLinearThree.steinberg_injective
    BinaryLinearThree.IrreducibleCatalogue.steinberg_irreducible e s hn
    (m := 8) (r := 3) (by decide) ?_
    BinaryLinearThree.NaturalDual.automorphism_two_rank_le_three (by decide)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    BinaryLinearThree.finrank_steinberg]

/-- The binary-three irreducible catalogue and the actual small offender construct natural coordinates.
The adjoint alternative is excluded by the full local automizer bounds. -/
theorem natural_of_irreducible_binary_three_section
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (ρ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    BinaryThreeNatural D := by
  let : ρ.IsIrreducible := hi
  let : IsSimpleGroup BinaryLinearThree.Group := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hnon : ∃ j v, ρ j v ≠ v := by
    by_contra! hh
    obtain ⟨j,hj⟩ := exists_ne (1 : BinaryLinearThree.Group)
    apply hj
    apply hf
    rw [map_one]
    exact LinearMap.ext (hh j)
  rcases BinaryLinearThree.IrreducibleCatalogue.classify_nontrivial ρ hnon with
    ha | ha | ha
  · obtain ⟨a⟩ := ha
    exact ⟨e,⟨s.relabel _ a⟩⟩
  · obtain ⟨a⟩ := ha
    exact ⟨e.trans BinaryLinearThree.AutomorphismAction.graph,
      ⟨s.relabel _ (a.trans BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm)⟩⟩
  · obtain ⟨a⟩ := ha
    obtain ⟨b⟩ := steinberg_large_bounds D c.nonnormal e (s.relabel _ a)
    exact (FixedSpaces.large_module_false_of_normalizer D c b hNL).elim

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 ChapterE PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)

local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_full_moved_elementary D

omit hn in
/-- Recognize the exact quotient action constructed before classification. -/
theorem natural_of_binary_three_moved_irreducible {g : G}
    (c : Configuration T D g)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hi : (binaryThreeMovedAction D c.nonnormal e).IsIrreducible) :
    BinaryThreeNatural D :=
  natural_of_irreducible_binary_three_section D c hNL
    (binaryThreeMovedAction D c.nonnormal e)
    (binaryThreeMovedAction_faithful D c.nonnormal e) hi e
    (binaryThreeMovedSection D c.nonnormal e)

omit hn in
/-- The source survivor and w ≥ 2 on the same original full module in this irreducible branch. -/
theorem survivor_of_binary_three_moved_irreducible {g : G}
    (c : Configuration T D g)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hi : (binaryThreeMovedAction D c.nonnormal e).IsIrreducible) :
    Nonempty (SourceLinearThreeGeometry T D) ∧
      2 ≤ globalW D.fullModule (T : Subgroup G) := by
  have hnat := natural_of_binary_three_moved_irreducible D e c hNL hi
  obtain ⟨f,⟨s⟩⟩ := hnat
  let m : SourceLinearThreeGeometry T D := {
    full_eq_local := ModuleChoice.full_eq_local_of_binaryThreeNatural D c.nonnormal ⟨f,⟨s⟩⟩
    quotient := f
    natural := s
    crossed := fun _ ht htn => binary_three_crossed_of_marking D ⟨f,⟨s⟩⟩ ht htn }
  refine ⟨⟨m⟩,?_⟩
  have hk : 2 ≤ subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) := by
    by_contra hn
    exact natural_small_corank_false_of_normalizer D c m hNL (by omega)
  rw [c.attained]
  exact_mod_cast hk

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
