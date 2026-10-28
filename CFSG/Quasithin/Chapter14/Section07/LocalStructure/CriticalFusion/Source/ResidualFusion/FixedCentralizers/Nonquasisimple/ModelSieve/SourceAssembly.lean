module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.SourceDichotomy
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.StarLocalResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.BlockComparisons
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.LinearParabolics.Transport
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.SymplecticCentralizer

/-!
# Comparing all eight C.2.7 alternatives at the original centralizer

The literal K-image supplies the perfect A₅-by-two residual in the actual
star stabilizer. Borel, transposition-centralizer, partition, parabolic and
order comparisons eliminate all but the A₇ and Sp₄(4) rows. The original
Sp₄(4) scalar torus gives a forbidden section centralizer of order divisible
by three. An A₇ block is therefore the only remaining row, and the literal
intersection filtration bounds every complete K-chief count by one.

Only the complete earlier C.2.7 conclusion remains explicit here. No separate
model-selection, A.3.14 comparison, star-residual or geometric transport
callback is assumed. Source: Aschbacher–Smith 14.7.68, printed pp.1071–1072.
-/

public section
open Subgroup Representation Theory.GroupTheory NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_a7_block_of_c27
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (c27 : Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) :
    ChapterC.IsBlock (Lu.subgroupOf (d.fixedCentralizer u)) ∧
      Nonempty ((Lu ⧸ pCore 2 Lu) ≃* alternatingGroup (Fin 7)) := by
  have hres := d.fixedStarM_hasA5TwoResidual u h c27
  cases c27.alternatives with
  | chi block chi cases =>
    exact ⟨block,(d.fixedComponent_chi_alternatingSeven u h c27 hres block chi cases).2.2.quotient_iso⟩
  | alternating n lower upper block model action centralizer =>
    have hn := d.fixedComponent_alternating_degree_seven u h hres n lower upper
      block model action centralizer
    subst n
    exact ⟨block,model.2.2.quotient_iso⟩
  | ahatSix block model index stabilizer =>
    exact (d.fixedComponent_not_ahatSix u h model index).elim
  | exceptionalSeven block model index =>
    exact ⟨block,model.2.1⟩
  | rankTwo block cases =>
    obtain ⟨hm,hp⟩ := d.fixedComponent_rankTwo_symplecticFour u h hres block cases
    exact (d.fixedComponent_sp4_contradiction u h hm c27 hp).elim
  | binaryG2 block model extension =>
    exact (d.fixedComponent_not_binaryG2 u h hres block model extension).elim
  | linearThree n k hn hk hp ms =>
    exact (d.fixedComponent_linearThree_parabolic_false u hres n k hn hk hp).elim
  | binaryLinear n hn hp =>
    exact (d.fixedComponent_binaryLinear_false u hres hn hp).elim

theorem fixedComponent_chief_upper_bound_of_c27
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (c27 : Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))
    (s : ChiefSeries (K F)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 := by
  obtain ⟨block, model⟩ := d.fixedComponent_a7_block_of_c27 u h c27
  exact d.every_complete_K_chief_count_le_one_of_c27 u h c27 block model s hs0 hs1

theorem fixedComponent_chief_upper_bound_of_source
    (c27 : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (s : ChiefSeries (K F)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 :=
  d.fixedComponent_chief_upper_bound_of_c27 u h
    (d.fixedComponent_C27_of_source_dichotomy c27 u h) s hs0 hs1

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
