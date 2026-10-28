module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ModuleGeometry
public import CFSG.Quasithin.ChapterE.Section06.Defs
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# The three remaining cases of the original L₃ centralizer argument

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

The configuration is the temporary counterexample in the proof of 12.4.8:
an actual hyperplane U of the original chosen V whose centralizer escapes
N_G(V). Its other fields are the original hypotheses and the permitted
earlier 12.2 implications. It includes no component classification,
odd-core centralization, or conclusion of 12.4.8.

The three propositions below are independent proof obligations. The source
assembly must prove all of them, rather than assuming that a case split
establishes the book theorem. Their owners can use the shared Preparation
module and the unconditional ordinary-layer application in Layer.

Source: Aschbacher–Smith, Lemma 12.4.8, printed pp.815–816.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
open Section02 SmallFusion ChapterE
universe u

/-- The literal source data during the reductio, before any of its three cases. -/
structure Configuration {G : Type u} [Group G] [Finite G]
    (T : Sylow 2 G) (L V U : Subgroup G) where
  hypothesis : Hypothesis1223 KnownSimple.IsKnownSimple T L
  chosen : ChosenModule T L V
  extension : SLThreeExtension chosen
  fixed_nontrivial : fixedSubgroup L V ≠ ⊥
  structural : Structural1222At KnownSimple.IsKnownSimple T
  normalizer_action : ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L,
    ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v
  le_module : U ≤ V
  corank : subgroupCorank V U = 1
  escape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)

/-- The E.6.14 application in the first case on p.815. -/
def CharacteristicTwoExclusion : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V U : Subgroup G),
    Configuration T L V U → HasCharacteristicTwo (centralizer (U : Set G)) → False

/-- The ordinary-component argument, including comparison with C_G(U∩Uˡ). -/
def ComponentExclusion : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V U : Subgroup G),
    Configuration T L V U →
      (∃ K : Subgroup G, IsComponentIn K (centralizer (U : Set G))) → False

/-- The odd-core argument on p.816, after exclusion of ordinary components. -/
def OddCoreExclusion : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V U : Subgroup G),
    Configuration T L V U →
      (∀ K : Subgroup G, ¬ IsComponentIn K (centralizer (U : Set G))) →
      pPrimeCore 2 (centralizer (U : Set G)) ≠ ⊥ → False

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
