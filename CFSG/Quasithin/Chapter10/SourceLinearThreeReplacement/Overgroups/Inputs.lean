module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Contracts
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterE.Defs
public import Theory.SpecificGroups.Held.Model.Basic

/-!
# Remaining earlier-source inputs for the replacement overgroup calculation

These propositions separate the normal-closure classification from the
model generation calculation. They state outstanding mathematical tasks,
not proved source assertions. The assembly proves the span identity after
both have been supplied. Binary fields use actual PSL₂ isomorphisms, and
E-generation concerns the literal component-orbit Sylow join. The extra
invariant Held row is retained from the proved adequate intrinsic 1.3.4;
its elimination also belongs to the model-generation obligation.

Source: Aschbacher--Smith 10.2.4, p.747, and the generation argument of
10.3.3 reused in the final paragraph of §10.3, pp.756--757.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] (T : Sylow 2 G)

/-- The component-model consequences of 10.2.4 required here. The binary
row retains the even degree; the invariant rows retain the original actor.
The linear invariant rows also retain the actual Aut(Lₖ(2)) quotient of IT.
Held is retained separately, as required by the intrinsic source correction. -/
def ClosureModel (I : Subgroup G) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ Even n ∧
    ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 (2 ^ n)) ∨
  (∃ p : ℕ, p.Prime ∧ Odd p ∧
    ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 p) ∨
  ((T : Subgroup G) ≤ normalizer (I : Set G) ∧
    (∃ k : ℕ, (k = 4 ∨ k = 5) ∧
      ClassicalGroup.IsPSL (I ⧸ pCore 2 I) k 2 ∧
      Nonempty (((I ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (I ⊔ (T : Subgroup G) : Subgroup G)) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin k) (ZMod 2))))) ∨
  ((T : Subgroup G) ≤ normalizer (I : Set G) ∧
    Nonempty ((I ⧸ pCore 2 I) ≃* Held.He))

/-- The required normal-closure consequence of 10.2.4 for the actual seed.
All geometry and recognition inputs are conditional, so this source proof
can run independently of their producers. -/
def ClosureAlternativesAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s),
    Nonempty ((componentJoin T L (d.first * d.second) ⧸
      pCore 2 (componentJoin T L (d.first * d.second))) ≃*
      Theory.SpecificGroups.SymmetricFive.WreathComponents.W) →
    centralizerSeed T L (d.first * d.second) < componentSpan T L (d.first * d.second) →
    ¬ componentSpan T L (d.first * d.second) ≤ D.maximalLocal →
    (∀ K ∈ Chapter1.cComponentsIn (componentJoin T L (d.first * d.second)),
      componentOrbit K (T : Subgroup G) = componentSpan T L (d.first * d.second)) →
    ∀ M : Subgroup G, IsMaximalTwoLocal M → componentJoin T L (d.first * d.second) ≤ M →
      conjugateSpanBy (centralizerSeed T L (d.first * d.second)) M =
          centralizerSeed T L (d.first * d.second) ∨
      ∃ I : Subgroup G, I ∈ Chapter1.cComponentsIn M ∧
        IsQuasisimple (I ⧸ pCore 2 I) ∧
        conjugateSpanBy (centralizerSeed T L (d.first * d.second)) M =
          componentOrbit I (T : Subgroup G) ∧ ClosureModel T I

/-- The model calculation used to discard the nonbinary rows. It may use
the literal seed geometry, but cannot assume the normal-closure theorem
or its conclusion J_z=K_z. The prime-five row belongs to the binary side. -/
def ModelGenerationAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s),
    Nonempty ((componentJoin T L (d.first * d.second) ⧸
      pCore 2 (componentJoin T L (d.first * d.second))) ≃*
      Theory.SpecificGroups.SymmetricFive.WreathComponents.W) →
    centralizerSeed T L (d.first * d.second) < componentSpan T L (d.first * d.second) →
    ¬ componentSpan T L (d.first * d.second) ≤ D.maximalLocal →
    (∀ K ∈ Chapter1.cComponentsIn (componentJoin T L (d.first * d.second)),
      componentOrbit K (T : Subgroup G) = componentSpan T L (d.first * d.second)) →
    ∀ M : Subgroup G, IsMaximalTwoLocal M → componentJoin T L (d.first * d.second) ≤ M →
    ∀ I : Subgroup G, I ∈ Chapter1.cComponentsIn M →
      IsQuasisimple (I ⧸ pCore 2 I) →
      conjugateSpanBy (centralizerSeed T L (d.first * d.second)) M =
        componentOrbit I (T : Subgroup G) → ClosureModel T I →
      (∃ n : ℕ, ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 (2 ^ n)) ∨
        ChapterE.IsEGenerated 1 (componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups
