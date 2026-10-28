module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Branches
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Inputs

/-!
# Source obligations for the non-Bender centralizer branch

The normal-seed exclusion, the strict-seed closure calculation, and the
model parabolic calculation have independent mathematical inputs. These
propositions specify those remaining obligations; they do not assert them.
All components, quotients and Sylow restrictions refer to the original G.

The adequate intrinsic 1.3.4 theorem retains Held. We retain it here too,
until the extra Chapter 10 hypotheses exclude it or supply its generation.
The small odd-prime sieve is proved separately in `Models`.

Source: Aschbacher--Smith 10.2.4 and 10.3.3, printed pp.747,756, and the
intrinsic 1.3.4 correction in `docs/quasithin-proof-basis.md`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- The actual nonbinary rows after excluding PSL₂(3) and identifying
PSL₂(5) with the binary Bender model. The invariant linear rows retain
the full automorphism-group quotient, not only their simple socle. -/
def RemainingModel (I : Subgroup G) : Prop :=
  (∃ p : ℕ, p.Prime ∧ Odd p ∧ 7 ≤ p ∧
    ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 p) ∨
  ((T : Subgroup G) ≤ normalizer (I : Set G) ∧
    (∃ k : ℕ, (k = 4 ∨ k = 5) ∧
      ClassicalGroup.IsPSL (I ⧸ pCore 2 I) k 2 ∧
      Nonempty (((I ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (I ⊔ (T : Subgroup G) : Subgroup G)) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin k) (ZMod 2))))) ∨
  ((T : Subgroup G) ≤ normalizer (I : Set G) ∧
    Nonempty ((I ⧸ pCore 2 I) ≃* Held.He))

/-- In the normal-seed case, the three-rank bound and Suzuki recognition
must apply to each actual escaping C-component. -/
def NormalSeedBenderAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s),
    centralizerSeed T L (d.first * d.second) = componentSpan T L (d.first * d.second) →
    ∀ I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)),
      ¬ I ≤ D.maximalLocal → ClassificationModels.IsBenderModel (I ⧸ pCore 2 I)

/-- The centralizer application of the genuine closure alternatives. This
has no wreath-recognition premise and is independent of the normal-seed
exclusion. The escaping component and its original T-orbit must be constructed. -/
def StrictClosureAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s),
    centralizerSeed T L (d.first * d.second) < componentSpan T L (d.first * d.second) →
    ∃ I : Subgroup G,
      I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)) ∧
      ¬ I ≤ D.maximalLocal ∧ IsQuasisimple (I ⧸ pCore 2 I) ∧
      componentOrbit I (T : Subgroup G) = componentSpan T L (d.first * d.second) ∧
      Overgroups.ClosureModel T I

/-- Only a specified family of actual minimal parabolics is requested.
Attained E-generation is enough: the original central involution supplies
positive numeric generation parameter in `Preparation`. -/
def ModelFamiliesAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s)
    (I : Subgroup G),
    I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)) →
    ¬ I ≤ D.maximalLocal → IsQuasisimple (I ⧸ pCore 2 I) →
    componentOrbit I (T : Subgroup G) = componentSpan T L (d.first * d.second) →
    RemainingModel T I →
    let Y := componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G)
    let S : Sylow 2 Y := T.subtype le_sup_right
    ∃ Δ : Set (Subgroup Y),
      (∀ P ∈ Δ, ChapterB.IsMinimalParabolicOver S P ∧ ChapterE.IsEGenerated 1 P) ∧
      sSup Δ ⊔ normalizer (S : Set Y) = ⊤

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
