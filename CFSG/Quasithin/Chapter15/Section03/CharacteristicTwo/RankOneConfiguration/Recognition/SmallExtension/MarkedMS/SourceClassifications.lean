module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Conditions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.CentralElimination

/-!
# Exact earlier classification inputs and surviving module alternatives

The earlier C.1.32 and C.1.34 implications are quantified over every finite
group with the complete small MS hypotheses. All five outcomes of each
classification are retained, including the full SL₃ field parameter and
all central, dual and Frattini layers. They are explicit source-theorem
parameters; this module does not prove their exhaustiveness.

After a binary SL₃ quotient has been constructed, specialization of C.1.34
and the central-omega elimination give cases (1)–(3). Comparison of the
full C.1.32 list with the actual marked action remains a separate proof.
`SurvivingSmallCases` is the requested output contract for that assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.32/34,
printed pp.135–137; proof of 15.3.31, printed p.1132.
-/

@[expose] public section

open Subgroup CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G]

/-- All five source conclusions of C.1.32, before comparison with the
marked small models. The last case retains the full universal SL3. -/
def RankTwoAlternatives (L R : Subgroup G) : Prop :=
  (IsBlock (L.subgroupOf (L ⊔ R)) ∧ IsG2TwoBlock L) ∨
  (IsBlock (L.subgroupOf (L ⊔ R)) ∧ IsAlternatingBlock L 6) ∨
  (IsBlock (L.subgroupOf (L ⊔ R)) ∧ IsSp4FourBlock L) ∨
  (IsBlock (L.subgroupOf (L ⊔ R)) ∧ IsExceptionalAhat6Block L) ∨
  ∃ n : ℕ, 1 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
    Nat.card F = 2 ^ n ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F)

/-- The universally quantified earlier source implications, restricted to
small MS-pairs. They retain all C.1.32 outcomes and every C.1.34 layer and
are explicit parameters, not axioms or a proof of either classification. -/
structure EarlierMSClassifications (κ : GroupClass.{u}) : Prop where
  rankTwo : ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J),
    SmallMSPair κ L R → RankTwoAlternatives L R
  linearThree : ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J),
    SmallMSPair κ L R → ∀ (n : ℕ), 1 ≤ n →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
    Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F) →
    ∀ S : Subgroup J, Chapter1.IsSylowIn 2 S (L ⊔ R) → R ≤ S →
      ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F,
        MSModuleAlternatives L R S n F e

/-- Specialize the full earlier C.1.34 implication and discharge the two
excluded cases. Only the binary quotient identification remains to be
obtained from C.1.32's complete alternatives. -/
theorem linearThree_survivors_of_classification [Finite G] {κ : GroupClass.{u}}
    (earlier : EarlierMSClassifications κ) {L S : Subgroup G}
    (hms : SmallMSPair κ L S)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ S))
    (hcard : Nat.card (omegaCenterIn S) = 4)
    (he : Nonempty ((L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      LinearThreeSurvivors L S e := by
  obtain ⟨e, hc⟩ := earlier.linearThree G L S hms 1 (by decide)
    (ZMod 2) (by simp) he S hS le_rfl
  exact ⟨e, linearThree_survivors hS hms.characteristic hcard e hc⟩

/-- The precise block/module alternatives to be constructed for the parent.
This predicate asserts no exhaustiveness on its own. -/
def SurvivingSmallCases (L S : Subgroup G) : Prop :=
  (IsBlock (L.subgroupOf (L ⊔ S)) ∧ IsAlternatingBlock L 6) ∨
  (IsBlock (L.subgroupOf (L ⊔ S)) ∧ IsG2TwoBlock L) ∨
  ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
    LinearThreeSurvivors L S e

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

end
