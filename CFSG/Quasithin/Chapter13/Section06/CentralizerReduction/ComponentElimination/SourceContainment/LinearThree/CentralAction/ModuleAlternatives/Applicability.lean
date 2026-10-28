module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Cases
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Applicability.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.TwoCore
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Preliminaries
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# Classifier applicability in the actual 13.6.20 configuration

The source application keeps all four clauses of Hypothesis 13.3.1,
including the uniform A₅ choice, the original class 𝒦, the actual A₅ module
marking, the selected invariant K in Y_z, and its actual PSL₃(2) plus image.
The earlier local inputs used here are the centralizer Sylow assertion,
the central involution z, characteristic two (13.6.6), and invariance
(13.6.14). No reduced-module, offender-containment or SQTK-quotient
certificate is an input. Preparation constructs all six applicability
clauses on the literal W_K action.

These local deductions work before selecting a particular model for K+.
The final application retains the L₃(2) identification and the full standing
source context for its 13.6.20 consumer. It supplies applicability only;
classifier comparison and the containment conclusion have separate owners.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
Hypothesis 13.3.1, printed p.884; 13.6.2–16, pp.926–930;
Lemma 13.6.20, p.931 (PDF p.948).
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

namespace Applicability
/-- Full Hypothesis 13.3.1, with the original group class as a parameter.
Every exclusion uses an actual group model, and the choice clause is the
existing source `UniformA5Choice`, not a condition on only the selected K. -/
structure SourceHypothesis (𝒦 : GroupClass.{u}) (T : Sylow 2 G) (L : Subgroup G) : Prop where
  qtke : IsSimpleQTKE 𝒦 G
  local_component : L ∈ MainForward.faithfulLocalComponents T
  no_larger_field : ∀ f : ℕ, 1 < f → ¬
    ((∃ n : ℕ, ClassicalGroup.IsPSL G n (2 ^ f) ∨
      ClassicalGroup.IsPSU G n (2 ^ f) ∨ ClassicalGroup.IsPSp G n (2 ^ f) ∨
      ClassicalGroup.IsPOmegaPlus G n (2 ^ f) ∨
      ClassicalGroup.IsPOmegaOdd G n (2 ^ f) ∨
      ClassicalGroup.IsPOmegaMinus G n (2 ^ f)) ∨
    ClassificationModels.IsG2At G (2 ^ f) ∨
    ExceptionalGroup.IsF4 G (2 ^ f) ∨ ExceptionalGroup.IsE6 G (2 ^ f) ∨
    ExceptionalGroup.IsE7 G (2 ^ f) ∨ ExceptionalGroup.IsE8 G (2 ^ f) ∨
    ExceptionalGroup.IsTwistedE6 G (2 ^ f) ∨
    Triality.Standard.IsTrialityGroupAt (2 ^ f) G ∨
    (∃ m : ℕ, f = 2 * m + 1 ∧
      (Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∨
       Nonempty (G ≃* ReeF4.Model m))))
  no_linear : ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL G n 2
  no_alternating_nine : ¬ Nonempty (G ≃* alternatingGroup (Fin 9))
  no_sporadic : ∀ s : KnownSimple.SporadicName,
    s = .m22 ∨ s = .m23 ∨ s = .m24 ∨ s = .he ∨ s = .j4 →
      ¬ Nonempty (G ≃* s.Carrier)
  uniformA5 : UniformA5Choice T L
end Applicability

/-- Preparation for the B.5.1/B.5.6 application in 13.6.20. The required
finite-module, faithfulness, two-core, relative normality, offender and
SQTK-cover clauses are all constructed. The genuine earlier conclusions
remain explicit for the enclosing source assembly; none is a module
classification or a conclusion of 13.6.20 or 13.6.22. -/
theorem classifierApplicability_of_source {𝒦 : GroupClass.{u}}
    {L V : Subgroup G} (T : Sylow 2 G) (s : A5Module.Marking L V)
    (standing : Applicability.SourceHypothesis 𝒦 T L)
    (_hA5 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (_hcounter : IsA5Counterexample G) (K : Subgroup G)
    (hL : Tv (T : Subgroup G) (A5Module.markedV s) ≤
      normalizer (Lv L (A5Module.markedV s) : Set G))
    (hz : Tv (T : Subgroup G) (A5Module.markedV s) ≤
      centralizer ({A5Module.markedZ s} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (A5Module.markedV s))
      (Gv (A5Module.markedV s)))
    (hzOmega : A5Module.markedZ s ∈
      omegaOneCenterAmbient (Tv (T : Subgroup G) (A5Module.markedV s)))
    (hv : orderOf (A5Module.markedV s) = 2)
    (hf : Theory.GroupTheory.generalizedFitting (Gv (A5Module.markedV s)) =
      pCore 2 (Gv (A5Module.markedV s)))
    (hK : K ∈ Yz L (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s))
    (hn : Tv (T : Subgroup G) (A5Module.markedV s) ≤ normalizer (K : Set G))
    (_model : plusImage K L (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s)
      hL hz K ≃* Matrix.PSL3Two.PSL) :
    let := wk_elementary K L (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s)
      hK.1.1 hSylow hzOmega hf
    ClassifierApplicability 𝒦
      (wkRepresentation K L (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s) hL hz)
      (plusImage K L (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s) hL hz K) :=
  classifierApplicability_of_local standing.qtke K L (T : Subgroup G)
    (A5Module.markedZ s) (A5Module.markedV s) hv hL hz hSylow hzOmega hf hK hn

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
