module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Extraction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Applicability
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier

/-!
# Module extraction for the central-action branch of 13.6.20

The full standing Hypothesis 13.3.1 and the genuine earlier local conclusions
prepare the literal plus action on W_K for the corrected universal B.5.1
and adequate B.5.6 implications. Their specialization gives a natural
U_K/C_{U_K}(K), with commutator generation, or a doubled U_K itself.

If K⁺ centralizes L_v⁺, the natural central quotient forces [U_K,L_v]=1,
contrary to the marked 13.6.11 theorem. The remaining doubled intertwiner
therefore supplies one compatible DoubledCoordinates marking for the actual
componentPlus map. Elementary structure and the centralizer Sylow witness
are derived from the earlier source data, rather than supplied as additional
classification premises.

The two universal classification implications remain explicit. The enclosing
13.6.20 owner supplies them and the earlier source conclusions, and uses the
coordinates in its independent parabolic-geometry argument. No containment
or noncentrality conclusion is asserted here.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.931.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
  {L V : Subgroup G} (T : Sylow 2 G) (s : A5Module.Marking L V)
  (standing : Applicability.SourceHypothesis 𝒦 T L)
  (hA5 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
  (hcounter : IsA5Counterexample G) (K : Subgroup G)
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
  (model : plusImage K L (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s)
    hL hz K ≃* Matrix.PSL3Two.PSL)
  (earlier : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleClassificationInput.{u,u} 𝒦)
  (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦)

include standing hA5 hcounter hSylow hzOmega hv hf hn model earlier classification

/-- The B.5.1/B.5.6 alternatives in the actual marked L₃(2) configuration.
The literal moved space is U_K and its central denominator is C_{U_K}(K),
by `movedEquivUK` and `central_eq`. No local classified-module premise remains. -/
theorem moduleCase_of_source :
    let := wk_elementary K L (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s)
      hK.1.1 hSylow hzOmega hf
    LinearThreeModuleCase
      (wkRepresentation K L (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s) hL hz)
      (plusImage K L (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s) hL hz K) := by
  let := wk_elementary K L (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s)
    hK.1.1 hSylow hzOmega hf
  exact Classifier.wk_moduleCase_of_classifications K L (T : Subgroup G)
    (A5Module.markedZ s) (A5Module.markedV s) hL hz
    (classifierApplicability_of_source T s standing hA5 hcounter K hL hz
      hSylow hzOmega hv hf hK hn model) model earlier classification

/-- The central-action branch of 13.6.20 has an actual doubled U_K.
Characteristic two supplies the elementary modules, the given centralizer
Sylow assertion supplies the literal Sylow witness, and 13.6.11 excludes
the natural quotient. Only the two universal source classifiers are retained. -/
theorem doubledCoordinates_of_source
    (hc : ⁅plusImage K L (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s) hL hz K,
      plusImage K L (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s)
        hL hz (Lv L (A5Module.markedV s))⁆ = ⊥) :
    Nonempty (DoubledCoordinates K L (T : Subgroup G)
      (A5Module.markedZ s) (A5Module.markedV s) hK.1.1 hL hz) := by
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (Qv (A5Module.markedV s))) :=
    omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s)) :=
    IsElementaryAbelian.of_le
      (Uv_le_coreOmega (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s)
        hSylow hzOmega hf)
  let := wk_elementary K L (T : Subgroup G) (A5Module.markedZ s) (A5Module.markedV s)
    hK.1.1 hSylow hzOmega hf
  have hcase := moduleCase_of_source T s standing hA5 hcounter K hL hz
    hSylow hzOmega hv hf hK hn model earlier classification
  obtain ⟨S, hS⟩ := hSylow
  exact doubled_of_moduleCase s K (T : Subgroup G) S hS hL hz hK hn hc hcase

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
