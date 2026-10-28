module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.SelectedSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.CompleteKnownSimple
public import CFSG.Quasithin.ClassificationModels

/-!
# Earlier inputs for the original Rudvalis application

The completed Goldschmidt size and marked classification theorems apply to
the original selected-path construction. The only C.2.7 conclusions used
are those for the relatively normal components of the actual fixed-element
centralizers. Keeping this local family explicit avoids requiring a new
universal C.2.7 theorem for unrelated groups.

The proof constructs the centralizer control, critical path, rank selection,
order and fusion before applying the concrete Rudvalis recognition. Its
classification consumer uses that same isomorphism in the full Theorem D
catalogue. The original Data and the named earlier structural, module,
Baumann, weak-closure and local C.2.7 inputs still need source proofs.

Source: Aschbacher--Smith 14.7.10, 14.7.31, 14.7.68--75 and J.1.1,
especially printed pp.1071--1078 of the combined manuscript (1 March 2004).
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Subgroup Representation Theory.GroupTheory Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter1.RadicalExclusions.ModelReduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- Only the actual fixed-centralizer instances of C.2.7 are needed. The
component is normal in its centralizer, as retained by `Nonquasisimple.Case`. -/
@[expose] def FixedComponentClassification (d : Data T L V F W) : Prop :=
  ∀ (u : F.U) (Lu : Subgroup G), Nonquasisimple.Case d u Lu →
    FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)

/-- The universal source implication supplies the precise local contract. -/
theorem fixedComponentClassification_of_source (d : Data T L V F W)
    (source : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G) :
    FixedComponentClassification d :=
  fun u _ h => d.fixedComponent_C27_of_source_dichotomy source u h

variable (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
  (baumann : ResidualNormalizer.LocalControl.Earlier14710.{u})
  (weakClosure : Theorem14731.{u})
  (localClassification : FixedComponentClassification d)
include d structural faithful modules baumann weakClosure localClassification

/-- The local C.2.7 family suffices for the original 14.7.68(2) application. -/
theorem fixedCentralizer_le_H_of_earlier_inputs
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) : d.fixedCentralizer u ≤ F.H := by
  classical
  by_contra hout
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S B hB
    exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
      (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y)) hX S hB
  obtain ⟨hNK, hmax⟩ :=
    d.normalizer_K_eq_H_of_known_simple_source structural faithful modules baumann weakClosure
  have hcomm := d.U_core_commutator_eq_point_of_source1332 modules structural uniqueness
  have hsyl := d.fixedSylow_isSylow_fivePoint_source hcomm u hu hne hfix hmax
  obtain ⟨Lu, hLu, hc, hKLu, hn⟩ :=
    d.exists_fixedComponent_of_known_simple_source u hu hne hfix hsyl
  have hLH := d.fixedComponent_not_le_H u hu hNK hout hLu hc hKLu hn
  have hlt : K F < Lu := lt_of_le_of_ne hKLu (fun he => hLH (he ▸ K_le_H F))
  by_cases hqs : IsQuasisimple Lu
  · exact d.false_of_quasisimple_fixedComponent_of_known_simple_source modules structural
      u hu hne hfix hNK hmax hsyl Lu hLu hc hn hlt hLH hqs
  · have h := d.fixedComponent_case_of_source u hu hne hfix hmax hNK hsyl
      hLu hc hlt hn hLH hqs
    exact d.false_of_nonquasisimple_fixedComponent u h (localClassification u Lu h) hcomm

/-- The original selected-data endpoint, with both amalgam inputs discharged
and C.2.7 required only on the fixed components actually used in the proof. -/
theorem source_rudvalis_of_earlier_inputs : Nonempty (G ≃* Rudvalis.Model) := by
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S B hB
    exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
      (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y)) hX S hB
  have hcomm := d.U_core_commutator_eq_point_of_source1332 modules structural uniqueness
  obtain ⟨c, selection⟩ := d.exists_selected_criticalPath structural uniqueness hcomm
  have hcentralizer := fixedCentralizer_le_H_of_earlier_inputs d structural faithful
    modules baumann weakClosure localClassification
  exact source_rudvalis_of_complete_goldschmidt d c structural faithful selection
    (d.order_two_of_source_reversal structural faithful modules baumann weakClosure
      hcentralizer c selection)
    modules (d.fusion_z_of_known_simple_source structural faithful modules baumann weakClosure)
    hcentralizer

/-- The actual Rudvalis isomorphism supplies the exceptional branch of D. -/
theorem source_theoremDModel_of_earlier_inputs : ClassificationModels.IsTheoremDModel G :=
  .exceptional (.sporadic .ru (by simp)
    (source_rudvalis_of_earlier_inputs d structural faithful modules baumann weakClosure
      localClassification))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
