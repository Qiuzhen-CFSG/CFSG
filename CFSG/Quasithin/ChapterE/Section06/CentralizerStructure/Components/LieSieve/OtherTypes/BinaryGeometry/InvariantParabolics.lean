module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.Parabolics
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.InvariantParabolics.FlagCalculations
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.InvariantParabolics.Transport

/-!
# Actual invariant generating parabolics for the binary cases of E.6.8

The source Sylow intersection L ∩ Q determines a full binary flag. The
conjugation action of Q preserves that Sylow subgroup, hence the paired
(1,4) and (2,3) flags in dimension five. In dimension four an inner action
preserves the line and hyperplane of the flag. The corresponding stabilizers
generate the component model and have characteristic two.

Their actual quotient images are Q-invariant. Pulling these images back
adds precisely the core of LQ, already contained in Q. The relative
component-orbit theorem therefore proves characteristic two of each lifted
join. No invariant flags, action kernel, generation, or local-core conclusion
is assumed. The independent exclusion of chi-zero blocks belongs to the
source theorem's final assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {M V U Q L : Subgroup G}

/-- The literal paired flags supply the invariant generating family in PSL₅(2),
including characteristic two for the actual lifted joins. -/
theorem five_invariant_generating_parabolics (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G)) (hm : ClassicalGroup.IsPSL L 5 2) :
    ∃ b : BinaryLinear.FiveFlagGeometry.FiveBasis,
      (⨆ i, fivePairedParabolic b i) = ⊤ ∧
      (∀ i, sylowImage Q L ≤ normalizer
        (quotientParabolic Q (by decide) hm (fivePairedParabolic b i) :
          Set (ComponentQuotient Q L))) ∧
      (∀ i, HasCharacteristicTwo
        ↥(quotientPreimage Q L (quotientParabolic Q (by decide) hm
          (fivePairedParabolic b i)) ⊔ Q)) := by
  obtain ⟨_, S, hS, _⟩ := component_sylow_action h hU hL hQ
  let e := binaryEquiv (by decide : 0 < 5) hm
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨b, hb⟩ := BinaryLinear.FiveFlagGeometry.sylow_eq_flagStabilizer R
  have hflag (g : (L ⊔ Q : Subgroup G)) (hg : (g : G) ∈ Q) :
      (BinaryLinear.FiveFlagGeometry.flagStabilizer b Set.univ).map
        (binaryAction (by decide) hm hN g).toMonoidHom =
          BinaryLinear.FiveFlagGeometry.flagStabilizer b Set.univ := by
    rw [← hb]
    exact binaryAction_preserves_sylow (by decide) hm hN S hS g hg
  have hinv (i : Fin 2) : Q ≤ normalizer
      ((fivePairedParabolic b i).map (modelInclusion (by decide) hm) : Set G) :=
    modelSubgroup_normalized (by decide) hm hN _
      (fun g hg => fivePairedParabolic_invariant b _ (hflag g hg) i)
  refine ⟨b, fivePairedParabolic_generate b R hb, ?_, ?_⟩
  · exact fun i => quotientParabolic_normalized (by decide) hm _ (hinv i)
  · exact fun i => quotientParabolic_join_characteristicTwo h hU hL hQ hN
      (by decide) hm _ (hinv i) (fivePairedParabolic_characteristicTwo b i)

/-- In the actual inner-action branch of PSL₄(2), the line and hyperplane
stabilizers supply the invariant generating family and characteristic-two lifts. -/
theorem four_inner_invariant_generating_parabolics (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G)) (hm : ClassicalGroup.IsPSL L 4 2)
    (hinner : (binaryAction (by decide) hm hN).range ≤
      MulAut.innerSubgroup (LinearGroup 4)) :
    ∃ b : BinaryLinear.InvariantNodeActions.Basis 3,
      (⨆ i, fourEndParabolic b i) = ⊤ ∧
      (∀ i, sylowImage Q L ≤ normalizer
        (quotientParabolic Q (by decide) hm (fourEndParabolic b i) :
          Set (ComponentQuotient Q L))) ∧
      (∀ i, HasCharacteristicTwo
        ↥(quotientPreimage Q L (quotientParabolic Q (by decide) hm
          (fourEndParabolic b i)) ⊔ Q)) := by
  obtain ⟨_, S, hS, _⟩ := component_sylow_action h hU hL hQ
  let e := binaryEquiv (by decide : 0 < 4) hm
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨b, hb⟩ := BinaryLinear.InvariantNodeActions.sylow_eq_cutStabilizer R
  have hflag (g : (L ⊔ Q : Subgroup G)) (hg : (g : G) ∈ Q) :
      (BinaryLinear.InvariantNodeActions.cutStabilizer b Set.univ).map
        (binaryAction (by decide) hm hN g).toMonoidHom =
          BinaryLinear.InvariantNodeActions.cutStabilizer b Set.univ := by
    rw [← hb]
    exact binaryAction_preserves_sylow (by decide) hm hN S hS g hg
  have hinv (i : Fin 2) : Q ≤ normalizer
      ((fourEndParabolic b i).map (modelInclusion (by decide) hm) : Set G) :=
    modelSubgroup_normalized (by decide) hm hN _
      (fun g hg => fourEndParabolic_invariant b _ (hflag g hg) (hinner ⟨g, rfl⟩) i)
  refine ⟨b, fourEndParabolic_generate b, ?_, ?_⟩
  · exact fun i => quotientParabolic_normalized (by decide) hm _ (hinv i)
  · exact fun i => quotientParabolic_join_characteristicTwo h hU hL hQ hN
      (by decide) hm _ (hinv i) (fourEndParabolic_characteristicTwo b i)

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry
