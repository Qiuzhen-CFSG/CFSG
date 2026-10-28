module
public import CFSG.Quasithin.ChapterG.Section11.ExchangedTypeA2
public import CFSG.Quasithin.ChapterG.Section10.RankTwoSolvableSource
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictExceptionalExclusion

/-!
# The strict source reduces to the exceptional action or a whole component

The original LocalAnalysis and Hypothesis611 supply the literal G.11 inputs.
Type-a₂ parity excludes all nondegenerate exchanged constituents. The
normal-cubic source theorem excludes the solvable remainder using the actual
moved plane's nontransitivity. The original thirteen-row elimination removes
the successful old alternatives.

The first reduction retains the marked exceptional whole S₈ action or the
whole-component G.9 hypothesis. Applying the independently proved ambient
central-cover exclusion then removes the exceptional action, leaving only
the whole-component case on the original strict quotient. Neither exhaustive
classification nor the final strict contradiction is asserted.
Source: Aschbacher--Smith 6.2.18--19, pp.690--691, G.10.15 and G.11.6--7,
pp.362--367, with the full-four correction in the proof basis.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The literal strict action is exceptional or still requires one of the
specified source recognitions. The printed thirteen rows are already excluded. -/
theorem LocalAnalysis.strict_corrected_whole_component_remaining
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    (hdS : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd3 : orderOf d = 3) :
    ∃ he : IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z),
      letI := he
      ∃ hX : IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L R z d),
        letI := hX
        ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)))
          (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z)),
          let ρ := strictRepresentation (T : Subgroup G) L R z
          let X := strictCrossingImage (T : Subgroup G) L R z d
          let X₀ := (strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf X
          let W := strictHatSpace (T : Subgroup G) L R z
            (strictCrossingIntersection (T : Subgroup G) L R z d)
          ChapterG.Section10.Hypothesis ρ B v W X X₀ ∧
          v ∈ strictSourceLine (T : Subgroup G) L R z ∧
          (∀ u w : sourceClosure (T : Subgroup G) L R z,
            B (strictHatElement (T : Subgroup G) L R z u)
              (strictHatElement (T : Subgroup G) L R z w) = 0 ↔ Commute u w) ∧
          (ChapterG.Section11.FullLinearFour.MarkedAlternative ρ B v W X X₀ ∨
            (IsIrreducible ρ ∧
              6 ≤ finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)) ∧
              ¬ Group.IsSolvable (StrictActor (T : Subgroup G) L R z) ∧
              ∃ K : Subgroup (StrictActor (T : Subgroup G) L R z),
                IsComponent (StrictActor (T : Subgroup G) L R z) K ∧ ⁅K,X⁆ ≠ ⊥ ∧
                ChapterG.Section10.ComponentOrthogonalData ρ B K ∧
                ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X K
                  (componentOrbit K ⊤) (finrank (ZMod 2) (Additive X)))) := by
  obtain ⟨he,hX,B,v,h,hv,hB,hd,cover,hSv,hXS,hXn,
    a,ha,ha1,ha2,_,hr,hva,htype,hnt⟩ :=
    A.strict_g11_inputs h611 hnatural hz horder hTH hstrict hdres hdH hdS hd3
  let := he
  let := hX
  refine ⟨he,hX,B,v,h,hv,hB,?_⟩
  rcases ChapterG.Section11.ExchangedRecognition.corrected_conclusion_or_whole_of_type_a2
    h cover ⟨_,hSv,hXS,hXn⟩ a ha ha2 hr hva htype hnt with (hc | hex) | hrem
  · exact (StrictCatalogue.false_of_conclusion h hd a ha ha1 ha2 hr htype hnt hc).elim
  · exact Or.inl hex
  · exact Or.inr hrem

/-- The literal ambient strict source has a whole component: the nondegenerate
exchanged, solvable, original catalogue and exceptional full-four cases are discharged. -/
theorem LocalAnalysis.strict_whole_component_source
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    (hdS : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd3 : orderOf d = 3) :
    ∃ he : IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z),
      letI := he
      ∃ hX : IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L R z d),
        letI := hX
        ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)))
          (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z)),
          let ρ := strictRepresentation (T : Subgroup G) L R z
          let X := strictCrossingImage (T : Subgroup G) L R z d
          let X₀ := (strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf X
          let W := strictHatSpace (T : Subgroup G) L R z
            (strictCrossingIntersection (T : Subgroup G) L R z d)
          ChapterG.Section10.Hypothesis ρ B v W X X₀ ∧
          v ∈ strictSourceLine (T : Subgroup G) L R z ∧
          (∀ u w : sourceClosure (T : Subgroup G) L R z,
            B (strictHatElement (T : Subgroup G) L R z u)
              (strictHatElement (T : Subgroup G) L R z w) = 0 ↔ Commute u w) ∧
          (IsIrreducible ρ ∧
              6 ≤ finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)) ∧
              ¬ Group.IsSolvable (StrictActor (T : Subgroup G) L R z) ∧
              ∃ K : Subgroup (StrictActor (T : Subgroup G) L R z),
                IsComponent (StrictActor (T : Subgroup G) L R z) K ∧ ⁅K,X⁆ ≠ ⊥ ∧
                ChapterG.Section10.ComponentOrthogonalData ρ B K ∧
                ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X K
                  (componentOrbit K ⊤) (finrank (ZMod 2) (Additive X))) := by
  obtain ⟨he,hX,B,v,h,hv,hB,hcases⟩ :=
    A.strict_corrected_whole_component_remaining h611 hnatural hz horder hTH hstrict
      hdres hdH hdS hd3
  let := he
  let := hX
  refine ⟨he,hX,B,v,h,hv,hB,?_⟩
  rcases hcases with hex | hwhole
  · exact (A.not_strict_marked_full_four h611 hnatural hz horder hTH hstrict B v _ _ _ hex).elim
  · exact hwhole

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
