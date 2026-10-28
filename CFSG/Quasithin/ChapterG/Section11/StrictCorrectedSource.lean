module
public import CFSG.Quasithin.ChapterG.Section11.StrictCorrectedReduction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictElimination

/-!
# The corrected G.11 remainder from the original strict local analysis

The original LocalAnalysis and Hypothesis611 construct the commutator form,
marked point, elementary quotient, SQTK cover, low-rank element and relative
normal Sylow actor. Applying the corrected reduction to these literal inputs
and the already proved thirteen-row exclusions leaves the marked exceptional
S₈ action or one of the still unresolved source recognition branches.

There is no catalogue assumption. This does not prove the final strict
contradiction: the classification owner retains the remaining recognition,
and the strict-elimination owner retains ambient exclusion of the exceptional
whole action, using the original crossing and lifting data.
Source: Aschbacher--Smith 6.2.18--19, printed pp.690--691, and the
G.10.15 correction in `docs/quasithin-proof-basis.md`.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The literal strict action is exceptional or still requires one of the
specified source recognitions. The printed thirteen rows are already excluded. -/
theorem LocalAnalysis.strict_corrected_remaining
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
              ((Group.IsSolvable (StrictActor (T : Subgroup G) L R z) ∧
                  finrank (ZMod 2) (Additive X) = 2 ∧
                  finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)) = 6) ∨
                (¬ Group.IsSolvable (StrictActor (T : Subgroup G) L R z) ∧
                  ChapterG.Section11.ExchangedRecognition.RemainingComponentModels ρ B v W X)))) := by
  obtain ⟨he,hX,B,v,h,hv,hB,hd,cover,hSv,hXS,hXn,
    a,ha,ha1,ha2,_,hr,hva,htype,hnt⟩ :=
    A.strict_g11_inputs h611 hnatural hz horder hTH hstrict hdres hdH hdS hd3
  let := he
  let := hX
  refine ⟨he,hX,B,v,h,hv,hB,?_⟩
  rcases ChapterG.Section11.ExchangedRecognition.corrected_conclusion_or_remaining
    h cover ⟨a,ha,hr.le,hva⟩ ⟨_,hSv,hXS,hXn⟩ with (hc | hex) | hrem
  · exact (StrictCatalogue.false_of_conclusion h hd a ha ha1 ha2 hr htype hnt hc).elim
  · exact Or.inl hex
  · exact Or.inr hrem

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
