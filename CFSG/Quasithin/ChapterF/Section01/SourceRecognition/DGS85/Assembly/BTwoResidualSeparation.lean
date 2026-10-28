module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoRegular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoResidualSeparationSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalProfileAction

/-!
# Original distance-two residual separation

The two orientations of the critical pair have the same finite binary field.
The paired center-action constructor therefore supplies both center actions
needed in the opening of DGS (10.8).  Applying the original transport keeps
the full endpoint two-cores, the original reduced-to-completion inclusion and
the literal `O²` actor of the reverse endpoint.  The result is the exact
separation-control package used before the residual is shown to vanish.

This is only the source separation stage: it does not identify the residual
order, construct the regular path parameters, or assert a marked amalgam
recognition.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(10.2)(c) and (10.8), pp.154,159--160.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile
open ChapterF.Source
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.Assembly
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => Reduction.reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (Reduction.G₀ L S)

private theorem base_edge : (graph F).Adj α β :=
  ⟨by change false ≠ true; decide,
    Subgroup.CosetGeometry.incident_base _ _ _⟩

/-- The literal original opening of (10.8), with both center actions supplied
by the paired reduced critical profile. -/
theorem original_bTwo_residual_separation
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u)
    (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β) :
    ∃ g : graphLocalGroup F α, (g : Reduction.G₀ L S) • β = t ∧
      let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι
      let W₀ := (Z F u).map ι ⊔ (Z F ((g : Reduction.G₀ L S) • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      let J₀ := R₀ ⊓ (Q F y).map ι
      let A₀ := ((pResidual 2 (graphLocalGroup F u)).map
        (graphLocalGroup F u).subtype).map ι
      let Z' := (Z F u).map ι
      J₀ ≤ (parabolic L S 1).pCoreIn 2 ⊓ (Q F y).map ι ∧
        Disjoint J₀ Z' ∧ ⁅J₀,A₀⁆ ≤ Z' ∧
        J₀ ≤ centralizer ((A₀ ⊓ normalizer (J₀ : Set G) : Subgroup G) : Set G) := by
  obtain ⟨k₀,f₀,n₀,ch₀,a₀,k₁,f₁,n₁,ch₁,a₁,c₀,c₁,ha₀,ha₁,_,_,_⟩ :=
    Reduction.reduced_bTwo_equal_field_profile_actions h hc hne hb base_edge hβu
  have hcentral := reduced_bTwo_middle_central h hc hne hb base_edge hβu
  have hA : ((pResidual 2 c₁.actor).map c₁.actor.subtype).map ι =
      ((pResidual 2 (graphLocalGroup F u)).map
        (graphLocalGroup F u).subtype).map ι := by
    rw [ha₁]
    rfl
  obtain ⟨g,hg,hout⟩ :=
    Reduction.original_bTwo_residual_separation_control h hb c₀ c₁ ha₀
      hcentral ht htne hy hyne
  let g' : graphLocalGroup F α := ⟨g, ha₀ ▸ g.property⟩
  refine ⟨g', ?_, ?_⟩
  · exact hg
  · simpa only [hA] using hout

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
