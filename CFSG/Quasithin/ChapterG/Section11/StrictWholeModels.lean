module
public import CFSG.Quasithin.ChapterG.Section11.WholeModels
public import CFSG.Quasithin.ChapterG.Section11.StrictWholeRankOne

/-!
# Surviving whole-component carriers on the literal strict quotient

The original rank-two/type-a₂ involution and marked plane are retained.
For a single whole component, the actual known-simple cover now gives the
reduced carrier list in `WholeModels`: the Bender, nonbinary G₂, binary SL₃
and SL₅, central three-covers, even-degree Mathieu and other G.9 exclusions are discharged.
The remaining modules and the two-component action still require analysis.

Source: Aschbacher--Smith G.11.7, pp.366--368, and 6.2.18--19, pp.690--691.
This theorem is a source reduction, not the final strict contradiction.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The literal strict whole action retains all original markings and has
only the displayed single-component carriers, or a nonsingle component orbit. -/
theorem LocalAnalysis.strict_whole_component_models
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
          ChapterG.Section11.NormalSylow ρ v X ∧
          (∃ a ∈ X, a ≠ 1 ∧ a^2 = 1 ∧
            RankTwo.movedSpace ρ a = strictCentralPlane (T : Subgroup G) L R z ∧
            finrank (ZMod 2) (RankTwo.movedSpace ρ a) = 2 ∧
            v ∈ RankTwo.movedSpace ρ a ∧ (∀ u, B u (ρ a u) = 0) ∧
            ¬ RankTwo.StabilizerTransitive ρ (RankTwo.movedSpace ρ a)) ∧
          (IsIrreducible ρ ∧
              6 ≤ finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)) ∧
              ¬ Group.IsSolvable (StrictActor (T : Subgroup G) L R z) ∧
              ∃ K : Subgroup (StrictActor (T : Subgroup G) L R z),
                IsComponent (StrictActor (T : Subgroup G) L R z) K ∧ ⁅K,X⁆ ≠ ⊥ ∧
                ChapterG.Section10.ComponentOrthogonalData ρ B K ∧
                ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X K
                  (componentOrbit K ⊤) (finrank (ZMod 2) (Additive X)) ∧
                (componentOrbit K ⊤ = K → IsSimpleGroup K ∧ ChapterG.Section11.WholeModels.Remaining K)) := by
  obtain ⟨he,hX,B,v,h,hv,hB,hS,ha,hi,hsix,hn,K,hK,hm,horth,h9,_⟩ :=
    A.strict_whole_component_without_bender h611 hnatural hz horder hTH hstrict
      hdres hdH hdS hd3
  let := he
  let := hX
  refine ⟨he,hX,B,v,h,hv,hB,hS,ha,hi,hsix,hn,K,hK,hm,horth,h9,?_⟩
  intro hsingle
  rw [hsingle] at h9
  obtain ⟨a,ha,_,ha2,_,hr,hva,_,hnt⟩ := ha
  exact ChapterG.Section11.WholeModels.remaining_single_component h h9
    ⟨a,ha,hr.le,hva⟩ hsix a ha2 hr hnt

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
