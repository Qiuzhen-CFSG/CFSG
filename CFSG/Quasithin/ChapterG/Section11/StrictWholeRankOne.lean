module
public import CFSG.Quasithin.ChapterG.Section11.WholeRankOne
public import CFSG.Quasithin.ChapterG.Section11.StrictWholeComponent

/-!
# The original strict whole action has no normal Bender component

The original strict quotient supplies its marked point and rank-two type-a₂
involution. The exchanged, solvable, old-catalogue and exceptional branches
are eliminated by their proved source theorems. On the surviving whole
component, the rank-one exclusion removes every normal Bender-family row.
The statement retains the same action, form, point, crossing actor and
moved-plane nontransitivity for the remaining G.11.7 branches.

Source: Aschbacher--Smith G.11.7, pp.366--368, and 6.2.18--19, pp.690--691.
This is a further source reduction, not the final strict contradiction.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The literal strict whole component cannot be a normal binary rank-one,
unitary rank-one or Suzuki component. Every original marking is retained. -/
theorem LocalAnalysis.strict_whole_component_without_bender
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
                (componentOrbit K ⊤ = K → ¬ ClassificationModels.IsBenderModel K)) := by
  obtain ⟨he,hX,B,v,h,hv,hB,hd,cover,hSv,hXS,hXn,
    a,ha,ha1,ha2,hplane,hr,hva,htype,hnt⟩ :=
    A.strict_g11_inputs h611 hnatural hz horder hTH hstrict hdres hdH hdS hd3
  let := he
  let := hX
  refine ⟨he,hX,B,v,h,hv,hB,⟨_,hSv,hXS,hXn⟩,
    ⟨a,ha,ha1,ha2,hplane,hr,hva,htype,hnt⟩,?_⟩
  rcases ChapterG.Section11.ExchangedRecognition.corrected_conclusion_or_whole_of_type_a2
    h cover ⟨_,hSv,hXS,hXn⟩ a ha ha2 hr hva htype hnt with
      (hc | hex) | ⟨hi,hsix,hn,K,hK,hm,horth,h9⟩
  · exact (StrictCatalogue.false_of_conclusion h hd a ha ha1 ha2 hr htype hnt hc).elim
  · exact (A.not_strict_marked_full_four h611 hnatural hz horder hTH hstrict B v _ _ _ hex).elim
  · refine ⟨hi,hsix,hn,K,hK,hm,horth,h9,?_⟩
    intro hsingle hmodel
    rw [hsingle] at h9
    exact ChapterG.Section11.WholeRankOne.not_bender_model h h9 ⟨a,ha,hr.le,hva⟩ hsix hmodel

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
