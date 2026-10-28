module
public import CFSG.Quasithin.ChapterG.Section11.WholeSingleExclusion
public import CFSG.Quasithin.ChapterG.Section11.WholePair
public import CFSG.Quasithin.ChapterG.Section11.StrictWholeModels

/-!
# The distinct component pair on the original strict quotient

All single whole-component actions have been excluded from the literal
strict quotient. The remaining join has two distinct isomorphic components,
with a constructed common-field tensor action, centerless factors, the
original actor-rank bound, and factor dimension two. The alternating
form, central plane, marked point, type-a2 involution and relative normality
are precisely those constructed from the original strict source.

The natural recognition and tensor exclusion are applied in
`StrictWholeExclusion`, which proves the strict contradiction.
Source: Aschbacher--Smith G.9.3, G.11.7 and 6.2.18--19,
printed pp.354--356,366--368,690--691.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The original strict source forces a genuine pair of components and
its small-factor tensor realization, retaining every original marking. -/
theorem LocalAnalysis.strict_whole_component_pair
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
                componentOrbit K ⊤ ≠ K ∧
                ∃ K₂ : Subgroup (StrictActor (T : Subgroup G) L R z),
                  IsComponent (StrictActor (T : Subgroup G) L R z) K₂ ∧
                  componentOrbit K ⊤ = K ⊔ K₂ ∧ K ≠ K₂ ∧ Nonempty (K ≃* K₂) ∧
                  center K = ⊥ ∧ finrank (ZMod 2) (Additive X) ≤ 2 * primeRank 2 K ∧
                  ∃ D : ChapterG.Section09.TwoComponents.TensorData ρ K K₂,
                    D.k = 2) := by
  obtain ⟨he,hX,B,v,h,hv,hB,hS,ha,hi,hsix,hn,K,hK,hm,horth,h9,_⟩ :=
    A.strict_whole_component_models h611 hnatural hz horder hTH hstrict
      hdres hdH hdS hd3
  let := he
  let := hX
  have hne : componentOrbit K ⊤ ≠ K := by
    intro hsingle
    have hsingle9 := h9
    rw [hsingle] at hsingle9
    obtain ⟨a,ha,_,ha2,_,hr,hva,htype,hnt⟩ := ha
    exact ChapterG.Section11.WholeSingleExclusion.false_of_single_component h hsingle9
      ⟨a,ha,hr.le,hva⟩ hS hsix a ha2 hr htype hnt
  exact ⟨he,hX,B,v,h,hv,hB,hS,ha,hi,hsix,hn,K,hK,hm,horth,h9,hne,
    ChapterG.Section11.WholePair.component_pair_data h9 hne
      (AlternatingForm.even_finrank B h.alternating h.nondegenerate)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
