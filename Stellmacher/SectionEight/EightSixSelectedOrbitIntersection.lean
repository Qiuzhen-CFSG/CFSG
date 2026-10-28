module
public import Stellmacher.SectionEight.EightSixActorCostSymmetry
public import Stellmacher.SectionEight.EightSixSelectedOrbitBackwardCost
public import Stellmacher.SectionEight.EightSixCommonStructure

/-!
In the high-cost branch of Stellmacher (8.6), the selected orbit U of the
initial center lies in D, the intersection of the neighboring two-cores.
Cubic symmetry transfers the uniform displacement lower bound eight to the
opposite direction. Every element of U has backward displacement at most
four, so it lies in the predecessor core; the orbit already lies in the
next core. The common identity [D,L]=Z_a, with Z_a contained in U, then
makes U normal in L.

The actual geometric witness, initial-core containment, and equation-one
packet are retained. The high-cost bound is the genuine remaining branch
premise, rather than an assumed orbit containment or classification model.
Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), printed p.44,
assertion (16) and the following normality sentence.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_six_selected_orbit_le_intersection
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover) :
    conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤ D := by
  have hUV : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := eight_six_conjugate_closure_le _ _ _
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1
    (geom.group_le.trans (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep))
  have hVR := SevenSix.neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath
    (show 1 < ctx.criticalPath.length by omega) ctx.criticalPath.firstStep
  have hback := eight_six_actor_cost_bound_symmetry ctx hquot previous hprev 8 hhigh
  rw [hD]
  refine le_inf ?_ (hUV.trans hVR)
  intro mover hmover
  by_contra hout
  have hh := hback mover ⟨hUV hmover,hcore hmover⟩ hout
  have hs := eight_six_selected_orbit_backward_cost_le_four ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL mover hmover
  omega

public theorem eight_six_selected_orbit_normal_in_closure
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (hQ : Q = twoCoreIn L) :
    NormalIn (conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E) L := by
  let U := conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E
  have hUD : U ≤ D := eight_six_selected_orbit_le_intersection ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh
  have hseed : ZAt ctx.Γ ctx.criticalPath.a ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hDL : D ≤ L := by
    rw [hD,hL]
    intro d hd
    exact Subgroup.subset_closure ⟨(1:GAt ctx.Γ ctx.criticalPath.a),⟨d,hd.1⟩,by simp⟩
  have hcomm := (eight_six_common_structure_local ctx hcenter hquot hlength hcard
    previous hprev D L Q hD hL hQ).2.1
  exact ⟨hUD.trans hDL, Subgroup.normal_subgroupOf_of_le_normalizer
    (Subgroup.le_normalizer_iff_commutator_le_left.mpr
      (((Subgroup.commutator_mono hUD le_rfl).trans_eq hcomm).trans hseed))⟩

end Stellmacher.SectionEight
