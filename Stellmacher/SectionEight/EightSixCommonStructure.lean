module
public import Stellmacher.SectionEight.GeneratedEightSixUpstreamAction
public import Stellmacher.SectionEight.GeneratedEightSixCoreOrbitCover
public import Stellmacher.SectionEight.GeneratedEightSixCoreOrbitSpan
public import Stellmacher.SectionEight.GeneratedEightSixCoreQuotientAlgebra
public import Stellmacher.SectionEight.GeneratedEightSixFrattiniIntersection

/-!
# Common structural conclusions in Stellmacher (8.6)

For the actual length-two local graph configuration, an initial ordinary
SL₂(2) quotient and initial center of order four, this module proves the
source's equation-one data and its common conclusions: [D,L] = Z_a,
Q/D is elementary abelian, and D is elementary abelian. The actual prescribed
D, L and Q are retained. The local context serves both the canonical and
ambient-backed generated developments without changing either graph.

The upstream action identities give normality of D, the Sylow intersection
and two commutator identities. The orbit-cover and orbit-span lemmas now
supply the full three-factor generation of Q. Commutator-image and square
bounds give its Frattini containment. The centralizer-rigidity argument then
computes the centralizer inside D, killing its Frattini subgroup; the full
commutator and elementary conclusions follow. No classification alternative
or common structural conclusion is assumed.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), printed pp.41–42,
equations (1)–(3); `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_six_common_structure_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L) :
    EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q ∧
      ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D := by
  have hnormal : NormalIn D (GAt ctx.Γ ctx.criticalPath.a) := by
    rw [hD]
    exact eight_six_intersection_normal_local ctx hcenter hquot hlength hcard previous hprev
  have hsylow := eight_six_sylow_intersection_local ctx hcard hlength
    previous hprev.1 L Q hL hQ
  have hfirst := eight_six_first_commutator_local ctx hcenter hcard hlength
  have hresidual : ⁅D, twoResidualIn L⁆ = ZAt ctx.Γ ctx.criticalPath.a := by
    apply le_antisymm
    · exact eight_six_residual_commutator_le_local ctx hcenter hlength hcard
        previous hprev.1 D L hD hL hnormal hfirst
    · have hcenterD := eight_six_initial_center_le_intersection_of_length_two
        ctx.Γ ctx.criticalPath hlength previous hprev.1 D hD
      have hresidual := eight_six_residual_eq_initial_of_closure ctx.sectionSeven
        ctx.Γ ctx.criticalPath previous hprev.1 L hL
      have haction := eight_six_initial_center_residual_local ctx hcenter hcard
      rw [hresidual, ← haction]
      exact Subgroup.commutator_mono hcenterD le_rfl
  have action : EightSixEquationOneActionData ctx.Γ ctx.criticalPath D L Q :=
    ⟨hnormal, hsylow, hfirst, hresidual⟩
  have hcover := eight_six_core_orbit_cover_local ctx hquot hlength previous hprev
    D L Q hD hL hQ action
  have hspan := eight_six_core_orbit_span_local ctx hquot hlength previous hprev
    D L Q hD hL hQ action
  have hgen := eight_six_generation_of_orbit_bounds ctx.sectionSeven ctx.Γ
    ctx.criticalPath (by omega) previous hprev.1 D L Q hD hL hQ action hcover hspan
  obtain ⟨actor, hactor, hintersection⟩ := eight_six_core_image_actor_local
    ctx hquot hlength previous hprev D hD action.intersection_normal
  have hcomm := eight_six_core_commutator_image_of_actor ctx hlength previous hprev.1
    D L Q hD hL hQ action hgen actor hactor hintersection
  obtain ⟨hderived, hAsquare, hBsquare⟩ := eight_six_core_derived_and_squares_local
    ctx hcenter hlength hcard previous hprev.1 D L Q hD hL hQ action hgen
  have hcore := eight_six_equation_one_core_of_generation_and_quotient_bounds
    ctx.sectionSeven ctx.Γ ctx.criticalPath previous hprev.1 D L Q hD hL hQ action
      hgen hcomm hderived hAsquare hBsquare
  have equation := eight_six_equation_one_of_action_and_core_algebra ctx hcenter
    previous hprev.1 D L Q hL action hcore.1 hcore.2.1 hcore.2.2
  have hcentralizer : D ⊓ Subgroup.centralizer
      (VAt ctx.Γ ctx.criticalPath.firstStep : Set G) =
        ZAt ctx.Γ ctx.criticalPath.firstStep := by
    apply eight_six_intersection_centralizer_of_rigidity ctx.sectionSeven ctx.Γ
      ctx.criticalPath hcenter previous D L Q hD equation
    intro U hU hUS
    have hUZ := eight_six_rigidity_le_initial_center ctx.sectionSeven ctx.Γ ctx.criticalPath
      hcenter hquot previous D L Q hD hL equation U (hU.trans inf_le_left) hUS
    exact eight_six_rigidity_le_first_center_of_le_initial ctx hcenter hlength hcard
      previous D L Q equation U hUZ (hU.trans inf_le_right)
  have hfrattini := eight_six_intersection_frattini_eq_bot_of_centralizer
    ctx.sectionSeven ctx.Γ ctx.criticalPath hcenter previous D L Q hD equation hcentralizer
  have hfullcomm := eight_six_intersection_full_commutator_of_frattini ctx.sectionSeven
    ctx.Γ ctx.criticalPath hcenter previous hprev.1 D L Q hD equation hfrattini
  exact ⟨equation, eight_six_base_of_equation_one_and_intersection_frattini
    ctx.Γ ctx.criticalPath previous D L Q hQ equation hfullcomm hfrattini⟩

end Stellmacher.SectionEight
