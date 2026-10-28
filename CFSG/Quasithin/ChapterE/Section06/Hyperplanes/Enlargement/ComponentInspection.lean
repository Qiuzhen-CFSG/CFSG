module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.Alternating
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.NonalternatingAssembly

/-!
# Component enlargement and the A₅-in-A₇ exception in E.6.22

The actual Sylow-central action puts an ordinary component of C_G(U) inside
an ordinary component X of C_G(A). Since U is a hyperplane and A has corank
at most two, its induced action on X is trivial or has order two. The proved
model inspections then give equality or an actual A₅ isomorphism inside A₇.
E.6.21 excludes the perfect central three-covers using their odd centers and
relative subnormality; no quotient identification is used as an isomorphism.

All model inspections are discharged. Only the permitted earlier I.3.1
balance input, E.6.8 alternatives and E.6.21 odd-core conclusion remain
explicit, alongside the genuine standing E.6.1 and E.6.15 hypotheses.
The existing conditional reduction and model interfaces are re-exported.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.254
(PDF p.265), the first paragraph of the proof of E.6.22.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
open ComponentBalance Components
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}

/-- The component-lifting alternative in E.6.22, with every intrinsic model
inspection proved. Both components are relative to their actual centralizers,
and the proper-enlargement alternative retains the actual A₅ and A₇ models. -/
theorem component_lift
    [IsElementaryAbelian 2 V] (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    (hbalance : EarlierBalance K) (ho : OddCoreFree V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      ¬ X ≤ M ∧ ComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X) :
    ComponentLiftAlternative M V := by
  exact component_lift_of_alternating_inspections h h15 hbalance ho h68
    (fun _ _ hm => alternating_six_noCentralInvolutionComponent hm)
    (fun _ _ hm => alternating_seven_centralInvolutionFive hm)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
