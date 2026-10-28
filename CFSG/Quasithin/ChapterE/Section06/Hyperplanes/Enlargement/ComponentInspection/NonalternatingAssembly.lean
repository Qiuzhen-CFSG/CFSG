module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.Reduction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.Nonalternating
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.Borel
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.OddLinear

/-!
# Component enlargement after all nonalternating inspections

The small Borel models (including all central two-covers of PSL₃(4)), actual
derived symplectic models, PSL₄(2), and all three odd-model families satisfy
the intrinsic fixed-component exclusions. This assembly supplies those proofs
to the E.6.22 reduction. Only the separately owned alternating inspections and
earlier source results remain explicit inputs in the final theorem. The earlier
partial assembly is retained with its original interface.

This is a conditional reduction, not the completed source theorem.
Source: Aschbacher–Smith, E.6.22, printed p.254 (PDF p.265).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
open ComponentBalance Components Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}

/-- The remaining nonalternating obligations are precisely Borel and odd-linear
model calculations; no persistence premise is introduced. -/
theorem component_lift_of_borel_and_oddLinear_inspections
    [IsElementaryAbelian 2 V] (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    (hbalance : EarlierBalance K) (ho : OddCoreFree V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      ¬ X ≤ M ∧ ComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X)
    (hborel : ∀ (X : Subgroup G), IsQuasisimple X → ∀ n : ℕ, n ≤ 2 →
      BorelComponentModel X n → NoCentralInvolutionComponent X)
    (hoddLinear : ∀ (X : Subgroup G), IsQuasisimple X →
      ((∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL X 2 p) ∨
        ClassicalGroup.IsPSL X 3 3) → NoCentralInvolutionComponent X)
    (hsix : ∀ (X : Subgroup G), IsQuasisimple X →
      IsAlternating X 6 → NoCentralInvolutionComponent X)
    (hseven : ∀ (X : Subgroup G), IsQuasisimple X →
      IsAlternating X 7 → CentralInvolutionFive X) : ComponentLiftAlternative M V := by
  apply component_lift_of_inspections h h15 hbalance ho h68 hborel
    (fun X _ n hn hm => symplectic_noCentralInvolutionComponent X n hn hm)
    (fun _ _ hm => linear_four_noCentralInvolutionComponent hm) hsix hseven
  intro X hX hm
  rcases hm with hp | hthree | he
  · exact hoddLinear X hX (Or.inl hp)
  · exact hoddLinear X hX (Or.inr hthree)
  · exact mathieu_eleven_noCentralInvolutionComponent he.some

/-- All nonalternating inspections in E.6.22 are discharged. The only model
inputs left are the degree-six and degree-seven alternating inspections; the
earlier balance, odd-core and full E.6.8 source statements remain explicit. -/
theorem component_lift_of_alternating_inspections
    [IsElementaryAbelian 2 V] (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    (hbalance : EarlierBalance K) (ho : OddCoreFree V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      ¬ X ≤ M ∧ ComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X)
    (hsix : ∀ (X : Subgroup G), IsQuasisimple X →
      IsAlternating X 6 → NoCentralInvolutionComponent X)
    (hseven : ∀ (X : Subgroup G), IsQuasisimple X →
      IsAlternating X 7 → CentralInvolutionFive X) : ComponentLiftAlternative M V := by
  exact component_lift_of_borel_and_oddLinear_inspections h h15 hbalance ho h68
    (fun X hX _ hn hm => borel_noCentralInvolutionComponent X hX hn hm)
    oddLinear_noCentralInvolutionComponent hsix hseven

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
