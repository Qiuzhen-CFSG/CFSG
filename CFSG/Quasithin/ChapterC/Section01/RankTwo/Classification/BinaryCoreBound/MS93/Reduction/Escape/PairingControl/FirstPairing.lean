module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Consequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree

/-!
# The first pairing and local conclusions of MS93 (4.3.2)(2)--(3)

The two local arguments have distinct targets. The first constructs
the opposite orientation on the moving section of V/Z by the quotient pairing
and both image-order cases. The second uses that orientation to identify the
intrinsic section Vcirc/U and prove the edge assertions.

`contraryLocalFacts_of_steps` performs their assembly, including transport to
arbitrary M-vertices and the deductions H=U and |Vcirc|=64. The theorem
`first_pairing_facts` supplies both proved producers from LocalSource, the
earlier module, normalization and initial facts, and the contrary commutator
hypothesis. No orientation, quotient-pairing premise or step (3) conclusion
remains to be supplied. The rest of (4.3.2) belongs to PairingControl.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.883--884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geometry : Geometry R}

/-- Conditional transport and numerical assembly. The theorem
`first_pairing_facts` below supplies both mathematical producers. -/
theorem contraryLocalFacts_of_steps (hb : 2 < geometry.b R)
    (transfer : NormalizationTransfer R) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (orientation : ∀ q : Counterexample geometry,
      ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a → Nonempty (MovingOrientationAt q.a))
    (stepThree : (∀ a, color R a = false → Nonempty (MovingOrientationAt a)) →
      ∀ q : Counterexample geometry,
        ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a → StepThreeAt geometry q.a) :
    ContraryLocalFacts geometry := by
  have orientations : ∀ a, color R a = false → Nonempty (MovingOrientationAt a) := by
    intro a ha
    obtain ⟨q, he, hbad⟩ := contrary_at p bad a ha
    exact he ▸ orientation q hbad
  have steps : ∀ a, color R a = false → StepThreeAt geometry a := by
    intro a ha
    obtain ⟨q, he, hbad⟩ := contrary_at p bad a ha
    exact he ▸ stepThree orientations q hbad
  refine {
    opposite := fun a ha => (steps a ha).opposite
    H_eq_U := ?_
    moving_card := ?_
    edge_eq := fun a t d ha hat hdt hd => (steps a ha).edge_eq t d hat hdt hd
    moving_symmetric := fun a d ha hd => (steps a ha).moving_symmetric d hd }
  · intro a ha
    obtain ⟨q, he, hbad⟩ := contrary_at p bad a ha
    obtain ⟨o⟩ := (steps q.a q.color_a).opposite
    exact he ▸ H_eq_U_of_opposite hb transfer q hbad o
  · intro a ha
    obtain ⟨o⟩ := (steps a ha).opposite
    exact moving_card_of_opposite hb a ha o

/-- Original MS93 (4.3.2)(2)--(3), binary case, under the contrary commutator
hypothesis: opposite natural sections U and Vcirc/U with a common marking,
H = U, |Vcirc| = 64, and the edge and moving-neighbor identities at every
M-vertex. Both source stages are discharged from the earlier inputs. -/
theorem first_pairing_facts {L : Subgroup M} (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ContraryLocalFacts geometry :=
  contraryLocalFacts_of_steps hb transfer p bad
    (moving_orientation hb modules transfer initial)
    (step_three source hb modules transfer initial)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
