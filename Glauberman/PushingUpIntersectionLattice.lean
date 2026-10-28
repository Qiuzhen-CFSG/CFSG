module
public import Glauberman.FixedNormalPairLattice
public import Glauberman.PushingUpIntersectionRows

/-!
# Initial lattice reconstruction under the original Main Hypothesis

The literal twisted conjugacy between the original Sylow and a generating
conjugate satisfies the numerical pair hypotheses by the proved omega-action
recognition. Finite descent and the relative-index criterion reconstruct the
intersection diagram through its elementary row, preserving the same map.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6 and the
first lattice-depth argument on printed page 46. The deeper lattice bound
and the nilpotence-class argument are not conclusions of this module.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

theorem original_psl2_four_elementary_lattice
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α) :
    ∃ g : H,
      (S : Subgroup H) ⊔ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = ⊤ ∧
      (S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = pCore 2 H ∧
      ∃ v : ℕ, 0 < v ∧
        IsElementaryAbelian 2 ↥(intervalCell (twistedConjugacy (S : Subgroup H) α g) 1 v) ∧
        rectangleStepIndex (twistedConjugacy (S : Subgroup H) α g) (v + 1) = 4 ∧
        ∀ a b : ℕ, 1 ≤ a + b → a + b ≤ v →
          intervalCell (twistedConjugacy (S : Subgroup H) α g) a (b + 1) ⊔
            intervalCell (twistedConjugacy (S : Subgroup H) α g) (a + 1) b =
              intervalCell (twistedConjugacy (S : Subgroup H) α g) a b := by
  obtain ⟨q, hq, hk, _, _, _, E, hE⟩ := original_psl2_four_omegaAction_recognition
    hF S hu K e hf hno.noCharacteristicNormal
  obtain ⟨g, hgen, hinter, hpair⟩ := original_numerical_pair_of_natural_quotient
    hF S α hu K e hno q hq hk E hE
  let P : IntersectionPair H :=
    ⟨S, (S : Subgroup H).map (MulAut.conj g).toMonoidHom,
      twistedConjugacy (S : Subgroup H) α g⟩
  have hp : NumericalPair P.left P.right P.equiv := hpair
  obtain ⟨v, hv, hEv, hi, hj⟩ := IntersectionPair.exists_elementary_lattice_row P hp
  exact ⟨g, hgen, hinter, v, hv, hEv, hi, hj⟩

end Glauberman
