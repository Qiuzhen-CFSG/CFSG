module
public import Glauberman.FixedNormalPairDiagramCommutators
public import Glauberman.PushingUpIntersectionRows

/-!
# Original center cells, deeper reconstruction and commutator estimate

The source omega-action recognition and numerical pair descent are applied
to the actual twisted conjugacy. The resulting single parameter retains the
elementary maximum cell, reconstruction through 2v - 1, all three exact
center markings, and the transported commutator bound. Only the original
Main Hypothesis is assumed.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6(b),(d)–(f)
and the intermediate lattice bound in (g), printed pages 46–47. The natural
commutator covering needed for depth 3v - 1 remains a subsequent step.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

theorem original_psl2_four_double_lattice_center_commutator
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
        let φ := twistedConjugacy (S : Subgroup H) α g
        IsElementaryAbelian 2 ↥(intervalCell φ 1 v) ∧
        intervalCell φ 1 v ∈ thompsonAbelianSubgroups (S : Subgroup H) ∧
        intervalCell φ 1 v ∈ thompsonAbelianSubgroups
          ((S : Subgroup H).map (MulAut.conj g).toMonoidHom) ∧
        (∀ a b : ℕ, 1 ≤ a + b → a + b < 2 * v →
          intervalCell φ a (b + 1) ⊔ intervalCell φ (a + 1) b = intervalCell φ a b) ∧
        centerIn (S : Subgroup H) = intervalCell φ v (v + 1) ∧
        centerIn ((S : Subgroup H).map (MulAut.conj g).toMonoidHom) =
          intervalCell φ (v + 1) v ∧
        centerIn (pCore 2 H) = intervalCell φ v v ∧
        ⁅intervalCell φ 0 (2 * v), intervalCell φ v v⁆ ≤ intervalCell φ v (2 * v) := by
  obtain ⟨q, hq, hk, _, _, _, E, hE⟩ := original_psl2_four_omegaAction_recognition
    hF S hu K e hf hno.noCharacteristicNormal
  obtain ⟨g, hgen, hinter, hpair⟩ := original_numerical_pair_of_natural_quotient
    hF S α hu K e hno q hq hk E hE
  let P : IntersectionPair H :=
    ⟨S, (S : Subgroup H).map (MulAut.conj g).toMonoidHom,
      twistedConjugacy (S : Subgroup H) α g⟩
  have hp : NumericalPair P.left P.right P.equiv := hpair
  obtain ⟨v, hv, hEv, hSv, hTv, hj, hzS, hzT, hzQ, hcomm⟩ := P.exists_double_lattice_center_commutator hp
  have hzcore : centerIn (pCore 2 H) = intervalCell P.equiv v v := by
    calc
      centerIn (pCore 2 H) = centerIn (P.left ⊓ P.right) := congrArg centerIn hinter.symm
      _ = _ := hzQ
  exact ⟨g, hgen, hinter, v, hv, hEv, hSv, hTv, hj, hzS, hzT, hzcore, hcomm⟩

end Glauberman
