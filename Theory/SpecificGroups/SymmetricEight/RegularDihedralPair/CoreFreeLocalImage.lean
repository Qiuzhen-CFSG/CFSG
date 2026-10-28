module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.OneLocalExtension
public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.LocalFixedPlane
import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation

/-! The full two-core-free overgroup of an actual S4 with regular Sylow D8
is the checked order-168 image. The second local is constructed by the finite
extension sieve. The natural-plus-dual fixed-line obstruction is retained
for the same original local and the same native action. -/

public noncomputable section
open Equiv Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
open SquareModule ClassicalOrthogonal BinaryD3Comparison

/-- Full image recognition and the local fixed-line obstruction, with no
second-local or recognition premise. -/
theorem core_free_local_image {X : Subgroup P8} (hX : MaximalTwo X)
    (hcore : pCore 2 X = ⊥) (A : Subgroup P8) (hAX : A ≤ X)
    (hTA : twoGroup ≤ A) (eA : A ≃* Perm (Fin 4)) :
    Nonempty (X ≃* PSL(3, ZMod 2)) ∧
      (∃ p : P8, X.map (MulAut.conj p).toMonoidHom = modelGroup) ∧
      ∀ x : D, (∀ g ∈ A, (symmetricEquiv g).val x = x) →
        Submodule.span F (Set.range (fun g : X => (symmetricEquiv g.val).val x)) ≠ ⊤ := by
  have hne : X ≠ A := by
    intro he
    have hcoreA : pCore 2 A = ⊥ := he ▸ hcore
    have hh := pCore_map_iso 2 eA
    rw [hcoreA, Subgroup.map_bot] at hh
    have hfour := SymmetricSix.DuadCalculation.core_card
    rw [SymmetricSix.DuadCalculation.core_eq, ← hh, card_bot] at hfour
    omega
  obtain ⟨B, hBX, hTB, ⟨eB⟩, hAB⟩ := proper_overgroup_second_local hX A hAX hTA eA hne
  exact ⟨(marked_pair_recognition hX A B hAX hBX hTA hTB eA eB hAB).2,
    marked_pair_conjugate hX A B hAX hBX hTA hTB eA eB hAB,
    fun x hfix => marked_pair_local_fixed_span_ne_top hX A B hAX hBX hTA hTB eA eB hAB x hfix⟩

end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
