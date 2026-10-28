module
public import Theory.GroupTheory.SubgroupTransport.NormalGapLayers
/-!
# The exact Niles gap parameter

The action on the second normal factor has kernel the Sylow intersection.
If the sharp bound were strict, the stronger derived interval would lie
in the smaller normal layer, making the entire right Sylow act trivially.
Thus 5v = 2k and v is even. All interval endpoints refer to the original
partial isomorphism and retain the full central attachments.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 5.7, p.52.
This uses the exact action kernel of 5.5 and the derived bound of 5.4.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

theorem intervalDiagram_gap_parameter_eq (φ : S ≃* T) (v k : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v) (hsharp : 5*v ≤ 2*k)
    (hne : ¬ T ≤ S)
    (hkernel : commutatorPreimage ⊤
      (intervalDiagram φ (3*v) (3*v-k) k)
      (intervalDiagram φ (3*v) (3*v-k+1) (k-1)) = S ⊓ T)
    (hderived : ⁅T,T⁆ ≤ intervalDiagram φ (3*v) (k-2*v+1) (5*v-k)) :
    5*v = 2*k ∧ Even v := by
  have heq : 5*v = 2*k := by
    by_contra hh
    have hTT : ⁅T,T⁆ ≤ intervalDiagram φ (3*v) (3*v-k+1) (k-1) :=
      hderived.trans (intervalDiagram_mono φ (by omega) (by omega))
    have hM : intervalDiagram φ (3*v) (3*v-k) k ≤ T := by
      apply (intervalDiagram_mono φ (show 1 ≤ 3*v-k by omega)
        (show k ≤ 3*v by omega)).trans
      simp only [intervalDiagram,Nat.sub_self,intervalCell_initial_right]
      exact le_rfl
    have hact := le_commutatorPreimage (show T ≤ (⊤ : Subgroup G) from le_top)
      ((commutator_mono le_rfl hM).trans hTT)
    rw [hkernel] at hact
    exact hne (hact.trans inf_le_left)
  refine ⟨heq,?_⟩
  exact ⟨k-2*v,by omega⟩
end Theory.GroupTheory.SubgroupTransport
