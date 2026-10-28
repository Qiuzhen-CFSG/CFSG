module
public import Glauberman.PushingUpIntervalNormality
public import Theory.GroupTheory.SubgroupTransport.IntervalCentralizers

/-!
# Original right-interval centralizers

The natural omega action identifies the original Sylow centralizer of
Z(O₂(H)) with O₂(H). At the first point this detects the opposite-point
centralizer kernel, because all other middle points commute. Transport
along the original partial isomorphism gives every subsequent point kernel;
successive endpoint deletion then determines the right-interval centralizer.
All preceding interval markings and bounds remain attached to the same g,v.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 5.2, printed p.49.
Natural interval endpoints here are the printed endpoints plus one. The
natural-action kernel and all local centralizer premises are discharged.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

theorem original_psl2_four_interval_centralizers
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α) :
    ∃ g : H, ∃ v : ℕ, 0 < v ∧
      let φ := twistedConjugacy (S : Subgroup H) α g
      let X := intervalDiagram φ (3 * v)
      X 0 (3 * v) = ⊤ ∧
      X 0 (3 * v - 1) = (S : Subgroup H) ∧
      X 1 (3 * v) = (S : Subgroup H).map (MulAut.conj g).toMonoidHom ∧
      X 1 (3 * v - 1) = pCore 2 H ∧
      centerIn (S : Subgroup H) = X v (2 * v - 1) ∧
      centerIn ((S : Subgroup H).map (MulAut.conj g).toMonoidHom) = X (v + 1) (2 * v) ∧
      centerIn (pCore 2 H) = X v (2 * v) ∧
      center H = X (v + 1) (2 * v - 1) ∧
      (∀ i j : ℕ, j ≤ 3 * v → j < i + 2 * v → IsElementaryAbelian 2 (X i j)) ∧
      (∀ i j k l : ℕ, i ≤ k → k ≤ j → j ≤ l → l ≤ 3 * v →
        X i j ⊔ X k l = X i l) ∧
      (∀ i j : ℕ, i ≤ j → j ≤ 3 * v → X i j = ⨆ k ∈ Set.Icc i j, X k k) ∧
      (∀ i j : ℕ, j < 3 * v → image φ (X i j) = X (i + 1) (j + 1)) ∧
      (∀ i : ℕ, i ≤ v → ⁅X i i, X (i + 2 * v) (i + 2 * v)⁆ ≤ X (i + v) (i + v)) ∧
      (∀ i j : ℕ, i < j → j ≤ 3 * v → j < i + 3 * v →
        X i j ≤ normalizer (X i (j - 1) : Set H) ∧
        X i j ≤ normalizer (X (i + 1) j : Set H) ∧
        ⁅X i i, X j j⁆ ≤ X (i + 1) (j - 1)) ∧
      (∀ r : ℕ, r ≤ v → X r r ⊓ centralizer (X (r + 2 * v) (r + 2 * v) : Set H) ≤
        X (r + 1) (r + 1)) ∧
      (∀ j : ℕ, 2 * v + 1 ≤ j → j ≤ 3 * v →
        ((S : Subgroup H).map (MulAut.conj g).toMonoidHom) ⊓ centralizer (X (v + 1) j : Set H) =
          X (j - 2 * v + 1) (3 * v)) := by
  obtain ⟨g, v, hv, htop, hS, hT, hQ, hzS, hzT, hzQ, hzH, hE, hjoin, hpoints, hshift, hcomm, hbound⟩ :=
    original_psl2_four_interval_endpoint_bounds hF S α hu K e hf hno
  let φ := twistedConjugacy (S : Subgroup H) α g
  let X := intervalDiagram φ (3 * v)
  have hinter : (S : Subgroup H) ⊓
      (S : Subgroup H).map (MulAut.conj g).toMonoidHom = pCore 2 H := by
    simpa only [intervalDiagram, show 3 * v - (3 * v - 1) = 1 by omega,
      intervalCell_intersection] using hQ
  have hgen : ∀ a b : ℕ, a + b < 3 * v →
      intervalCell φ a (b + 1) ⊔ intervalCell φ (a + 1) b = intervalCell φ a b := by
    intro a b hab
    apply le_antisymm (sup_le (intervalCell_antitone φ le_rfl (Nat.le_succ b))
      (intervalCell_antitone φ (Nat.le_succ a) le_rfl))
    have he : intervalCell φ a b = X a (3 * v - b) := by
      simp only [X, intervalDiagram, show 3 * v - (3 * v - b) = b by omega]
    rw [he]
    have hp : X a (3 * v - b) = ⨆ k ∈ Set.Icc a (3 * v - b), X k k :=
      hpoints a (3 * v - b) (by omega) (by omega)
    rw [hp]
    apply iSup_le
    intro k
    apply iSup_le
    intro hk
    obtain ⟨hak, hkb⟩ := hk
    by_cases hka : k = a
    · subst k
      exact (intervalCell_antitone φ le_rfl (show b + 1 ≤ 3 * v - a by omega)).trans le_sup_left
    · exact (intervalCell_antitone φ (show a + 1 ≤ k by omega)
        (show b ≤ 3 * v - k by omega)).trans le_sup_right
  have hnS : (S : Subgroup H) ≤ normalizer
      (((S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H) := by
    rw [hinter, normalizer_eq_top]
    exact le_top
  have hnT : (S : Subgroup H).map (MulAut.conj g).toMonoidHom ≤ normalizer
      (((S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H) := by
    rw [hinter, normalizer_eq_top]
    exact le_top
  obtain ⟨q, hq, hk, _, _, _, _, _⟩ := original_psl2_four_omegaAction_recognition
    hF S hu K e hf hno.noCharacteristicNormal
  have hkernel := original_omega_sylow_centralizer_eq hF S hu K e q hq hk
  have hcenter := (original_psl2_four_omegaCenters_eq_centers hF S α hu K e hf hno).2
  rw [hcenter, hzQ] at hkernel
  have hpoint := intervalDiagram_opposite_point_kernel φ v hv hgen hE
    (hkernel.trans_le hinter.ge)
  exact ⟨g, v, hv, htop, hS, hT, hQ, hzS, hzT, hzQ, hzH, hE, hjoin, hpoints, hshift,
    hcomm, hbound, hpoint, fun j hjlo hjhi => intervalDiagram_right_centralizer_eq φ v
      hnS hnT hgen hE (fun r _ hr => hpoint r hr) hjlo hjhi⟩

end Glauberman
