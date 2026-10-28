module
public import Glauberman.PushingUpIntervalDiagram
public import Theory.GroupTheory.SubgroupTransport.IntersectionNormality

/-!
# Endpoint commutators in the original pushing-up interval diagram

The original Sylow pair intersects in the normal two-core. Normality
therefore propagates through the literal partial-isomorphism rectangle.
Every proper interval normalizes its two endpoint deletions, and its
endpoint commutator lies in the interval with both endpoints deleted.
The original-source assembly retains all previously constructed intervals,
center markings, singleton generation and elementary-abelian bounds.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 5.1, printed p.49.
The natural endpoints are the source integer endpoints plus one. The full
ambient interval is excluded explicitly; no nilpotence-class bound is used.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

omit [Finite H] in
/-- Apply the endpoint bound to any literal original conjugate whose
intersection is the two-core; the chosen diagram is unchanged. -/
theorem original_interval_endpoint_bound (S : Sylow 2 H) (α : MulAut S) (g : H)
    (hinter : (S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = pCore 2 H)
    (w i j : ℕ) (hij : i < j) (hjw : j ≤ w) (hproper : j < i + w) :
    let X := intervalDiagram (twistedConjugacy (S : Subgroup H) α g) w
    X i j ≤ normalizer (X i (j - 1) : Set H) ∧
      X i j ≤ normalizer (X (i + 1) j : Set H) ∧
      ⁅X i i, X j j⁆ ≤ X (i + 1) (j - 1) := by
  have hS : (S : Subgroup H) ≤ normalizer
      (((S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H) := by
    rw [hinter, normalizer_eq_top]
    exact le_top
  have hT : (S : Subgroup H).map (MulAut.conj g).toMonoidHom ≤ normalizer
      (((S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H) := by
    rw [hinter, normalizer_eq_top]
    exact le_top
  have hn := intervalDiagram_normalizes_trim (twistedConjugacy (S : Subgroup H) α g)
    hS hT w hij hjw hproper
  exact ⟨hn.1, hn.2, intervalDiagram_endpoint_commutator_le
    (twistedConjugacy (S : Subgroup H) α g) hS hT w hij hjw hproper⟩

/-- The source interval structure and Niles 5.1 hold simultaneously for
the same original conjugate, elementary parameter, and partial map. -/
theorem original_psl2_four_interval_endpoint_bounds
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
        ⁅X i i, X j j⁆ ≤ X (i + 1) (j - 1)) := by
  obtain ⟨g, v, hv, htop, hS, hT, hQ, hzS, hzT, hzQ, hzH, hE, hjoin, hpoints, hshift, hcomm⟩ :=
    original_psl2_four_interval_diagram hF S α hu K e hf hno
  have hinter : (S : Subgroup H) ⊓
      (S : Subgroup H).map (MulAut.conj g).toMonoidHom = pCore 2 H := by
    simpa only [intervalDiagram, show 3 * v - (3 * v - 1) = 1 by omega,
      intervalCell_intersection] using hQ
  exact ⟨g, v, hv, htop, hS, hT, hQ, hzS, hzT, hzQ, hzH, hE, hjoin, hpoints, hshift,
    hcomm, fun i j hij hjw hproper => original_interval_endpoint_bound S α g hinter
      (3 * v) i j hij hjw hproper⟩

end Glauberman
