module
public import Theory.GroupTheory.SubgroupTransport.NormalGapLayers

/-!
# Fixed halves of the second Niles factor

The two half intervals between the normal gap layers are fixed by the
respective Sylows modulo the smaller layer. Both have relative index q
in the larger layer. Reflection gives the left-hand assertion from the
right-hand gap bound, keeping the full center in the denominator.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 5.5(b),
pp.51--52. Used for the literal natural-factor recognition in
`Glauberman.PushingUpSL2DegreeNaturalLayers`.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] [Finite G] {S T : Subgroup G}

theorem intervalDiagram_gap_fixed_halves (φ : S ≃* T) (v k q : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v) (hsharp : 5*v ≤ 2*k)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hzS : centerIn S = intervalDiagram φ (3*v) v (2*v-1))
    (hzT : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (hgap : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) j j⁆ ≤ centerIn T)
    (hindex : ∀ a : ℕ, 1 ≤ a → a ≤ 2*v → rectangleStepIndex φ a = q) :
    let X := intervalDiagram φ (3*v)
    let N := X (3*v-k+1) (k-1)
    let M := X (3*v-k) k
    let A := X (3*v-k) (k-1)
    let B := X (3*v-k+1) k
    N ≤ A ∧ A ≤ M ∧ N ≤ B ∧ B ≤ M ∧
      ⁅S,A⁆ ≤ N ∧ ⁅T,B⁆ ≤ N ∧ A.relIndex M = q ∧ B.relIndex M = q := by
  let X := intervalDiagram φ (3*v)
  have hT := intervalDiagram_gap_central φ v k hgen hgap
    (a := 3*v-k+1) (b := k) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hgenR : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ.symm a (b+1) ⊔ intervalCell φ.symm (a+1) b = intervalCell φ.symm a b := by
    intro a b hab
    simpa only [intervalCell_symm,sup_comm] using hgen b a (by omega)
  have hgapR := intervalDiagram_gap_central_symm φ v k (by omega) hzS hzT hgap
  have hS := intervalDiagram_gap_central φ.symm v k hgenR hgapR
    (a := 3*v-k+1) (b := k) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [intervalDiagram_symm φ (3*v) (3*v-k+1) k (by omega),
    show 3*v-(3*v-k+1)=k-1 by omega] at hS
  refine ⟨intervalDiagram_mono φ (by omega) le_rfl,
    intervalDiagram_mono φ le_rfl (by omega),
    intervalDiagram_mono φ le_rfl (by omega),
    intervalDiagram_mono φ (by omega) le_rfl,
    hS.trans (hzS ▸ intervalDiagram_mono φ (by omega) (by omega)),
    hT.trans (hzT ▸ intervalDiagram_mono φ (by omega) (by omega)),?_,?_⟩
  · dsimp only [X,intervalDiagram]
    rw [intervalCell_relIndex φ _ _ _ _ le_rfl (by omega) (by omega)]
    exact hindex _ (by omega) (by omega)
  · dsimp only [X,intervalDiagram]
    rw [intervalCell_relIndex φ _ _ _ _ (by omega) le_rfl (by omega)]
    exact hindex _ (by omega) (by omega)
end Theory.GroupTheory.SubgroupTransport
