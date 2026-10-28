module
public import Glauberman.PushingUpSL2DegreePoints
public import Theory.GroupTheory.SubgroupTransport.GapEndpoints
public import Theory.GroupTheory.SubgroupTransport.ReflectedCentralizers

/-!
# Normal gap intervals for the original-degree Niles quotient

On the same original-degree point diagram, the two middle intervals below
the shortest noncentral gap are normal in the right Sylow. Their exact
centralizers bound its derived subgroup. The first-gap commutator escapes
one of the two central boundaries, and its left endpoint is exactly
k-2v+1 in the left-escaping branch. The sharp numerical inequality,
when proved, then forces class at most three; it remains an explicit
premise of that last implication here.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas 5.3--5.4,
pp.50--51. This constructs the source intervals from the original SL₂
quotient and does not assume field four or remove central attachments.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

@[expose] def NilesGapDiagram (q : ℕ) (S : Subgroup G) (α : MulAut S) : Prop :=
  ∃ g : G, g ∈ pResidual 2 G ∧
    let T := S.map (MulAut.conj g).toMonoidHom
    let φ := twistedConjugacy S α g
    S ⊔ T = ⊤ ∧ S ⊓ T = pCore 2 G ∧ NumericalPairAt q S T φ ∧
    ∃ v : ℕ, 0 < v ∧
      let X := intervalDiagram φ (3*v)
      (∀ a b : ℕ, a+b < 3*v →
        intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b) ∧
      (∀ i j : ℕ, j ≤ 3*v → j < i+2*v → IsElementaryAbelian 2 (X i j)) ∧
      centerIn S = X v (2*v-1) ∧ centerIn T = X (v+1) (2*v) ∧
      centerIn (pCore 2 G) = X v (2*v) ∧ center G = X (v+1) (2*v-1) ∧
      (∀ i : ℕ, i ≤ v → ⁅X i i,X (i+2*v) (i+2*v)⁆ ≤ X (i+v) (i+v)) ∧
      (∀ i : ℕ, i ≤ v →
        PointCommutatorCovering (X i i) (X (i+1) (i+1))
          (X (i+2*v) (i+2*v)) (X (i+2*v-1) (i+2*v-1)) (X (i+v) (i+v)) (X (i+v+1) (i+v+1)) ∧
        PointCommutatorCovering (X i i) (X (i+1) (i+1))
          (X (i+2*v) (i+2*v)) (X (i+2*v-1) (i+2*v-1)) (X (i+v) (i+v)) (X (i+v-1) (i+v-1))) ∧
      (⁅T,T⁆ ≤ centerIn T ∨ ∃ k : ℕ, 2*v < k ∧ k < 3*v ∧
        (∃ i : ℕ, 1 ≤ i ∧ i+k ≤ 3*v ∧ ¬ ⁅X i i,X (i+k) (i+k)⁆ ≤ centerIn T) ∧
        (∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k → ⁅X i i,X j j⁆ ≤ centerIn T) ∧
        (⁅T,X (v+1) k⁆ ≤ centerIn T ∧
          T ≤ normalizer (X (v+1) k : Set G) ∧
          T ≤ normalizer ((T ⊓ centralizer (X (v+1) k : Set G) : Subgroup G) : Set G)) ∧
        (⁅T,X (3*v-k+1) (2*v)⁆ ≤ centerIn T ∧
          T ≤ normalizer (X (3*v-k+1) (2*v) : Set G) ∧
          T ≤ normalizer ((T ⊓ centralizer (X (3*v-k+1) (2*v) : Set G) : Subgroup G) : Set G)) ∧
        T ⊓ centralizer (X (v+1) k : Set G) = X (k-2*v+1) (3*v) ∧
        T ⊓ centralizer (X (3*v-k+1) (2*v) : Set G) = X 1 (5*v-k) ∧
        ⁅T,T⁆ ≤ X (k-2*v+1) (5*v-k) ∧
        ⁅⁅X 1 1,X (k+1) (k+1)⁆,X (k-2*v+1) (3*v)⁆ ≤ X (k-v+1) (k-v+1) ∧
        (¬ ⁅X 1 1,X (k+1) (k+1)⁆ ≤ X (v+1) (3*v) ∨
          ¬ ⁅X 1 1,X (k+1) (k+1)⁆ ≤ X 1 (k-v+1)) ∧
        (¬ ⁅X 1 1,X (k+1) (k+1)⁆ ≤ X (v+1) (3*v) →
          ¬ ⁅X 1 1,X (k+1) (k+1)⁆ ≤ X (k-2*v+2) (3*v)) ∧
        (5*v ≤ 2*k → ⁅T,T⁆ ≤ X (3*v-k+1) k ∧ T.lowerCentralSeries 3 = ⊥))

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem original_sl2_gap_diagram
    (e : (G ⧸ pCore 2 G) ≃* Matrix.SpecialLinearGroup (Fin 2) F) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    NilesGapDiagram (Nat.card F) (S : Subgroup G) α := by
  obtain ⟨g,hg,hgen,hinter,hnum,v,hv,hj,hshort,hzs,hzt,hzq,hzg,htwice,hpoint,hbranch⟩ :=
    original_sl2_point_diagram e hn hF S α hfit hno
  refine ⟨g,hg,hgen,hinter,hnum,v,hv,hj,hshort,hzs,hzt,hzq,hzg,htwice,hpoint,?_⟩
  rcases hbranch with hc | ⟨k,hk,hkw,hex,hgap⟩
  · exact Or.inl hc
  · apply Or.inr
    let T := (S : Subgroup G).map (MulAut.conj g).toMonoidHom
    let φ := twistedConjugacy (S : Subgroup G) α g
    let X := intervalDiagram φ (3*v)
    have hω := hnum.omegaCenters_eq_centers.2.2
    rw [hinter] at hω
    have hC := sl2_core_omega_centralizer e hn hF S hfit hno.noCharacteristicNormal
    rw [hω,hzq] at hC
    have hkS : (S : Subgroup G) ⊓ centralizer (X v (2*v) : Set G) ≤
        (S : Subgroup G) ⊓ T := by
      rw [hC,hinter]
      exact inf_le_right
    have hkT : T ⊓ centralizer (X v (2*v) : Set G) ≤ T ⊓ (S : Subgroup G) := by
      rw [hC]
      exact le_inf inf_le_left (inf_le_right.trans (hinter.symm.le.trans inf_le_left))
    have hp := intervalDiagram_opposite_point_kernel φ v hv hj hshort hkS
    have hc₁ := intervalDiagram_right_centralizer_eq φ v hnum.normal_left hnum.normal_right
      hj hshort (fun r _ hr => hp r hr) (j := k) (by omega) (by omega)
    have hc₂ := intervalDiagram_left_centralizer_eq φ v hv hnum.normal_left hnum.normal_right
      hj hshort hkT hk hkw
    have hnorm := intervalDiagram_gap_normalizers φ v k hk hkw hj hzt hgap
    have hd := intervalDiagram_derived_gap_bound φ v k hk hkw hj hshort hzt hgap hc₁ hc₂
    have hnC : T ≤ normalizer (X (k-2*v+1) (3*v) : Set G) := by
      have hh := hnorm.1.2.2
      rw [hc₁] at hh
      exact hh
    have htriple := intervalDiagram_gap_triple_bound φ v k hk hkw hj hshort hzt htwice hnC
    have hne : ¬ T ≤ (S : Subgroup G) := by
      intro hle
      have hi := hnum.index_right
      have he : ((S : Subgroup G) ⊓ T).relIndex T = 1 :=
        relIndex_eq_one.mpr (le_inf hle le_rfl)
      rw [he] at hi
      have := hnum.nontrivial_index
      omega
    have hleft := intervalDiagram_gap_left_endpoint φ v k hk hkw
      hnum.normal_left hnum.normal_right hne hj hshort hzt htwice
      (fun m hm => (hpoint m hm).2) _ htriple
    exact ⟨k,hk,hkw,hex,hgap,hnorm.1,hnorm.2,hc₁,hc₂,hd,htriple,
      intervalDiagram_gap_endpoint_escape φ v k hk hkw hzt hex,hleft,
      fun hsharp => intervalDiagram_class_three_of_gap_bound φ v k hk hkw hsharp hj hgap hd⟩
end Glauberman
