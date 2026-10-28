module
public import Glauberman.PushingUpSL2DegreeLayers
public import Theory.GroupTheory.SubgroupTransport.GapParameters

/-!
# Exact parameters of the original-degree Niles normal layers

The same normal-layer witness satisfies 5v = 2k in the noncentral-derived
branch. Its exact two-core action kernel excludes a strict gap inequality:
the earlier precise centralizers would then place the whole Sylow derived
subgroup in the smaller layer. In particular v is even. The elementary
factors, order q² and full central attachments remain in the same witness.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 5.7, p.52.
This does not yet identify the natural factors or assert the later
commutator conclusion of Theorem B.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

@[expose] def NilesExactLayerDiagram (q : ℕ) (S : Subgroup G) (α : MulAut S) : Prop :=
  ∃ g : G, g ∈ pResidual 2 G ∧
    let T := S.map (MulAut.conj g).toMonoidHom
    let φ := twistedConjugacy S α g
    S ⊔ T = ⊤ ∧ S ⊓ T = pCore 2 G ∧ NumericalPairAt q S T φ ∧
    ∃ v : ℕ, 0 < v ∧
      let X := intervalDiagram φ (3*v)
      (∀ a b : ℕ, a+b < 3*v →
        intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b) ∧
      (∀ a b : ℕ, b ≤ 3*v → b < a+2*v → IsElementaryAbelian 2 (X a b)) ∧
      centerIn S = X v (2*v-1) ∧ centerIn T = X (v+1) (2*v) ∧
      centerIn (pCore 2 G) = X v (2*v) ∧ center G = X (v+1) (2*v-1) ∧
      (∀ i : ℕ, i ≤ v → ⁅X i i,X (i+2*v) (i+2*v)⁆ ≤ X (i+v) (i+v)) ∧
      (∀ i : ℕ, i ≤ v →
        PointCommutatorCovering (X i i) (X (i+1) (i+1))
          (X (i+2*v) (i+2*v)) (X (i+2*v-1) (i+2*v-1)) (X (i+v) (i+v)) (X (i+v+1) (i+v+1)) ∧
        PointCommutatorCovering (X i i) (X (i+1) (i+1))
          (X (i+2*v) (i+2*v)) (X (i+2*v-1) (i+2*v-1)) (X (i+v) (i+v)) (X (i+v-1) (i+v-1))) ∧
      ∃ hV : (X v (2*v)).Normal,
      letI := hV
      (⁅T,T⁆ ≤ centerIn T ∧
        ⁅(⊤ : Subgroup G),pCore 2 G⁆ ≤ X v (2*v) ∧
        IsElementaryAbelian 2 ((pCore 2 G).map (QuotientGroup.mk' (X v (2*v))))) ∨
      ∃ k : ℕ, 2*v < k ∧ k < 3*v ∧ 5*v = 2*k ∧ Even v ∧
        (∃ i : ℕ, 1 ≤ i ∧ i+k ≤ 3*v ∧ ¬ ⁅X i i,X (i+k) (i+k)⁆ ≤ centerIn T) ∧
        (∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k → ⁅X i i,X j j⁆ ≤ centerIn T) ∧
        let N := X (3*v-k+1) (k-1)
        let M := X (3*v-k) k
        ∃ hN : N.Normal, ∃ hM : M.Normal,
        letI := hN
        letI := hM
        X v (2*v) ≤ N ∧ N ≤ M ∧ M ≤ pCore 2 G ∧
          ⁅(⊤ : Subgroup G),N⁆ ≤ X v (2*v) ∧
          ⁅(⊤ : Subgroup G),pCore 2 G⁆ ≤ M ∧
          ⁅pCore 2 G,M⁆ ≤ centerIn T ∧
          ⁅T,T⁆ ≤ X (3*v-k+1) k ∧
          N.relIndex M = q^2 ∧
          IsElementaryAbelian 2 ((pCore 2 G).map (QuotientGroup.mk' M)) ∧
          IsElementaryAbelian 2 (N.map (QuotientGroup.mk' (X v (2*v)))) ∧
          IsElementaryAbelian 2 (M.map (QuotientGroup.mk' N)) ∧
          commutatorPreimage ⊤ M N = pCore 2 G

/-- The exact gap identity, with the full original normal filtration. -/
theorem original_sl2_exact_layers
    (e : (G ⧸ pCore 2 G) ≃* Matrix.SpecialLinearGroup (Fin 2) F) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    NilesExactLayerDiagram (Nat.card F) (S : Subgroup G) α := by
  obtain ⟨g,hg,hgen,hinter,hnum,v,hv,hj,hshort,hzs,hzt,hzq,hzg,htwice,hpoint,hVn,hbranch⟩ :=
    original_sl2_normal_layers e hn hF S α hfit hno
  let T := (S : Subgroup G).map (MulAut.conj g).toMonoidHom
  let φ := twistedConjugacy (S : Subgroup G) α g
  let X := intervalDiagram φ (3*v)
  let _ := hVn
  refine ⟨g,hg,hgen,hinter,hnum,v,hv,hj,hshort,hzs,hzt,hzq,hzg,htwice,hpoint,hVn,?_⟩
  rcases hbranch with hc | ⟨k,hk,hkw,hsharp,hex,hgap,hN,hM,hVN,hNM,hMQ,hNV,hQM,hMQZ,hd,hidx,hEq,hEn,hEm,hkernel⟩
  · exact Or.inl hc
  · apply Or.inr
    let _ := hN
    let _ := hM
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
    have hd' := intervalDiagram_derived_gap_bound φ v k hk hkw hj hshort hzt hgap hc₁ hc₂
    have hne : ¬ T ≤ (S : Subgroup G) := by
      intro hle
      have hi := hnum.index_right
      have he : ((S : Subgroup G) ⊓ T).relIndex T = 1 :=
        relIndex_eq_one.mpr (le_inf hle le_rfl)
      rw [he] at hi
      have := hnum.nontrivial_index
      omega
    obtain ⟨hparam,heven⟩ := intervalDiagram_gap_parameter_eq φ v k hk hkw hsharp hne
      (hkernel.trans hinter.symm) hd'
    exact ⟨k,hk,hkw,hparam,heven,hex,hgap,hN,hM,hVN,hNM,hMQ,hNV,hQM,hMQZ,hd,hidx,hEq,hEn,hEm,hkernel⟩

end Glauberman
