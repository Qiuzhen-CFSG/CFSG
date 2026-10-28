module
public import Glauberman.PushingUpSL2DegreeLattice
public import Theory.GroupTheory.SubgroupTransport.IntervalCentralizers

/-!
# Original-degree interval normality and centralizers

Reindex the full depth-3v lattice without changing its residual conjugator.
Short intervals are elementary; overlapping intervals generate their union.
Normality of the original two-core gives endpoint-deletion normality and
commutator bounds. Faithfulness on the full core center detects opposite
point kernels, and successive endpoint deletion determines right-interval
centralizers. Every center retains its full central attachment.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem 4.7(a--c)
and its initial commutator bound, and Lemmas 5.1--5.2, pp.47--49.
Our natural endpoints are the source integer endpoints plus one. The
nonabelian class bound is not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

@[expose] def NilesIntervalDiagram (S : Subgroup G) (α : MulAut S) : Prop :=
    ∃ g : G, g ∈ pResidual 2 G ∧ ∃ v : ℕ, 0 < v ∧
      let φ := twistedConjugacy S α g
      let X := intervalDiagram φ (3 * v)
      X 0 (3 * v) = ⊤ ∧
      X 0 (3 * v - 1) = S ∧
      X 1 (3 * v) = S.map (MulAut.conj g).toMonoidHom ∧
      X 1 (3 * v - 1) = pCore 2 G ∧
      centerIn S = X v (2 * v - 1) ∧
      centerIn (S.map (MulAut.conj g).toMonoidHom) = X (v + 1) (2 * v) ∧
      centerIn (pCore 2 G) = X v (2 * v) ∧
      center G = X (v + 1) (2 * v - 1) ∧
      (∀ i j : ℕ, j ≤ 3 * v → j < i + 2 * v → IsElementaryAbelian 2 (X i j)) ∧
      (∀ i j k l : ℕ, i ≤ k → k ≤ j → j ≤ l → l ≤ 3 * v →
        X i j ⊔ X k l = X i l) ∧
      (∀ i j : ℕ, i ≤ j → j ≤ 3 * v → X i j = ⨆ k ∈ Set.Icc i j, X k k) ∧
      (∀ i j : ℕ, j < 3 * v → image φ (X i j) = X (i + 1) (j + 1)) ∧
      (∀ i : ℕ, i ≤ v → ⁅X i i, X (i + 2 * v) (i + 2 * v)⁆ ≤ X (i + v) (i + v)) ∧
      (∀ i j : ℕ, i < j → j ≤ 3 * v → j < i + 3 * v →
        X i j ≤ normalizer (X i (j - 1) : Set G) ∧
        X i j ≤ normalizer (X (i + 1) j : Set G) ∧
        ⁅X i i, X j j⁆ ≤ X (i + 1) (j - 1)) ∧
      (∀ r : ℕ, r ≤ v → X r r ⊓ centralizer (X (r + 2 * v) (r + 2 * v) : Set G) ≤
        X (r + 1) (r + 1)) ∧
      (∀ j : ℕ, 2 * v + 1 ≤ j → j ≤ 3 * v →
        (S.map (MulAut.conj g).toMonoidHom) ⊓ centralizer (X (v + 1) j : Set G) =
          X (j - 2 * v + 1) (3 * v))

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem original_sl2_interval_centralizers
    (e : (G ⧸ pCore 2 G) ≃* Matrix.SpecialLinearGroup (Fin 2) F) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    NilesIntervalDiagram (S : Subgroup G) α := by
  obtain ⟨⟨g,hg,hgen,hinter,hnum,v,hv,hE,_,_,hj,hzS,hzT,hzQ,hzH,hcomm⟩,_⟩ :=
    original_sl2_full_intersection_lattice e hn hF S α hfit hno
  let φ := twistedConjugacy (S : Subgroup G) α g
  let X := intervalDiagram φ (3*v)
  let _ := hE
  have hjall : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b := by
    intro a b hab
    by_cases hz : a+b = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a b
      simpa only [Nat.zero_add,intervalCell_initial_left,intervalCell_initial_right,
        intervalCell_zero_left,forwardChain_zero,forwardChain_one,MulEquiv.symm_symm] using hgen
    · exact hj a b (by omega) hab
  have hshort : ∀ i j : ℕ, j ≤ 3*v → j < i+2*v → IsElementaryAbelian 2 (X i j) :=
    fun i j hj hlen => intervalDiagram_elementary_of_short φ 2 v hj hlen
  have hzQ' : centerIn (pCore 2 G) = X v (2*v) := by
    simpa only [X,intervalDiagram,show 3*v-2*v=v by omega] using hzQ
  have hω := hnum.omegaCenters_eq_centers.2.2
  rw [hinter] at hω
  have hC := sl2_core_omega_centralizer e hn hF S hfit hno.noCharacteristicNormal
  rw [hω,hzQ'] at hC
  have hkernel : (S : Subgroup G) ⊓ centralizer (X v (2*v) : Set G) ≤
      (S : Subgroup G) ⊓ (S : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [hC,hinter]
    exact inf_le_right
  have hpoint := intervalDiagram_opposite_point_kernel φ v hv hjall hshort hkernel
  have hnS := hnum.normal_left
  have hnT := hnum.normal_right
  refine ⟨g,hg,v,hv,?_,?_,?_,?_,?_,?_,hzQ',?_,hshort,?_,?_,?_,?_,?_,hpoint,?_⟩
  · simp only [intervalDiagram,Nat.sub_self,intervalCell_zero_left,forwardChain_zero]
  · simp only [intervalDiagram,show 3*v-(3*v-1)=1 by omega,intervalCell_initial_left]
  · simp only [intervalDiagram,Nat.sub_self,intervalCell_initial_right]
  · simpa only [intervalDiagram,show 3*v-(3*v-1)=1 by omega,intervalCell_intersection] using hinter
  · simpa only [intervalDiagram,show 3*v-(2*v-1)=v+1 by omega] using hzS
  · simpa only [intervalDiagram,show 3*v-2*v=v by omega] using hzT
  · simpa only [intervalDiagram,show 3*v-(2*v-1)=v+1 by omega] using hzH
  · exact fun i j k l hik hkj hjl hlw => intervalDiagram_sup_of_overlap φ (3*v) hjall hik hkj hjl hlw
  · exact fun i j hij hjw => intervalDiagram_eq_iSup_points φ (3*v) hjall hij hjw
  · exact fun i j hj => image_intervalDiagram φ hj
  · exact fun i hi => intervalDiagram_commutator_twice φ v hcomm hi
  · intro i j hij hjw hproper
    have hn := intervalDiagram_normalizes_trim φ hnS hnT (3*v) hij hjw hproper
    exact ⟨hn.1,hn.2,intervalDiagram_endpoint_commutator_le φ hnS hnT (3*v) hij hjw hproper⟩
  · exact fun j hjlo hjhi => intervalDiagram_right_centralizer_eq φ v hnS hnT hjall hshort
      (fun r _ hr => hpoint r hr) hjlo hjhi
end Glauberman
