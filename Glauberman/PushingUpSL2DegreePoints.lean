module
public import Glauberman.PushingUpSL2DegreePointCovering
public import Glauberman.PushingUpSL2DegreeLattice
public import Theory.GroupTheory.SubgroupTransport.PointCovering
public import Theory.GroupTheory.SubgroupTransport.NoncentralGap
/-!
# The full original-degree Niles point diagram

The original residual Sylow pair has both elementwise covering statements
of Niles 4.7(d), including noncommutation of escaping opposite points.
The full lattice, short elementary intervals and all center markings are
retained for the same conjugator and depth. Applying the original center
covering to both Sylows and reflecting the partial isomorphism supplies
both neighboring quotients of every middle point. If the Sylow derived
subgroup is noncentral, the same diagram selects the shortest escaping
gap k, proves 2v < k < 3v and centrality of all shorter gaps.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem 4.7 and
the initial selection in Lemma 5.3, pp.47--50.
The original F₀ application is `RootProductNilesPoints`; no Sylow class
bound or distance conclusion is assumed or asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

@[expose] def NilesPointDiagram (q : ℕ) (S : Subgroup G) (α : MulAut S) : Prop :=
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
        (∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k → ⁅X i i,X j j⁆ ≤ centerIn T))

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem original_sl2_point_diagram
    (e : (G ⧸ pCore 2 G) ≃* Matrix.SpecialLinearGroup (Fin 2) F) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    NilesPointDiagram (Nat.card F) (S : Subgroup G) α := by
  obtain ⟨⟨g,hg,hgen,hinter,hnum,v,hv,hE,_,_,hj,hzS,hzT,hzQ,hzH,hcomm⟩,_⟩ :=
    original_sl2_full_intersection_lattice e hn hF S α hfit hno
  let T := S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hT : (T : Subgroup G) = (S : Subgroup G).map (MulAut.conj g).toMonoidHom := rfl
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
  have hzs : centerIn (S : Subgroup G) = X v (2*v-1) := by
    simpa only [X,intervalDiagram,show 3*v-(2*v-1)=v+1 by omega] using hzS
  have hzt : centerIn (T : Subgroup G) = X (v+1) (2*v) := by
    rw [hT]
    simpa only [X,intervalDiagram,show 3*v-2*v=v by omega] using hzT
  have hzq : centerIn (pCore 2 G) = X v (2*v) := by
    simpa only [X,intervalDiagram,show 3*v-2*v=v by omega] using hzQ
  have hzg : center G = X (v+1) (2*v-1) := by
    simpa only [X,intervalDiagram,show 3*v-(2*v-1)=v+1 by omega] using hzH
  have hcomms := fun i hi => intervalDiagram_commutator_twice φ v hcomm (i := i) hi
  obtain ⟨hact,hvec,hnc⟩ := original_sl2_center_point_covering e hn hF S α hfit hno S
  rw [←hinter] at hact hvec hnc
  have hbase := intervalDiagram_initial_point_covering φ v hv hjall hnum.normal_left
    hzs (by rw [hinter]; exact hzq) hzg (by simpa only [Nat.zero_add] using hcomms 0 (by omega))
    hact hvec hnc
  have hjrev : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ.symm a (b+1) ⊔ intervalCell φ.symm (a+1) b = intervalCell φ.symm a b := by
    intro a b hab
    simpa only [intervalCell_symm,sup_comm] using hjall b a (by omega)
  have hzrT : centerIn (T : Subgroup G) = intervalDiagram φ.symm (3*v) v (2*v-1) := by
    rw [hT]
    simpa only [intervalDiagram,intervalCell_symm,show 3*v-(2*v-1)=v+1 by omega] using hzT
  have hzrQ : centerIn ((T : Subgroup G) ⊓ (S : Subgroup G)) =
      intervalDiagram φ.symm (3*v) v (2*v) := by
    rw [hT,inf_comm,hinter]
    simpa only [intervalDiagram,intervalCell_symm,show 3*v-2*v=v by omega] using hzQ
  have hzrG : center G = intervalDiagram φ.symm (3*v) (v+1) (2*v-1) := by
    simpa only [intervalDiagram,intervalCell_symm,show 3*v-(2*v-1)=v+1 by omega] using hzH
  have hcr : ⁅intervalDiagram φ.symm (3*v) 0 0,intervalDiagram φ.symm (3*v) (2*v) (2*v)⁆ ≤
      intervalDiagram φ.symm (3*v) v v := by
    simpa only [intervalDiagram,intervalCell_symm,Nat.sub_zero,
      show 3*v-2*v=v by omega,show 3*v-v=2*v by omega,
      show v+2*v=3*v by omega,show v+v=2*v by omega,Nat.sub_self,commutator_comm] using hcomms v le_rfl
  obtain ⟨hactT,hvecT,hncT⟩ := original_sl2_center_point_covering e hn hF S α hfit hno T
  have hTS : (T : Subgroup G) ⊓ (S : Subgroup G) = pCore 2 G := (inf_comm _ _).trans hinter
  rw [←hTS] at hactT hvecT hncT
  have hbaseT := intervalDiagram_initial_point_covering φ.symm v hv hjrev
    (by simpa only [inf_comm] using hnum.normal_right) hzrT hzrQ hzrG hcr hactT hvecT hncT
  refine ⟨g,hg,hgen,hinter,hnum,v,hv,hjall,hshort,hzs,hzt,hzq,hzg,hcomms,?_,?_⟩
  · intro i hi
    exact ⟨intervalDiagram_point_covering_shift φ v hv hbase i hi,
      intervalDiagram_point_covering_reverse φ v hv hbaseT i hi⟩
  · classical
    by_cases hc : ⁅(T : Subgroup G),(T : Subgroup G)⁆ ≤ centerIn (T : Subgroup G)
    · exact Or.inl hc
    · exact Or.inr (intervalDiagram_minimal_noncentral_gap φ v hv hjall hshort hzt hcomms hc)
end Glauberman
