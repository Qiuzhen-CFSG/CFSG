module
public import Glauberman.PushingUpSL2DegreeClass
public import Theory.GroupTheory.SubgroupTransport.NormalGapLayers
public import Theory.GroupTheory.Commutator.PerfectQuotient
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Original-degree Niles normal factors

The same residual Sylow pair and shortest-gap diagram construct the two
normal layers in Niles 5.5. The three factors Q/M, M/N and N/Z(Q) are
elementary. The middle factor has order q² and its action kernel is
exactly Q, by perfectness and simplicity of the original SL₂ quotient.
In the class-two branch, Q/Z(Q) is elementary and ambient central.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 5.5,
pp.51--52. This proves the filtration and faithful-action clauses.
Natural-module coordinates and the parameter equality in 5.7 remain
separate conclusions; no field-four restriction is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite G] [Finite F] in
/-- A nontrivial normal section annihilated by the original two-core
has precisely that core as its action kernel. -/
theorem sl2_normal_section_kernel
    (e : (G ⧸ pCore 2 G) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hlarge : 3 < Nat.card F) (M N : Subgroup G) [M.Normal] [N.Normal]
    (hQ : ⁅pCore 2 G,M⁆ ≤ N) (hnt : ¬ ⁅(⊤ : Subgroup G),M⁆ ≤ N) :
    commutatorPreimage ⊤ M N = pCore 2 G := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).isSimpleGroup
  let C := commutatorPreimage ⊤ M N
  have hQC : pCore 2 G ≤ C := le_commutatorPreimage le_top hQ
  let : C.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp
    (commutatorPreimage_normalized ⊤ M N ⊤ le_normalizer_of_normal
      le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal))
  let : (C.map f).Normal := Normal.map inferInstance f hf
  apply le_antisymm ?_ hQC
  rcases (inferInstance : (C.map f).Normal).eq_bot_or_eq_top with hb | ht
  · rw [←hk]
    exact (Subgroup.map_eq_bot_iff C).mp hb
  · have he := congrArg (Subgroup.comap f) ht
    rw [comap_map_eq,hk,sup_eq_left.mpr hQC,comap_top] at he
    exact (hnt (he ▸ commutator_commutatorPreimage_le ⊤ M N le_normalizer_of_normal)).elim

/-- The actual gap diagram with both normal layers and their literal factors.
The natural-module recognition and the final parameter equality are subsequent
claims, not fields in this conclusion. -/
@[expose] def NilesNormalLayerDiagram (q : ℕ) (S : Subgroup G) (α : MulAut S) : Prop :=
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
      ∃ k : ℕ, 2*v < k ∧ k < 3*v ∧ 5*v ≤ 2*k ∧
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

/-- Niles 5.5's normal filtration at the original degree, including elementary
factors, the order q² of the second factor, and its exact SL₂ action kernel. -/
theorem original_sl2_normal_layers
    (e : (G ⧸ pCore 2 G) ≃* Matrix.SpecialLinearGroup (Fin 2) F) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    NilesNormalLayerDiagram (Nat.card F) (S : Subgroup G) α := by
  obtain ⟨g,hg,hgen,hinter,hnum,v,hv,hj,hshort,hzs,hzt,hzq,hzg,htwice,hpoint,hbranch⟩ :=
    original_sl2_gap_diagram e hn hF S α hfit hno
  let T := S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  let φ := twistedConjugacy (S : Subgroup G) α g
  let X := intervalDiagram φ (3*v)
  have hVn : (X v (2*v)).Normal := by
    change (intervalDiagram (twistedConjugacy (S : Subgroup G) α g) (3*v) v (2*v)).Normal
    rw [←hzq]
    exact normalizer_eq_top_iff.mp (top_le_iff.mp
      (normalizes_centerIn (show (⊤ : Subgroup G) ≤ normalizer (pCore 2 G : Set G) from
        le_normalizer_of_normal)))
  let _ := hVn
  refine ⟨g,hg,hgen,hinter,hnum,v,hv,hj,hshort,hzs,hzt,hzq,hzg,htwice,hpoint,hVn,?_⟩
  rcases hbranch with hc | ⟨k,hk,hkw,hex,hgap,_,_,_,_,_,_,_,_,hclass⟩
  · have hcentral := intervalDiagram_class_two_core φ v hv hgen hzs hzt hVn hc
    rw [hinter] at hcentral
    refine Or.inl ⟨hc,hcentral,?_⟩
    have hQ : X 1 (3*v-1) = pCore 2 G := by
      simp only [X,intervalDiagram,show 3*v-(3*v-1)=1 by omega,intervalCell_intersection]
      exact hinter
    rw [←hQ]
    apply intervalDiagram_elementary_image φ v hv hj hshort (by omega) (by omega)
    rw [QuotientGroup.ker_mk']
    change ⁅X 1 (3*v-1),X 1 (3*v-1)⁆ ≤ X v (2*v)
    rw [hQ]
    exact (commutator_mono le_top le_rfl).trans hcentral
  · apply Or.inr
    have hω := hnum.omegaCenters_eq_centers.2.2
    rw [hinter] at hω
    have hC := sl2_core_omega_centralizer e hn hF S hfit hno.noCharacteristicNormal
    rw [hω,hzq] at hC
    have hsharp := sl2_gap_sharp e S T φ hnum hinter hv hk hkw hj hshort
      hzs hzt hzq htwice hpoint hgap hC hex
    have hd := (hclass hsharp).1
    obtain ⟨hVN,hNM,hMQ,hnN,hnM,hNV,hQM,hMQZ⟩ :=
      intervalDiagram_gap_layers φ v k hk hkw hgen hj hzs hzt hgap hVn hd
    let N := X (3*v-k+1) (k-1)
    let M := X (3*v-k) k
    let _ : N.Normal := hnN
    let _ : M.Normal := hnM
    have hMQV : ⁅(S : Subgroup G) ⊓ (T : Subgroup G),M⁆ ≤ X v (2*v) :=
      hMQZ.trans (hzt ▸ intervalDiagram_mono φ (by omega) le_rfl)
    obtain ⟨hEq,hEn,hEm⟩ := intervalDiagram_gap_elementary_sections φ v k hk hkw hj hshort
      (X v (2*v)) N M rfl rfl hVN hMQ hNV hQM hMQV
    have hindex : ∀ a : ℕ, 1 ≤ a → a ≤ 2*v → rectangleStepIndex φ a = Nat.card F := by
      have hfirst : rectangleStepIndex φ 1 = Nat.card F := by
        let P : IntersectionPair G := ⟨S,T,φ⟩
        exact P.rectangleStepIndex_eq_index 0 hnum
      have hlast := hnum.rectangleStepIndex_double_eq_index v hv
        (by simpa only [intervalDiagram,show 3*v-(2*v-1)=v+1 by omega] using hzs)
        (by simpa only [hinter,intervalDiagram,show 3*v-2*v=v by omega] using hzq)
      change rectangleStepIndex φ (2*v) = Nat.card F at hlast
      intro a ha haw
      apply le_antisymm
      · simpa only [hfirst] using rectangleStepIndex_antitone φ ha
      · simpa only [hlast] using rectangleStepIndex_antitone φ haw
    have hidx := intervalDiagram_gap_layer_index φ v k (Nat.card F) hk hkw hsharp hindex
    have hlarge : 3 < Nat.card F := by
      rw [hF]
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
      norm_num at hh
      omega
    let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
      GorensteinWalter.sl2_isPerfect_of_card_gt_three F hlarge
    have hperfect : ⁅(⊤ : Subgroup G),(⊤ : Subgroup G)⁆ ⊔ ((S : Subgroup G) ⊓ (T : Subgroup G)) = ⊤ := by
      let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
      have hkf : f.ker = pCore 2 G := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
      have he := CentralExtension.ker_sup_commutator_eq_top_of_surjective f
        (e.surjective.comp (QuotientGroup.mk'_surjective _))
      change _root_.commutator G ⊔ ((S : Subgroup G) ⊓
        (S : Subgroup G).map (MulAut.conj g).toMonoidHom) = ⊤
      rw [hinter]
      simpa only [hkf,sup_comm] using he
    have hnt := intervalDiagram_gap_action_nontrivial φ v k hk hkw hperfect hzt hex hVn hNV hMQV
    have hkernel := sl2_normal_section_kernel e hlarge M N
      (hinter ▸ hMQV.trans hVN) hnt
    rw [hinter] at hMQ hQM hMQZ hEq
    exact ⟨k,hk,hkw,hsharp,hex,hgap,hnN,hnM,hVN,hNM,hMQ,hNV,hQM,hMQZ,hd,hidx,hEq,hEn,hEm,hkernel⟩

end Glauberman
