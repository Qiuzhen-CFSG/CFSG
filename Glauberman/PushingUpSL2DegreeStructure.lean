module
public import Glauberman.PushingUpSL2Degree
public import Glauberman.PushingUpQuadraticOffender
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The original-degree diagram and its abelian-core branch

Numerical pair descent makes the full core center elementary. If the
core is abelian it equals its omega; the selected quadratic offender
supplements it by sharp replacement. Hence its Sylow commutator is
central and the Sylow has class at most two. This retains the original
core and all central factors, using no natural-module recognition.

The resulting diagram is constructed explicitly from the original SL2
quotient. Its actual application retains the same F0 and Baumann Sylow in
NonbinarySymplectic.CriticalReduction.RootProductNilesDiagram.

Source: Niles, *Pushing-up in finite groups* (1979), Sections 4--6,
pp.44--57, the elementary-core branch used in MS93 (5.1).
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G] {q : ℕ}

theorem class_le_two_of_abelian_core_numerical_pair
    (S : Sylow 2 G) (T : Subgroup G) (φ : (S : Subgroup G) ≃* T)
    (h : NumericalPairAt q (S : Subgroup G) T φ)
    (hinter : (S : Subgroup G) ⊓ T = pCore 2 G)
    (hno : NoCharacteristicNormal (S : Subgroup G))
    (hQ : IsMulCommutative (pCore 2 G)) : Group.nilpotencyClass S ≤ 2 := by
  let _ := hQ
  let _ := S.isPGroup'.isNilpotent
  have hV := h.omegaCenters_eq_centers.2.2
  rw [hinter,centerIn,inf_eq_left.mpr (le_centralizer_iff_isMulCommutative.mpr hQ)] at hV
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro he
    have hi := h.index_left
    rw [he,relIndex_bot_right] at hi
    have := h.nontrivial_index
    omega
  obtain ⟨A,hA,hout,hquad,_⟩ := pushingUp_quadratic_offender S hSne hno
  have hQS : pCore 2 G ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  have hlower : (pCore 2 G).relIndex (S : Subgroup G) ≤
      (omegaCenterIn (pCore 2 G) ⊓ centralizer (A : Set G)).relIndex
        (omegaCenterIn (pCore 2 G)) := by
    rw [←hinter,h.index_left]
    exact h.lower_left A hA.1 (hinter.symm ▸ hout)
  have hgen := (maximum_abelian_replacement_of_fixedIndex hA hQS
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) inferInstance
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
    le_normalizer_of_normal hlower).1
  rw [hV] at hquad
  have hWQ : ⁅pCore 2 G,A⁆ ≤ pCore 2 G := commutator_le_left _ _
  have hQc : pCore 2 G ≤ centralizer (pCore 2 G : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr hQ
  have hWc : ⁅pCore 2 G,A⁆ ≤ centralizer ((S : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mpr
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hquad))
      (le_centralizer_iff.mp (hWQ.trans hQc))
  have hcomm : ⁅pCore 2 G,(S : Subgroup G)⁆ ≤ centerIn (S : Subgroup G) := by
    have he := commutator_eq_of_centralizing_sup ((sup_comm _ _).trans hgen)
      hQc (show A ≤ normalizer (pCore 2 G : Set G) from le_normalizer_of_normal)
    rw [←he]
    exact le_inf (hWQ.trans hQS) hWc
  have hnorm : (S : Subgroup G) ≤ normalizer (centerIn (S : Subgroup G) : Set G) :=
    (le_centralizer_iff.mpr inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hAA : ⁅A,A⁆ = ⊥ := commutator_self_eq_bot_iff.mpr hA.2.1
  have hAS : ⁅A,(S : Subgroup G)⁆ ≤ centerIn (S : Subgroup G) := by
    rw [commutator_comm]
    have hh := commutator_sup_le_of_relative_normal (S : Subgroup G) A (pCore 2 G)
      A (centerIn (S : Subgroup G)) hnorm hA.1 hQS (hAA.le.trans bot_le)
      ((commutator_mono le_rfl hA.1).trans hcomm)
    rwa [hgen] at hh
  have hSS : ⁅(S : Subgroup G),(S : Subgroup G)⁆ ≤ centerIn (S : Subgroup G) := by
    have hh := commutator_sup_le_of_relative_normal (S : Subgroup G) A (pCore 2 G)
      (S : Subgroup G) (centerIn (S : Subgroup G)) hnorm hA.1 hQS hAS hcomm
    rwa [hgen] at hh
  have hd : _root_.commutator S ≤ center S := by
    intro x hx
    have hh : (x : G) ∈ centerIn (S : Subgroup G) := by
      apply hSS
      rw [←map_subtype_commutator]
      exact mem_map_of_mem (S : Subgroup G).subtype hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (hh.2 y y.property))
  apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
  rw [Subgroup.lowerCentralSeries_succ,Subgroup.top_lowerCentralSeries_one]
  exact commutator_top_right_eq_bot_iff_le_center.mpr hd

/-- The literal residual Sylow pair, elementary maximum row, and center
cells used in the Niles structure argument. This is a conclusion package;
the following theorem constructs it from the Main Hypothesis inputs. -/
@[expose] def NilesIntersectionDiagram (q : ℕ) (S : Subgroup G) (α : MulAut S) : Prop :=
  ∃ x : G, x ∈ pResidual 2 G ∧
  let T := S.map (MulAut.conj x).toMonoidHom
  let φ := twistedConjugacy S α x
  S ⊔ T = ⊤ ∧ S ⊓ T = pCore 2 G ∧
  Glauberman.NumericalPairAt (q) S T φ ∧
  omegaOneAmbient S = S ∧ omegaOneAmbient T = T ∧
  omegaCenterIn S = centerIn S ∧ omegaCenterIn T = centerIn T ∧
  omegaCenterIn (pCore 2 G) = centerIn (pCore 2 G) ∧
  ∃ v : ℕ, 0 < v ∧
    IsElementaryAbelian 2 (intervalCell φ 1 v) ∧
    intervalCell φ 1 v ∈ thompsonAbelianSubgroups S ∧
    intervalCell φ 1 v ∈ thompsonAbelianSubgroups T ∧
    (∀ i j : ℕ, 1 ≤ i+j → i+j < 2*v →
      intervalCell φ i (j+1) ⊔
        intervalCell φ (i+1) j =
          intervalCell φ i j) ∧
    centerIn S = intervalCell φ v (v+1) ∧
    centerIn T = intervalCell φ (v+1) v ∧
    centerIn (pCore 2 G) = intervalCell φ v v

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
/-- The unchanged-degree Main Hypothesis constructs its actual diagram;
its abelian-core branch already has Sylow class at most two. -/
theorem original_sl2_niles_diagram
    (e : (G ⧸ pCore 2 G) ≃* Matrix.SpecialLinearGroup (Fin 2) F) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    NilesIntersectionDiagram (Nat.card F) (S : Subgroup G) α ∧
      (IsMulCommutative (pCore 2 G) → Group.nilpotencyClass S ≤ 2) := by
  obtain ⟨x,hx,hpair,hinter,hnum⟩ := original_sl2_numerical_pair e hn hF S α hfit hno
  have hclass := class_le_two_of_abelian_core_numerical_pair S _ _ hnum hinter
    hno.noCharacteristicNormal
  obtain ⟨hωS,hωT⟩ := hnum.omega_generated
  obtain ⟨hzS,hzT,hzQ⟩ := hnum.omegaCenters_eq_centers
  let pair : IntersectionPair G :=
    ⟨S,(S : Subgroup G).map (MulAut.conj x).toMonoidHom,
      twistedConjugacy (S : Subgroup G) α x⟩
  obtain ⟨v,hv,hElem,hmaxS,hmaxT,hlattice,hcenterS,hcenterT,hcenterQ⟩ :=
    pair.exists_double_lattice_center_cells_at hnum
  rw [hinter] at hzQ
  change centerIn ((S : Subgroup G) ⊓
    (S : Subgroup G).map (MulAut.conj x).toMonoidHom) = _ at hcenterQ
  rw [hinter] at hcenterQ
  exact ⟨⟨x,hx,hpair,hinter,hnum,hωS,hωT,hzS,hzT,hzQ,
    v,hv,hElem,hmaxS,hmaxT,hlattice,hcenterS,hcenterT,hcenterQ⟩,hclass⟩
end Glauberman
