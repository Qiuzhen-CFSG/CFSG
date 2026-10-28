module
public import Glauberman.PushingUpSL2DegreeReduction

/-!
# The full marked two-step Niles diagram

The reduced quotient already has parameter two for its specified twist.
Full center covering reconstructs that same depth-six lattice and all its
indices. Point commutators put the core derived group in the full ambient
center; point generation makes the corresponding quotient elementary.
The literal interval X[3,5] centralizes the right Sylow modulo the ambient
center and has relative order q². An elementary terminal interval supplements
the core. These are the original section inputs for the binary exclusion.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem 6.9, p.58,
with natural endpoints shifted up by one. All central attachments remain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
open scoped MatrixGroups
namespace Glauberman
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

@[expose] def NilesTwoStepFullDiagram (q : ℕ) (S T : Subgroup G) (φ : S ≃* T) : Prop :=
  let X := intervalDiagram φ 6
  NumericalPairAt q S T φ ∧
    (∀ a b : ℕ, a+b < 6 →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b) ∧
    (∀ a b : ℕ, b ≤ 6 → b < a+4 → IsElementaryAbelian 2 (X a b)) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 6 → rectangleStepIndex φ i = q) ∧
    centerIn S = X 2 3 ∧ centerIn T = X 3 4 ∧
    centerIn (pCore 2 G) = X 2 4 ∧ center G = X 3 3 ∧
    (∀ i : ℕ, i ≤ 2 → ⁅X i i,X (i+4) (i+4)⁆ ≤ X (i+2) (i+2))

theorem sl2_two_step_full_diagram
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) (g : G)
    (hgen : (S : Subgroup G) ⊔ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤)
    (hinter : (S : Subgroup G) ⊓ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = pCore 2 G)
    (hd : NilesTwoStepDiagram (Nat.card F) (S : Subgroup G) α g) :
    NilesTwoStepFullDiagram (Nat.card F) (S : Subgroup G)
      ((S : Subgroup G).map (MulAut.conj g).toMonoidHom)
      (twistedConjugacy (S : Subgroup G) α g) := by
  obtain ⟨hnum,hE,hzs,hzt,hzq⟩ := hd
  let T := (S : Subgroup G).map (MulAut.conj g).toMonoidHom
  let φ := twistedConjugacy (S : Subgroup G) α g
  let P : IntersectionPair G := ⟨S,T,φ⟩
  let _ := hE
  have hzq' : centerIn ((S : Subgroup G) ⊓ T) = intervalCell φ 2 2 := by
    rw [hinter]
    exact hzq
  have hi1 : rectangleStepIndex φ 1 = Nat.card F := P.rectangleStepIndex_eq_index 0 hnum
  have hi4 : rectangleStepIndex φ 4 = Nat.card F :=
    hnum.rectangleStepIndex_double_eq_index 2 (by decide) hzs hzq'
  have hj : ∀ a b : ℕ, 1 ≤ a+b → a+b < 4 →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b := by
    intro a b hab hlt
    apply intervalCell_sup_of_stepIndex_lower φ hab (show a+b+1 ≤ 4 by omega)
    rw [hi1,hi4]
  have hnS := normalizes_centerIn (S := (S : Subgroup G) ⊓ T) (A := (S : Subgroup G)) hnum.normal_left
  have hnT := normalizes_centerIn (S := (S : Subgroup G) ⊓ T) (A := T) hnum.normal_right
  rw [hzq'] at hnS hnT
  have hcomm := intervalCell_center_commutator_bound φ 2 (by decide) hnS hnT
  have hzGle : center G ≤ (S : Subgroup G) ⊓ T := by
    rw [hinter]
    have hh : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
      rw [←hfit]
      exact centralizer_generalizedFitting_le G
    exact (center_le_centralizer _).trans hh
  have hzg : center G = intervalCell φ 3 3 := by
    rw [center_eq_inf_centers_of_generating hgen hzGle,hzs,hzt,intervalCell_inf]
    rfl
  obtain ⟨hcover,_,hiS⟩ := original_sl2_full_center_covering e hn hF S α hfit hno
  have hcover' : ⁅centerIn ((S : Subgroup G) ⊓ T),(S : Subgroup G)⁆ ⊔ center G =
      centerIn (S : Subgroup G) := by rw [hinter]; exact hcover
  have hi6 : rectangleStepIndex φ 6 = Nat.card F :=
    P.rectangleStepIndex_triple_eq_index (Nat.card F) 2 (by decide) hnum.normal_left
      hj hzs hzq' hzg hcomm hcover' hiS
  have hjall : ∀ a b : ℕ, a+b < 6 →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b := by
    intro a b hab
    by_cases hz : a+b=0
    · have ha : a=0 := by omega
      have hb : b=0 := by omega
      subst a b
      simpa only [Nat.zero_add,intervalCell_initial_left,intervalCell_initial_right,
        intervalCell_zero_left,forwardChain_zero,forwardChain_one,MulEquiv.symm_symm] using hgen
    · apply intervalCell_sup_of_stepIndex_lower φ (by omega) (show a+b+1 ≤ 6 by omega)
      rw [hi1,hi6]
  refine ⟨hnum,hjall,?_,?_,hzs,hzt,hzq,hzg,?_⟩
  · intro a b hb hlen
    exact intervalDiagram_elementary_of_short φ 2 2 hb hlen
  · intro i hi hil
    apply le_antisymm
    · simpa only [hi1] using rectangleStepIndex_antitone φ hi
    · simpa only [hi6] using rectangleStepIndex_antitone φ hil
  · exact fun i hi => intervalDiagram_commutator_twice φ 2 hcomm hi

/-- The reduced core modulo the whole ambient center, together with its
literal fixed subgroup of order q². No central complement is chosen. -/
theorem two_step_core_sections
    {S T : Subgroup G} (φ : S ≃* T) {q : ℕ}
    (hd : NilesTwoStepFullDiagram q S T φ)
    (hinter : S ⊓ T = pCore 2 G) :
    let X := intervalDiagram φ 6
    ⁅pCore 2 G,pCore 2 G⁆ ≤ center G ∧
      IsElementaryAbelian 2 ((pCore 2 G).map (QuotientGroup.mk' (center G))) ∧
      X 3 5 ≤ pCore 2 G ∧ ⁅T,X 3 5⁆ ≤ center G ∧
      (center G).relIndex (X 3 5) = q^2 ∧
      pCore 2 G ⊔ X 3 6 = T := by
  obtain ⟨hnum,hj,hshort,hindex,hzs,hzt,hzq,hzg,htwice⟩ := hd
  let X := intervalDiagram φ 6
  have hQ : X 1 5 = pCore 2 G := by
    change intervalCell φ 1 1 = _
    rw [intervalCell_intersection,hinter]
  have hT : X 1 6 = T := by
    change intervalCell φ 1 0 = _
    exact intervalCell_initial_right φ
  have hpoint (i j : ℕ) (hi : 1 ≤ i) (hj' : j ≤ 5)
      (hji : 1 ≤ j) (hi' : i ≤ 5) : ⁅X i i,X j j⁆ ≤ center G := by
    rcases le_total i j with hij | hji'
    · by_cases hclose : j < i+4
      · have hh := intervalDiagram_point_centralizes_of_close φ 2 i j hshort
          (by omega) (by omega) (by omega) (by omega)
        exact (commutator_eq_bot_iff_le_centralizer.mpr hh).le.trans bot_le
      · have hi1 : i=1 := by omega
        have hj5 : j=5 := by omega
        subst i j
        exact (htwice 1 (by decide)).trans hzg.symm.le
    · by_cases hclose : i < j+4
      · rw [commutator_comm]
        have hh := intervalDiagram_point_centralizes_of_close φ 2 j i hshort
          (by omega) (by omega) (by omega) (by omega)
        exact (commutator_eq_bot_iff_le_centralizer.mpr hh).le.trans bot_le
      · have hi5 : i=5 := by omega
        have hj1 : j=1 := by omega
        subst i j
        rw [commutator_comm]
        exact (htwice 1 (by decide)).trans hzg.symm.le
  have hderived : ⁅pCore 2 G,pCore 2 G⁆ ≤ center G := by
    rw [←hQ]
    apply intervalDiagram_commutator_le_of_points φ 6 hj (by decide : 1 ≤ 5)
      (by decide) (center G) le_normalizer_of_normal
    intro i j hi hi' hj' hj''
    exact hpoint i j hi hj'' hj' hi'
  have helem : IsElementaryAbelian 2 ((pCore 2 G).map (QuotientGroup.mk' (center G))) := by
    rw [←hQ]
    apply intervalDiagram_elementary_image φ 2 (by decide) hj hshort
      (by decide : 1 ≤ 5) (by decide)
    rw [QuotientGroup.ker_mk']
    change ⁅X 1 5,X 1 5⁆ ≤ center G
    rwa [hQ]
  have hD : X 3 5 ≤ pCore 2 G := (intervalDiagram_mono φ (by decide) le_rfl).trans hQ.le
  have hfixed : ⁅T,X 3 5⁆ ≤ center G := by
    rw [←hT]
    apply intervalDiagram_cross_commutator_le φ 6 hj (by decide : 1 ≤ 6)
      (by decide : 3 ≤ 5) (by decide) (by decide) (center G)
      le_normalizer_of_normal le_normalizer_of_normal
    intro i j hi hi' hj' hj''
    by_cases hi5 : i ≤ 5
    · exact hpoint i j hi hj'' (by omega) hi5
    · have hi6 : i=6 := by omega
      subst i
      rw [commutator_comm]
      have hh := intervalDiagram_point_centralizes_of_close φ 2 j 6 hshort
        (by omega) (by omega) (by omega) (by omega)
      exact (commutator_eq_bot_iff_le_centralizer.mpr hh).le.trans bot_le
  have hi1 : (X 3 3).relIndex (X 3 4) = q := by
    change (intervalCell φ 3 3).relIndex (intervalCell φ 3 2) = q
    rw [intervalCell_relIndex φ 3 2 3 3 le_rfl (by decide) (by decide)]
    exact hindex 5 (by decide) (by decide)
  have hi2 : (X 3 4).relIndex (X 3 5) = q := by
    change (intervalCell φ 3 2).relIndex (intervalCell φ 3 1) = q
    rw [intervalCell_relIndex φ 3 1 3 2 le_rfl (by decide) (by decide)]
    exact hindex 4 (by decide) (by decide)
  have hi := relIndex_mul_relIndex (X 3 3) (X 3 4) (X 3 5)
    (intervalDiagram_mono φ le_rfl (by decide)) (intervalDiagram_mono φ le_rfl (by decide))
  rw [hi1,hi2] at hi
  refine ⟨hderived,helem,hD,hfixed,?_,?_⟩
  · rw [hzg]
    exact hi.symm.trans (pow_two q).symm
  · rw [←hQ]
    exact (intervalDiagram_sup_of_overlap φ 6 hj (by decide) (by decide) (by decide) (by decide)).trans hT

/-- The left Sylow has the corresponding fixed section and elementary
supplement in the same marked interval diagram. -/
theorem two_step_left_fixed_section
    {S T : Subgroup G} (φ : S ≃* T) {q : ℕ}
    (hd : NilesTwoStepFullDiagram q S T φ)
    (hinter : S ⊓ T = pCore 2 G) :
    let X := intervalDiagram φ 6
    X 1 3 ≤ pCore 2 G ∧ ⁅S,X 1 3⁆ ≤ center G ∧
      (center G).relIndex (X 1 3) = q^2 ∧
      pCore 2 G ⊔ X 0 3 = S := by
  obtain ⟨hnum,hj,hshort,hindex,hzs,hzt,hzq,hzg,htwice⟩ := hd
  let X := intervalDiagram φ 6
  have hQ : X 1 5 = pCore 2 G := by
    change intervalCell φ 1 1 = _
    rw [intervalCell_intersection,hinter]
  have hS : X 0 5 = S := by
    change intervalCell φ 0 1 = _
    exact intervalCell_initial_left φ
  have hD : X 1 3 ≤ pCore 2 G := (intervalDiagram_mono φ le_rfl (by decide)).trans hQ.le
  have hfixed : ⁅S,X 1 3⁆ ≤ center G := by
    conv_lhs => lhs; rw [←hS]
    apply intervalDiagram_cross_commutator_le φ 6 hj (by decide : 0 ≤ 5)
      (by decide : 1 ≤ 3) (by decide) (by decide) (center G)
      le_normalizer_of_normal le_normalizer_of_normal
    intro i j hi hi' hj' hj''
    by_cases hclose : i < j+4
    · have hh := intervalDiagram_point_centralizes_of_close φ 2 i j hshort
        (by omega) (by omega) (by omega) (by omega)
      exact (commutator_eq_bot_iff_le_centralizer.mpr hh).le.trans bot_le
    · have hi5 : i=5 := by omega
      have hj1 : j=1 := by omega
      subst i j
      rw [commutator_comm]
      exact (htwice 1 (by decide)).trans hzg.symm.le
  have hi1 : (X 3 3).relIndex (X 2 3) = q := by
    change (intervalCell φ 3 3).relIndex (intervalCell φ 2 3) = q
    rw [intervalCell_relIndex φ 2 3 3 3 (by decide) le_rfl (by decide)]
    exact hindex 5 (by decide) (by decide)
  have hi2 : (X 2 3).relIndex (X 1 3) = q := by
    change (intervalCell φ 2 3).relIndex (intervalCell φ 1 3) = q
    rw [intervalCell_relIndex φ 1 3 2 3 (by decide) le_rfl (by decide)]
    exact hindex 4 (by decide) (by decide)
  have hi := relIndex_mul_relIndex (X 3 3) (X 2 3) (X 1 3)
    (intervalDiagram_mono φ (by decide) le_rfl) (intervalDiagram_mono φ (by decide) le_rfl)
  rw [hi1,hi2] at hi
  refine ⟨hD,hfixed,?_,?_⟩
  · rw [hzg]
    exact hi.symm.trans (pow_two q).symm
  · rw [←hQ,sup_comm]
    exact (intervalDiagram_sup_of_overlap φ 6 hj (by decide) (by decide) (by decide) (by decide)).trans hS

end Glauberman
