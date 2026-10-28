module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.CensusGeometry

/-!
# Native line/plane geometry for the pure-first normalizer branch

The certified max4 eight is an elementary binary eight with an explicit word
action. Its four-subgroups are all conjugate, by an actual max4 word, to the
marked plane. The resulting maximal-two-local exclusion is the concrete
consumer used when a pure rank-one/AAA(1) source group has already been placed
inside this native eight.

This is a source adapter for the KW Section 2.1 line endpoint; arbitrary source
placement and the AAA(2) quotient geometry remain separate obligations.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.PureFirstNormalizers
open SymmetricLinear NormalEight
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
open Max4EightAction
attribute [local irreducible] modelGroup matrixA matrixB

private def lineWord : List Bool → max4Subgroup
  | [] => 1
  | b :: w => (if b then y else x) * lineWord w

private theorem lineWord_conj (w : List Bool) (i : Fin 8) :
    (lineWord w)⁻¹ * element i * lineWord w = element (wordAction w i) := by
  induction w generalizing i with
  | nil => simp [lineWord, wordAction]
  | cons b w ih =>
    cases b <;> simp only [lineWord, wordAction, Bool.false_eq_true, if_false,
      if_true, mul_inv_rev]
    · calc
        _ = (lineWord w)⁻¹ * (x⁻¹ * element i * x) * lineWord w := by group
        _ = _ := by rw [element_conj_x, ih]
    · calc
        _ = (lineWord w)⁻¹ * (y⁻¹ * element i * y) * lineWord w := by group
        _ = _ := by rw [element_conj_y, ih]

private theorem native_plane_le_eight : max4Plane ≤ max4Eight := by
  apply map_mono
  rintro z ⟨i,rfl⟩
  exact ⟨planeIndex i,rfl⟩

private theorem native_plane_closure :
    max4Plane = closure ({(element 1 : Model),(element 2 : Model)} : Set Model) := by
  apply le_antisymm
  · rintro z ⟨u,⟨i,rfl⟩,rfl⟩
    have h1 : (element 1 : Model) ∈
        closure ({(element 1 : Model),(element 2 : Model)} : Set Model) :=
      subset_closure (by simp)
    have h2 : (element 2 : Model) ∈
        closure ({(element 1 : Model),(element 2 : Model)} : Set Model) :=
      subset_closure (by simp)
    fin_cases i
    · change (element 0 : Model) ∈ _
      rw [element_zero,Subgroup.coe_one]
      exact one_mem _
    · exact h1
    · exact h2
    · change (element 5 : Model) ∈ _
      have he : (element 5 : Model) = (element 1 : Model) * (element 2 : Model) :=
        congrArg (fun z : max4Subgroup => (z : Model)) (element_mul 1 2).symm
      rw [he]
      exact mul_mem h1 h2
  · apply (closure_le _).mpr
    rintro z (rfl | rfl)
    · exact mem_map_of_mem _ (show element 1 ∈ localPlane from ⟨1,rfl⟩)
    · exact mem_map_of_mem _ (show element 2 ∈ localPlane from ⟨2,rfl⟩)

private theorem native_eight_card : Nat.card max4Eight = 8 :=
  (card_map_of_injective max4Subgroup.subtype_injective).trans card_eight

private theorem native_eight_elementary : IsElementaryAbelian 2 max4Eight := by
  let := elementary_eight
  exact IsElementaryAbelian.map_subtype

/-- Every plane of the native eight is conjugate to the marked plane inside its full normalizer. -/
theorem max4_eight_plane_transitive (Y : Subgroup Model)
    (hY : Y ≤ max4Eight) (hcard : Nat.card Y = 4) :
    ∃ g : max4Subgroup, Y = max4Plane.map (MulAut.conj (g : Model)).toMonoidHom := by
  let : IsElementaryAbelian 2 max4Eight := native_eight_elementary
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le hY
  have hYne : Y ≠ ⊥ := by intro he; simp [he] at hcard
  obtain ⟨u,hu⟩ := ne_bot_iff_exists_ne_one.mp hYne
  have hu1 : (u : Model) ≠ 1 := fun he => hu (Subtype.ext he)
  have hu2 : orderOf (u : Model) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ u.property) hu1
  have hn : ¬ Y ≤ zpowers (u : Model) := by
    intro hh
    have h := Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hh)
    rw [hcard,Nat.card_zpowers,hu2] at h
    omega
  obtain ⟨v,hv,hvn⟩ := SetLike.not_le_iff_exists.mp hn
  have hv1 : v ≠ 1 := by intro he; exact hvn (he ▸ one_mem _)
  have huv : (u : Model) ≠ v := by intro he; exact hvn (he ▸ mem_zpowers (u : Model))
  obtain ⟨_,⟨i,rfl⟩,hi⟩ := hY u.property
  obtain ⟨_,⟨j,rfl⟩,hj⟩ := hY hv
  have hi0 : i ≠ 0 := by
    intro he
    subst i
    exact hu1 (hi.symm.trans (congrArg (fun z : max4Subgroup => (z : Model)) element_zero))
  have hj0 : j ≠ 0 := by
    intro he
    subst j
    exact hv1 (hj.symm.trans (congrArg (fun z : max4Subgroup => (z : Model)) element_zero))
  have hji : j ≠ i := by intro he; exact huv (hi.symm.trans (he ▸ hj))
  have hext : ∀ i j : Fin 8, i ≠ 0 → j ≠ 0 → j ≠ i → ∃ k, IsBasis i j k := by
    decide +kernel
  obtain ⟨k,hk⟩ := hext i j hi0 hj0 hji
  let w := wordFor i j k
  obtain ⟨h1,h2,_⟩ := wordFor_spec i j k hk
  let g : max4Subgroup := (lineWord w)⁻¹
  have hg1 : (MulAut.conj (g : Model)) (element 1 : Model) = u := by
    simpa [g, MulAut.conj_apply, mul_assoc] using
      (congrArg (fun z : max4Subgroup => (z : Model))
        ((lineWord_conj w 1).trans (congrArg element h1))).trans hi
  have hg2 : (MulAut.conj (g : Model)) (element 2 : Model) = v := by
    simpa [g, MulAut.conj_apply, mul_assoc] using
      (congrArg (fun z : max4Subgroup => (z : Model))
        ((lineWord_conj w 2).trans (congrArg element h2))).trans hj
  refine ⟨g, (eq_of_le_of_card_ge ?_ ?_).symm⟩
  · rw [native_plane_closure,MonoidHom.map_closure,Set.image_pair]
    apply (closure_le _).mpr
    rintro z (rfl | rfl)
    · change (MulAut.conj (g : Model)) (element 1 : Model) ∈ Y
      rw [hg1]
      exact u.property
    · change (MulAut.conj (g : Model)) (element 2 : Model) ∈ Y
      rw [hg2]
      exact hv
  · rw [card_map_of_injective (MulAut.conj (g : Model)).injective,max4Plane_card,hcard]

/-- A pure order-four subgroup inside the certified max4 eight cannot be the
maximal TWO-local endpoint: the word table transports it to the marked plane,
whose normalizer is strictly contained in max4. -/
theorem contained_plane_not_maximal
    (Y : Subgroup Model) [IsElementaryAbelian 2 Y]
    (hY : Y ≤ max4Eight) (hcard : Nat.card Y = 4)
    (hmax : IsMaximalTwoLocal (normalizer (Y : Set Model))) : False := by
  obtain ⟨g, hg⟩ := max4_eight_plane_transitive Y hY hcard
  rw [hg] at hmax
  exact conjugate_plane_not_maximal g hmax

end Janko4.LocalStructure.PureFirstNormalizers
