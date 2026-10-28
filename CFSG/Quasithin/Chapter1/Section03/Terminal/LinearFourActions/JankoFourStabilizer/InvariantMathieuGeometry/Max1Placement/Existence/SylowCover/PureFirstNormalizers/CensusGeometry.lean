module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.Max4Endpoint
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.FourGroupGeometry

/-!
# Census placement of the certified max4 pure plane

The checked max4 eight is pure 2A: its generator action table connects every
nonidentity word to the marked first-class element.  The bridge marking and the
max2 quotient census then identify the literal four-space spanned by rows 1 and
2 with census representative 2.  Thus the native plane is one of the two
native pure four-group rows, with an actual ambient conjugator retained.

The proof uses only existing word, marking, quotient and fusion certificates;
no new exhaustive enumeration is introduced.  It does not classify arbitrary
pure four-groups beyond the existing two-row coverage, and it does not identify
the native order-256 normalizer with an F normalizer.

Source: Kleidman--Wilson (1988), Table 1 and Corollary 1.2.2, pp.487--488.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.PureFirstNormalizers
open SymmetricLinear NormalEight
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
attribute [local irreducible] modelGroup matrixA matrixB

private theorem element_two_first : IsConj a (element 2 : Model) := by
  let h := OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.h
  have ht := OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.conjugates_t
  have hm := Max4EightCentralizer.marking.2.1
  apply IsConj.symm
  apply isConj_iff.mpr
  refine ⟨h⁻¹ * Max4EightCentralizer.bridge, ?_⟩
  calc
    _ = h⁻¹ * ((MulAut.conj Max4EightCentralizer.bridge) (element 2 : Model)) * h := by
      simp [MulAut.conj_apply, mul_assoc]
    _ = a := by rw [hm]; exact ht

private theorem element_conj_x_ambient (i : Fin 8) :
    IsConj (element i : Model) (element (actionX i) : Model) := by
  apply isConj_iff.mpr
  refine ⟨(x : Model)⁻¹, ?_⟩
  simpa only [MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv] using
    congrArg (fun z : max4Subgroup => (z : Model)) (element_conj_x i)

private theorem element_conj_y_ambient (i : Fin 8) :
    IsConj (element i : Model) (element (actionY i) : Model) := by
  apply isConj_iff.mpr
  refine ⟨(y : Model)⁻¹, ?_⟩
  simpa only [MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv] using
    congrArg (fun z : max4Subgroup => (z : Model)) (element_conj_y i)

theorem normal_eight_element_first (i : Fin 8) (hi : i ≠ 0) :
    IsConj a (element i : Model) := by
  have h1 : IsConj a (element 1 : Model) :=
    element_two_first.trans (element_conj_y_ambient 1).symm
  have h3 : IsConj a (element 3 : Model) :=
    element_two_first.trans (element_conj_x_ambient 2)
  have h4 : IsConj a (element 4 : Model) :=
    element_two_first.trans (element_conj_y_ambient 2)
  have h5 : IsConj a (element 5 : Model) := h4.trans (element_conj_x_ambient 4)
  have h6 : IsConj a (element 6 : Model) := h4.trans (element_conj_y_ambient 4)
  have h7 : IsConj a (element 7 : Model) := h5.trans (element_conj_y_ambient 5)
  fin_cases i
  · exact (hi rfl).elim
  · exact h1
  · exact element_two_first
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

theorem max4_eight_pure : ∀ z ∈ max4Eight, z ≠ 1 → IsConj a z := by
  rintro z ⟨u, ⟨i, rfl⟩, rfl⟩ hne
  apply normal_eight_element_first i
  intro hi
  subst i
  exact hne (congrArg (fun z : max4Subgroup => (z : Model)) element_zero)

theorem max4_plane_pure : ∀ z ∈ max4Plane, z ≠ 1 → IsConj a z := by
  rintro z ⟨u, ⟨i, rfl⟩, rfl⟩ hne
  exact max4_eight_pure _ (mem_map_of_mem _
    (show element (planeIndex i) ∈ eight from ⟨planeIndex i, rfl⟩)) hne

open Cardinality.LocalInvolutionCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

private theorem quotient_lift_three_ne_one : q (lift 3) ≠ 1 := by
  rw [← QuotientCensus.element_marked 3]
  intro he
  have hh := congrArg (fun v : Q => v.val.val) he
  rw [QuotientCensus.element_val] at hh
  have hn : QuotientCensus.decode (QuotientCensus.code (QuotientCensus.markedIndex 3)) ≠ 1 := by
    decide +kernel
  exact hn hh

private theorem kernel_pure_pair_conjugacy (u : H) (hu : q u = 1)
    (ha : IsConj a (eH u)) (hap : IsConj a (eH (u * zH))) :
    IsConj (representative 2) u := by
  have hc := aa_coverage Cardinality.Thompson.max2_card.le (show u ∈ aa from ⟨ha,hap⟩)
  rcases hc with hh | hh
  · exact hh
  · have hq := q.map_isConj hh
    rw [hu] at hq
    have he := isConj_one_left.mp hq
    rw [q_representative] at he
    exact (quotient_lift_three_ne_one he).elim

private theorem plane_closure :
    max4Plane = closure ({(NormalEight.element 2 : Model), (NormalEight.element 1 : Model)} : Set Model) := by
  apply le_antisymm
  · rintro z ⟨u,⟨i,rfl⟩,rfl⟩
    have h1 : (NormalEight.element 1 : Model) ∈
        closure ({(NormalEight.element 2 : Model), (NormalEight.element 1 : Model)} : Set Model) :=
      subset_closure (by simp)
    have h2 : (NormalEight.element 2 : Model) ∈
        closure ({(NormalEight.element 2 : Model), (NormalEight.element 1 : Model)} : Set Model) :=
      subset_closure (by simp)
    fin_cases i
    · change (NormalEight.element 0 : Model) ∈ _
      rw [NormalEight.element_zero, Subgroup.coe_one]
      exact (closure ({(NormalEight.element 2 : Model),
        (NormalEight.element 1 : Model)} : Set Model)).one_mem
    · exact h1
    · exact h2
    · have he : (NormalEight.element 5 : Model) =
          (NormalEight.element 1 : Model) * (NormalEight.element 2 : Model) :=
        congrArg (fun z : max4Subgroup => (z : Model)) (NormalEight.element_mul 1 2).symm
      change (NormalEight.element 5 : Model) ∈ _
      rw [he]
      exact mul_mem h1 h2
  · apply (closure_le _).mpr
    rintro v (rfl | rfl)
    · exact mem_map_of_mem _ (show NormalEight.element 2 ∈ localPlane from ⟨2,rfl⟩)
    · exact mem_map_of_mem _ (show NormalEight.element 1 ∈ localPlane from ⟨1,rfl⟩)

private theorem marked_plane_first_pair :
    ∃ g : Model, (MulAut.conj g) a = (NormalEight.element 2 : Model) ∧
      (MulAut.conj g) (eH (representative 2)) = (NormalEight.element 1 : Model) := by
  let u : H := sourceSubgroupEquivLocal Max4EightCentralizer.sourceP
  let c : Model := h⁻¹ * Max4EightCentralizer.bridge
  have hc2 : (MulAut.conj c) (NormalEight.element 2 : Model) = a := by
    change (h⁻¹ * Max4EightCentralizer.bridge) * (NormalEight.element 2 : Model) *
      (h⁻¹ * Max4EightCentralizer.bridge)⁻¹ = a
    calc
      _ = h⁻¹ * ((MulAut.conj Max4EightCentralizer.bridge) (NormalEight.element 2 : Model)) * h := by
        simp [MulAut.conj_apply,mul_assoc]
      _ = a := by rw [Max4EightCentralizer.marking.2.1]; exact conjugates_t
  have hc1 : (MulAut.conj c) (NormalEight.element 1 : Model) = eH u := by
    change (h⁻¹ * Max4EightCentralizer.bridge) * (NormalEight.element 1 : Model) *
      (h⁻¹ * Max4EightCentralizer.bridge)⁻¹ = eH (sourceSubgroupEquivLocal Max4EightCentralizer.sourceP)
    rw [eH_sourceSubgroupEquivLocal]
    calc
      _ = h⁻¹ * ((MulAut.conj Max4EightCentralizer.bridge) (NormalEight.element 1 : Model)) * h := by
        simp [MulAut.conj_apply,mul_assoc]
      _ = _ := by rw [Max4EightCentralizer.marking.1]
  have hc5 : (MulAut.conj c) (NormalEight.element 5 : Model) = eH (u*zH) := by
    have h5 : (NormalEight.element 5 : Model) =
        (NormalEight.element 1 : Model) * (NormalEight.element 2 : Model) :=
      congrArg (fun z : max4Subgroup => (z : Model)) (NormalEight.element_mul 1 2).symm
    rw [h5,map_mul,hc1,hc2,map_mul,eH_zH]
  have huq : q u = 1 := q_localKernelProduct 6607
  have hp : IsConj (representative 2) u := kernel_pure_pair_conjugacy u huq
    ((normal_eight_element_first 1 (by decide)).trans (isConj_iff.mpr ⟨c,hc1⟩))
    ((normal_eight_element_first 5 (by decide)).trans (isConj_iff.mpr ⟨c,hc5⟩))
  obtain ⟨k,hk⟩ := isConj_iff.mp hp
  have hka : (MulAut.conj (eH k)) a = a := by
    change eH k * a * (eH k)⁻¹ = a
    have hc : eH k * a = a * eH k := (eH_commute_z k).eq
    rw [hc,mul_inv_cancel_right]
  have hku : (MulAut.conj (eH k)) (eH (representative 2)) = eH u := by
    simpa only [map_mul,map_inv,MulAut.conj_apply] using congrArg eH hk
  refine ⟨c⁻¹ * eH k, ?_, ?_⟩
  · calc
      _ = (MulAut.conj c⁻¹) ((MulAut.conj (eH k)) a) := by simp [mul_assoc]
      _ = (NormalEight.element 2 : Model) := by rw [hka,← hc2]; simp [mul_assoc]
  · calc
      _ = (MulAut.conj c⁻¹) ((MulAut.conj (eH k)) (eH (representative 2))) := by simp [mul_assoc]
      _ = (NormalEight.element 1 : Model) := by rw [hku,← hc1]; simp [mul_assoc]

/-- Census row 2 is the literal max4 plane class, with the ambient conjugator retained. -/
theorem first_four_two_conjugate_plane :
    ∃ g : Model, (ElementaryNormalizerCover.firstFourGroup 2).map
      (MulAut.conj g).toMonoidHom = max4Plane := by
  obtain ⟨g,hg,hk⟩ := marked_plane_first_pair
  refine ⟨g,?_⟩
  rw [ElementaryNormalizerCover.firstFourGroup,MonoidHom.map_closure,Set.image_pair]
  change closure ({(MulAut.conj g) a, (MulAut.conj g) (eH (representative 2))} : Set Model) = _
  rw [hg,hk,← plane_closure]

end Janko4.LocalStructure.PureFirstNormalizers
