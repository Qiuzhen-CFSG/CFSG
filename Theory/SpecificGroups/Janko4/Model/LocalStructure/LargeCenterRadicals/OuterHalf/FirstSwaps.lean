module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstSwaps.Case5
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstSwaps.Case7
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstSwaps.Case10
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstRepresentativeForward
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstSymmetryReduction
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Thompson.Centralizers
import Mathlib.Tactic.FinCases

/-!
# Symmetry for commuting involutions in the first native class

Explicit native exchange words close census pairs 5, 7 and 10. Together with
the two-core pair calculation, these give symmetry for every commuting pair
whose two entries are conjugate to the first marked involution. In particular
they give the missing reverse residual memberships for representatives 7 and
10, and transport them through their entire local conjugacy classes.

Source: Kleidman--Wilson (1988), pp.485,487, Lemma 1.1.3 and Corollary 1.1.4.
The mixed-class and second-class comparisons are separate obligations; this
module does not assume or assert them or any normalizer coverage theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Janko4.Cardinality.LocalInvolutionCensus
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound
open Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem source_symmetry_of_exchange (i : Fin 11) (g : Model)
    (hfirst : g * (sourceRepresentative i : Model) * g⁻¹ =
      ((sourceSeed ^ 2 : sourceSubgroup) : Model))
    (hsecond : g * ((sourceSeed ^ 2 : sourceSubgroup) : Model) * g⁻¹ =
      (sourceRepresentative i : Model)) :
    InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceRepresentative i) ↔
      InnerRelated (sourceRepresentative i) ((sourceSeed ^ 2 : sourceSubgroup) : Model) := by
  have h₁ : (MulAut.conj g) (sourceRepresentative i : Model) =
      ((sourceSeed ^ 2 : sourceSubgroup) : Model) := hfirst
  have h₂ : (MulAut.conj g) ((sourceSeed ^ 2 : sourceSubgroup) : Model) =
      (sourceRepresentative i : Model) := hsecond
  have he := innerRelated_equiv (MulAut.conj g) (sourceRepresentative i)
    ((sourceSeed ^ 2 : sourceSubgroup) : Model)
  rw [h₁, h₂] at he
  exact he

private theorem first_symmetry_of_source (i : Fin 11)
    (hp : InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceRepresentative i) ↔
      InnerRelated (sourceRepresentative i) ((sourceSeed ^ 2 : sourceSubgroup) : Model)) :
    InnerRelated Janko4.a (eH (representative i)) ↔
      InnerRelated (eH (representative i)) Janko4.a := by
  have hs : (MulAut.conj h⁻¹) ((sourceSeed ^ 2 : sourceSubgroup) : Model) = Janko4.a := by
    simpa only [MulAut.conj_apply, inv_inv, coe_sourceSeed_sq] using conjugates_t
  have hu : (MulAut.conj h⁻¹) (sourceRepresentative i : Model) = eH (representative i) := by
    rw [representative_eq, eH_sourceSubgroupEquivLocal, MulAut.conj_apply, inv_inv]
  simpa only [hs, hu] using
    (innerRelated_equiv (MulAut.conj h⁻¹)
      ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceRepresentative i)).trans
      (hp.trans (innerRelated_equiv (MulAut.conj h⁻¹) (sourceRepresentative i)
        ((sourceSeed ^ 2 : sourceSubgroup) : Model)).symm)

/-- The literal representative-5 pair has equal intrinsic residual characters. -/
theorem first_pair5_symmetry :
    InnerRelated Janko4.a (eH (representative 5)) ↔
      InnerRelated (eH (representative 5)) Janko4.a :=
  first_symmetry_of_source 5 (source_symmetry_of_exchange 5 FirstSwaps.Case5.conjugator
    FirstSwaps.Case5.conjugator_first FirstSwaps.Case5.conjugator_second)

/-- The literal representative-7 pair has equal intrinsic residual characters. -/
theorem first_pair7_symmetry :
    InnerRelated Janko4.a (eH (representative 7)) ↔
      InnerRelated (eH (representative 7)) Janko4.a :=
  first_symmetry_of_source 7 (source_symmetry_of_exchange 7 FirstSwaps.Case7.conjugator
    FirstSwaps.Case7.conjugator_first FirstSwaps.Case7.conjugator_second)

/-- The literal representative-10 pair has equal intrinsic residual characters. -/
theorem first_pair10_symmetry :
    InnerRelated Janko4.a (eH (representative 10)) ↔
      InnerRelated (eH (representative 10)) Janko4.a :=
  first_symmetry_of_source 10 (source_symmetry_of_exchange 10 FirstSwaps.Case10.conjugator
    FirstSwaps.Case10.conjugator_first FirstSwaps.Case10.conjugator_second)

/-- Reverse membership for the seventh representative, in the full residual. -/
theorem first_pair7_reverse : InnerRelated (eH (representative 7)) Janko4.a :=
  first_pair7_symmetry.mp first_pair7_forward

/-- Reverse membership for the tenth representative, in the full residual. -/
theorem first_pair10_reverse : InnerRelated (eH (representative 10)) Janko4.a :=
  first_pair10_symmetry.mp first_pair10_forward

/-- Symmetry throughout the fifth local conjugacy class. -/
theorem first_pair5_class_symmetry (u : H) (hu : IsConj (representative 5) u) :
    InnerRelated Janko4.a (eH u) ↔ InnerRelated (eH u) Janko4.a :=
  (innerRelated_first_class_iff hu).1.symm.trans
    (first_pair5_symmetry.trans (innerRelated_first_class_iff hu).2)

/-- Both inner-half memberships throughout the seventh local conjugacy class. -/
theorem first_pair7_class_inner (u : H) (hu : IsConj (representative 7) u) :
    InnerRelated Janko4.a (eH u) ∧ InnerRelated (eH u) Janko4.a :=
  ⟨(innerRelated_first_class_iff hu).1.mp first_pair7_forward,
    (innerRelated_first_class_iff hu).2.mp first_pair7_reverse⟩

/-- Both inner-half memberships throughout the tenth local conjugacy class. -/
theorem first_pair10_class_inner (u : H) (hu : IsConj (representative 10) u) :
    InnerRelated Janko4.a (eH u) ∧ InnerRelated (eH u) Janko4.a :=
  ⟨(innerRelated_first_class_iff hu).1.mp first_pair10_forward,
    (innerRelated_first_class_iff hu).2.mp first_pair10_reverse⟩

private theorem representative_one : eH (representative 1) = Janko4.a := by
  have he : sourceRepresentative 1 = sourceSeed ^ 2 := by
    apply Subtype.ext
    apply toMatrix_injective
    change toMatrix (sourceRepresentative 1 : Model) = toMatrix (kernelFactor 0 : Model)
    rw [eval_rep_1, KernelSeparation.eval_factor]
  rw [representative_eq, he, Coordinates.sourceEquiv_seed_sq, eH_zH]

/-- The complete first-class part of the actual first-centralizer census. -/
theorem first_centralizer_first_class_symmetry (u : H)
    (hu : IsConj Janko4.a (eH u)) :
    InnerRelated Janko4.a (eH u) ↔ InnerRelated (eH u) Janko4.a := by
  have hs : u ^ 2 = 1 := by
    apply eH_injective
    rw [map_pow, map_one]
    exact isConj_one_right.mp (by simpa only [Janko4.a_pow_two] using hu.pow 2)
  obtain ⟨i, hi⟩ := square_one_coverage Janko4.Cardinality.Thompson.max2_card.le u hs
  have ht : IsConj z (firstTarget i) :=
    hu.trans ((eH_isConj hi).symm.trans (firstTarget_isConj_representative i).symm)
  have hne : z ≠ 1 := by
    intro he
    have ho : orderOf z = 2 := orderOf_z
    rw [he, orderOf_one] at ho
    omega
  have hcases : i = 1 ∨ i = 2 ∨ i = 5 ∨ i = 7 ∨ i = 10 := by
    fin_cases i <;>
      simp only [firstTarget, Matrix.cons_val_zero', Matrix.cons_val_succ',
        isConj_one_left, hne, not_isConj_z_t] at ht
    all_goals decide
  have hc := innerRelated_first_class_iff hi
  apply hc.1.symm.trans
  apply Iff.trans _ hc.2
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · rw [representative_one]
  · exact ⟨fun _ => first_pair_inner.2, fun _ => first_pair_inner.1⟩
  · exact first_pair5_symmetry
  · exact first_pair7_symmetry
  · exact first_pair10_symmetry

/-- Symmetry for a commuting pair of actual first-class involutions. -/
theorem innerRelated_symm_of_first_class (x y : Model)
    (hx : IsConj Janko4.a x) (hy : IsConj Janko4.a y) (hc : Commute x y) :
    InnerRelated x y ↔ InnerRelated y x := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  let e := MulAut.conj g⁻¹
  have hx' : e x = Janko4.a := by
    rw [← hg]
    simp [e, mul_assoc]
  have hy' : IsConj Janko4.a (e y) :=
    hy.trans (isConj_iff.mpr ⟨g⁻¹, rfl⟩)
  have hc' : Commute Janko4.a (e y) := by
    simpa only [MulEquiv.coe_toMonoidHom, hx'] using hc.map e.toMonoidHom
  let v : centralizer ({z} : Set Model) :=
    ⟨e y, mem_centralizer_singleton_iff.mpr hc'.eq.symm⟩
  obtain ⟨u, hu⟩ := Janko4.Cardinality.Thompson.max2EquivCentralizer.surjective v
  have hu' : eH u = e y := by
    simpa only [Janko4.Cardinality.Thompson.max2EquivCentralizer_coe] using
      congrArg Subtype.val hu
  have hh := first_centralizer_first_class_symmetry u (hu'.symm ▸ hy')
  rw [hu', ← hx'] at hh
  exact (innerRelated_equiv e x y).symm.trans (hh.trans (innerRelated_equiv e y x))

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
