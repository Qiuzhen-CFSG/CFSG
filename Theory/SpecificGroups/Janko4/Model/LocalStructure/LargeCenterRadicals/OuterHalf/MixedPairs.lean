module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.MixedPairs.Case4
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.MixedPairs.Case6
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.MixedPairs.Case8
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.MixedPairs.FirstCharacter
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.SecondCharacter
import Mathlib.Tactic.FinCases

/-!
# All mixed-class commuting-involution comparisons

The three remaining first-centralizer representatives are compared using the
actual residual characters. Representatives 4 and 6 are outer in both
directions; representative 8 is inner in both. Together with the previously
checked pairs this proves intrinsic symmetry whenever either involution is
in the first ambient class. The certificate tests the literal second-star
pair, not membership in an arbitrary smaller subgroup.

Source: Kleidman--Wilson (1988), p.487, Lemma 1.1.3 and Corollary 1.1.4.
Pure second-class pairs outside the two-core remain a separate obligation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Janko4.Cardinality.LocalInvolutionCensus
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound Coordinates FusionCertificates
open Janko4.InvolutionCentralizers.Second
open Janko4.Simplicity.Max1Fusion.KernelOrbits
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem source_center_commute (u : sourceSubgroup) :
    Commute (u : Model) ((sourceSeed ^ 2 : sourceSubgroup) : Model) := by
  have he : u * sourceSeed ^ 2 = sourceSeed ^ 2 * u := by
    apply sourceSubgroupEquivLocal.injective
    simpa only [map_mul, sourceEquiv_seed_sq] using
      mem_center_iff.mp zH_mem_center (sourceSubgroupEquivLocal u)
  exact congrArg Subtype.val he

private theorem reverse_to_second (u : sourceSubgroup) (d : Model)
    (hd : d * (u : Model) * d⁻¹ = seed) :
    d * ((sourceSeed ^ 2 : sourceSubgroup) : Model) * d⁻¹ ∈ ambientCentralizer := by
  have he := (source_center_commute u).map (MulAut.conj d).toMonoidHom
  change Commute (d * (u : Model) * d⁻¹)
    (d * ((sourceSeed ^ 2 : sourceSubgroup) : Model) * d⁻¹) at he
  rw [hd] at he
  exact mem_centralizer_singleton_iff.mpr he.eq.symm

private theorem source_reverse_inner (u : sourceSubgroup) (d : Model)
    (hd : d * (u : Model) * d⁻¹ = seed)
    (he : let v := d * ((sourceSeed ^ 2 : sourceSubgroup) : Model) * d⁻¹
      v * ((maskValue Janko4.matrixA_mul_self Janko4.matrixB_pow_four 28).val : Model) * v⁻¹ =
        ((maskValue Janko4.matrixA_mul_self Janko4.matrixB_pow_four 180).val : Model)) :
    InnerRelated (u : Model) ((sourceSeed ^ 2 : sourceSubgroup) : Model) := by
  let v := d * ((sourceSeed ^ 2 : sourceSubgroup) : Model) * d⁻¹
  have hv := reverse_to_second u d hd
  let w : InvolutionCentralizers.Second.Local := ⟨v, ambient_le_max1 hv⟩
  let g : localCentralizer := ⟨w, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp hv))⟩
  have hi := second_inner_of_pair_image180 g he
  apply (innerRelated_equiv (MulAut.conj d) _ _).mp
  change InnerRelated (d * (u : Model) * d⁻¹) v
  rw [hd]
  exact hi

private theorem source_reverse_not_inner (u : sourceSubgroup) (d : Model)
    (hd : d * (u : Model) * d⁻¹ = seed) (n : ℕ) (hn : n = 1059 ∨ n = 29)
    (he : let v := d * ((sourceSeed ^ 2 : sourceSubgroup) : Model) * d⁻¹
      v * ((maskValue Janko4.matrixA_mul_self Janko4.matrixB_pow_four 28).val : Model) * v⁻¹ =
        ((maskValue Janko4.matrixA_mul_self Janko4.matrixB_pow_four n).val : Model)) :
    ¬ InnerRelated (u : Model) ((sourceSeed ^ 2 : sourceSubgroup) : Model) := by
  let v := d * ((sourceSeed ^ 2 : sourceSubgroup) : Model) * d⁻¹
  have hv := reverse_to_second u d hd
  let w : InvolutionCentralizers.Second.Local := ⟨v, ambient_le_max1 hv⟩
  let g : localCentralizer := ⟨w, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp hv))⟩
  intro hi
  apply second_not_inner_of_pair_image g n hn he
  have hi' := (innerRelated_equiv (MulAut.conj d) _ _).mpr hi
  change InnerRelated (d * (u : Model) * d⁻¹) v at hi'
  rwa [hd] at hi'

private theorem source_reverse_iff_first (i : Fin 11) :
    InnerRelated (sourceRepresentative i) ((sourceSeed ^ 2 : sourceSubgroup) : Model) ↔
      InnerRelated (eH (representative i)) Janko4.a := by
  have hs : (MulAut.conj h⁻¹) ((sourceSeed ^ 2 : sourceSubgroup) : Model) = Janko4.a := by
    simpa only [MulAut.conj_apply, inv_inv, coe_sourceSeed_sq] using conjugates_t
  have hu : (MulAut.conj h⁻¹) (sourceRepresentative i : Model) = eH (representative i) := by
    rw [representative_eq, eH_sourceSubgroupEquivLocal, MulAut.conj_apply, inv_inv]
  exact (innerRelated_equiv (MulAut.conj h⁻¹) _ _).symm.trans (by rw [hu, hs])

/-- The reversed fourth pair is outer in the full centralizer. -/
theorem first_pair4_not_reverse : ¬ InnerRelated (eH (representative 4)) Janko4.a := by
  rw [← source_reverse_iff_first]
  exact source_reverse_not_inner _ MixedPairs.Case4.conjugator
    MixedPairs.Case4.conjugator_first 1059 (Or.inl rfl) MixedPairs.Case4.conjugator_pair_action

/-- The reversed sixth pair is outer in the full centralizer. -/
theorem first_pair6_not_reverse : ¬ InnerRelated (eH (representative 6)) Janko4.a := by
  rw [← source_reverse_iff_first]
  exact source_reverse_not_inner _ MixedPairs.Case6.conjugator
    MixedPairs.Case6.conjugator_first 29 (Or.inr rfl) MixedPairs.Case6.conjugator_pair_action

/-- The reversed eighth pair is inner in the full centralizer. -/
theorem first_pair8_reverse : InnerRelated (eH (representative 8)) Janko4.a := by
  rw [← source_reverse_iff_first]
  exact source_reverse_inner _ MixedPairs.Case8.conjugator
    MixedPairs.Case8.conjugator_first MixedPairs.Case8.conjugator_pair_action

/-- Complete symmetry in the full first centralizer, including every mixed pair. -/
theorem first_centralizer_symmetry (u : H) (hu : orderOf (eH u) = 2) :
    InnerRelated Janko4.a (eH u) ↔ InnerRelated (eH u) Janko4.a := by
  have hs : u ^ 2 = 1 := by
    apply eH_injective
    rw [map_pow, map_one]
    simpa only [hu] using pow_orderOf_eq_one (eH u)
  obtain ⟨i, hi⟩ := square_one_coverage Janko4.Cardinality.Thompson.max2_card.le u hs
  have hc := innerRelated_first_class_iff hi
  apply hc.1.symm.trans
  apply Iff.trans _ hc.2
  fin_cases i
  · have hz : IsConj 1 (eH u) := (firstTarget_isConj_representative 0).trans (eH_isConj hi)
    rw [isConj_one_right.mp hz, orderOf_one] at hu
    omega
  · exact first_centralizer_first_class_symmetry _ (firstTarget_isConj_representative 1)
  · exact first_centralizer_first_class_symmetry _ (firstTarget_isConj_representative 2)
  · have hp := first_pair3_class_inner _ (IsConj.refl _)
    exact ⟨fun _ => hp.2, fun _ => hp.1⟩
  · exact iff_of_false first_pair4_not_forward first_pair4_not_reverse
  · exact first_pair5_symmetry
  · exact iff_of_false first_pair6_not_forward first_pair6_not_reverse
  · exact first_pair7_symmetry
  · exact ⟨fun _ => first_pair8_reverse, fun _ => first_pair8_forward⟩
  · have hp := first_pair9_class_inner _ (IsConj.refl _)
    exact ⟨fun _ => hp.2, fun _ => hp.1⟩
  · exact first_pair10_symmetry

/-- Intrinsic symmetry whenever the first involution is in the first ambient class. -/
theorem innerRelated_symm_of_first (x y : Model)
    (hx : IsConj Janko4.a x) (hy : orderOf y = 2) (hc : Commute x y) :
    InnerRelated x y ↔ InnerRelated y x := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  let e := MulAut.conj g⁻¹
  have hx' : e x = Janko4.a := by
    rw [← hg]
    simp [e, mul_assoc]
  have hy' : orderOf (e y) = 2 := (e.orderOf_eq y).trans hy
  have hc' : Commute Janko4.a (e y) := by
    simpa only [MulEquiv.coe_toMonoidHom, hx'] using hc.map e.toMonoidHom
  let v : centralizer ({z} : Set Model) :=
    ⟨e y, mem_centralizer_singleton_iff.mpr hc'.eq.symm⟩
  obtain ⟨u, hu⟩ := Janko4.Cardinality.Thompson.max2EquivCentralizer.surjective v
  have hu' : eH u = e y := by
    simpa only [Janko4.Cardinality.Thompson.max2EquivCentralizer_coe] using
      congrArg Subtype.val hu
  have hh := first_centralizer_symmetry u (hu'.symm ▸ hy')
  rw [hu', ← hx'] at hh
  exact (innerRelated_equiv e x y).symm.trans (hh.trans (innerRelated_equiv e y x))

/-- If the third involution in the four-group is first-class, row linearity
and the mixed comparisons also settle the pair of the other two involutions. -/
theorem innerRelated_symm_of_product_first (x y : Model)
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hc : Commute x y)
    (hp : IsConj Janko4.a (x * y)) : InnerRelated x y ↔ InnerRelated y x := by
  let a := x * y
  have ha : orderOf a = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hp
    change orderOf (x * y) = 2
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq Janko4.a).trans Janko4.orderOf_a
  have hax : Commute a x := (Commute.refl x).mul_left hc.symm
  have hay : Commute a y := hc.mul_left (Commute.refl y)
  let u : centralizer ({a} : Set Model) := ⟨x, mem_centralizer_singleton_iff.mpr hax.eq.symm⟩
  let v : centralizer ({a} : Set Model) := ⟨y, mem_centralizer_singleton_iff.mpr hay.eq.symm⟩
  have hm (w : centralizer ({a} : Set Model)) :
      InnerRelated a w ↔ w ∈ solvableResidual (centralizer ({a} : Set Model)) :=
    mem_map_iff_mem (centralizer ({a} : Set Model)).subtype_injective
  have hprod : u * v ∈ solvableResidual (centralizer ({a} : Set Model)) :=
    (hm (u * v)).mp (innerRelated_self a ha)
  have hrow : InnerRelated a x ↔ InnerRelated a y :=
    (hm u).trans (((solvableResidual (centralizer ({a} : Set Model))).mul_mem_iff_of_index_two
      (involution_residual_index a ha) (a := u) (b := v)).mp hprod |>.trans (hm v).symm)
  have hxrow : InnerRelated x a ↔ InnerRelated x y :=
    ((solvableResidual (centralizer ({x} : Set Model))).map
      (centralizer ({x} : Set Model)).subtype).mul_mem_cancel_left (innerRelated_self x hx)
  have hyrow : InnerRelated y a ↔ InnerRelated y x := by
    change InnerRelated y (x * y) ↔ InnerRelated y x
    rw [hc.eq]
    exact ((solvableResidual (centralizer ({y} : Set Model))).map
      (centralizer ({y} : Set Model)).subtype).mul_mem_cancel_left (innerRelated_self y hy)
  exact hxrow.symm.trans ((innerRelated_symm_of_first a x hp hx hax).symm.trans
    (hrow.trans ((innerRelated_symm_of_first a y hp hy hay).trans hyrow)))

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
