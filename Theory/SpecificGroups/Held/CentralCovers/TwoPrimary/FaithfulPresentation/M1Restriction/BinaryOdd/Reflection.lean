module
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryContracts
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts.Odd.Symmetry
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.PerfectTriangle
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd.ReflectionModel
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
/-!
# Reflection compatibility in actual Held central covers

The source reflection fixes `x` and inverts `y`. Its action on the concrete
Held model is inner, by `ReflectionModel`. The source presentation is perfect
by its (2,7,17) relations. Uniqueness of maps from a perfect group into a central
extension therefore identifies a reflected presentation map with conjugation
by a lift of that concrete reflector. Thus an equation killed by the original
map remains killed after reflection, including the marked even equations and
the seventh relation used to prove the eighth.

Source: John Bray's `Held/Model/Source/HeG1-P1.M`; the source reflection
calculation in `RelatorLifts/Odd/Symmetry.lean` and its concrete inner
implementer in `BinaryOdd/ReflectionModel.lean`. No faithful presentation or
multiplier theorem is assumed.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd
open RelatorLifts PerfectCentralCovering
private theorem reflected_relations (i : Fin 7) : relationWord x y⁻¹ i = 1 := by
  have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_left
    (by simpa only [relationWord, pow_two] using presentation_relations 0)
  have hy : y ^ 7 = 1 := presentation_relations 1
  fin_cases i
  · exact presentation_relations 0
  · simp only [relationWord, inv_pow, hy, inv_one]
  · have he : x * y⁻¹ = MulAut.conj x ((x * y)⁻¹) := by
      have hxx : x * x = 1 := by simpa only [pow_two] using
        (show x ^ 2 = 1 from presentation_relations 0)
      simp only [MulAut.conj_apply, mul_inv_rev, hx, mul_assoc, hxx, mul_one]
    have hxy : (x * y) ^ 17 = 1 := presentation_relations 2
    simp only [relationWord, he, ← map_pow, inv_pow, hxy, inv_one, map_one]
  · have he : value ((sourceIndices 0).map (fun n => -n)) =
        relationWord x y⁻¹ 3 := by
      simp only [value, sourceIndices, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, conjugate, relationWord, mul_inv_rev, hx, inv_inv]
      group
    exact he.symm.trans (value_neg_eq_one _ (source_value 0))
  · have he : value ((sourceIndices 1).map (fun n => -n)) =
        relationWord x y⁻¹ 4 := by
      simp only [value, sourceIndices, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, conjugate, relationWord, hx, pow_succ, pow_zero]
      group
    exact he.symm.trans (value_neg_eq_one _ (source_value 1))
  · have he : value ((sourceIndices 2).map (fun n => -n)) =
        relationWord x y⁻¹ 5 := by
      simp only [value, sourceIndices, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, conjugate, relationWord, hx, pow_succ, pow_zero]
      group
    exact he.symm.trans (value_neg_eq_one _ (source_value 2))
  · have he : value ((sourceIndices 3).map (fun n => -n)) * (y⁻¹) ^ 7 =
        relationWord x y⁻¹ 6 := by
      simp only [value, sourceIndices, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, conjugate, relationWord, pow_succ, pow_zero]
      group
    rw [inv_pow, hy, inv_one, mul_one] at he
    exact he.symm.trans (value_neg_eq_one _ (source_value 3))

private def reflectionGenerator : Fin 2 → Presentation
  | 0 => x
  | 1 => y⁻¹

private theorem reflection_relators (r : FreeGroup (Fin 2)) (hr : r ∈ definingRelators) :
    FreeGroup.lift reflectionGenerator r = 1 := by
  obtain ⟨i, rfl⟩ := hr
  rw [map_relationWord]
  simpa only [FreeGroup.lift_apply_of, reflectionGenerator] using reflected_relations i

private def reflection : Presentation →* Presentation :=
  PresentedGroup.toGroup reflection_relators

private theorem reflection_x : reflection x = x := PresentedGroup.toGroup.of reflection_relators
private theorem reflection_y : reflection y = y⁻¹ := PresentedGroup.toGroup.of reflection_relators

private theorem reflection_conjugate (n : ℤ) : reflection (conjugate n) = conjugate (-n) := by
  simp only [conjugate, map_mul, map_inv, map_zpow, reflection_x, reflection_y,
    inv_zpow, zpow_neg]

private theorem reflection_value (w : List ℤ) :
    reflection (value w) = value (w.map (fun n => -n)) := by
  simp only [value, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro n hn
  exact reflection_conjugate n


private theorem presentation_perfect : Group.IsPerfect Presentation := by
  have hgen : Subgroup.closure ({x, y} : Set Presentation) = ⊤ := by
    have hr : Set.range (PresentedGroup.of : Fin 2 → Presentation) = {x, y} := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [x, y]
      · rintro (rfl | hz)
        · exact ⟨0, rfl⟩
        · exact ⟨1, Set.mem_singleton_iff.mp hz |>.symm⟩
    rw [← hr]
    exact PresentedGroup.closure_range_of definingRelators
  have hp := Group.isPerfect_closure_pair_of_coprime_triangle x y
    (by decide : Nat.Coprime 2 7) (by decide : Nat.Coprime (2 * 7) 17)
    (presentation_relations 0) (presentation_relations 1) (presentation_relations 2)
  rw [hgen] at hp
  exact Group.IsPerfect.top_iff.mp hp

/-- An actual inner implementer on the concrete generators determines the
reflected lift in every central cover. -/
private theorem reflection_lift_of_inner {E : Type*} [Group E]
    (f : Cover E He) (h : Presentation →* E)
    (ht : f.toMonoidHom.comp h = presentationMap)
    (t : He) (hta : t⁻¹ * a * t = a) (htb : t⁻¹ * b * t = b⁻¹) :
    ∃ c : E, ∀ p : Presentation, h (reflection p) = c⁻¹ * h p * c := by
  let := presentation_perfect
  obtain ⟨c, hc⟩ := f.surjective t
  refine ⟨c, ?_⟩
  have he : h.comp reflection = (MulAut.conj c⁻¹).toMonoidHom.comp h := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq f.toMonoidHom f.ker_le_center
    apply PresentedGroup.ext
    intro i
    have hm (p : Presentation) : f.toMonoidHom (h p) = presentationMap p :=
      DFunLike.congr_fun ht p
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    fin_cases i
    · change f.toMonoidHom (h (reflection x)) = f.toMonoidHom (c⁻¹ * h x * c)
      simp only [reflection_x, map_mul, map_inv, hm, hc, x, presentationMap_of, generator]
      exact hta.symm
    · change f.toMonoidHom (h (reflection y)) = f.toMonoidHom (c⁻¹ * h y * c)
      simp only [reflection_y, map_mul, map_inv, hm, hc, y, presentationMap_of, generator]
      exact htb.symm
  intro p
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    using DFunLike.congr_fun he p


/-- Reflection preserves every identity in a marked image over the literal
Held presentation map. Centrality suffices; no bound on the kernel is needed. -/
theorem image_value_neg_eq_one {E : Type*} [Group E]
    (f : Cover E He) (h : Presentation →* E)
    (ht : f.toMonoidHom.comp h = presentationMap)
    (w : List ℤ) (hw : h (value w) = 1) :
    h (value (w.map (fun n => -n))) = 1 := by
  obtain ⟨c, hc⟩ := reflection_lift_of_inner f h ht
    ReflectionModel.reflector ReflectionModel.reflector_conj_a
    ReflectionModel.reflector_conj_b
  rw [← reflection_value, hc, hw, mul_one, inv_mul_cancel]

private theorem value_reverse (w : List ℤ) : value w.reverse = (value w)⁻¹ := by
  induction w with
  | nil => simp [value]
  | cons a w ih =>
    have ha : (conjugate a)⁻¹ = conjugate a :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using conjugate_sq a)
    simpa only [value, List.reverse_cons, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      mul_inv_rev, ha] using congrArg (fun z => z * conjugate a) ih

private theorem image_value_rotate {E : Type*} [Group E]
    (h : Presentation →* E) (w : List ℤ) (hw : h (value w) = 1) (k : ℕ) :
    h (value (w.rotate k)) = 1 := by
  have hw' : (w.map (fun n => h (conjugate n))).prod = 1 := by
    simpa only [value, map_list_prod, List.map_map, Function.comp_def] using hw
  simpa only [value, map_list_prod, List.map_map, List.map_rotate, Function.comp_def]
    using List.prod_rotate_eq_one_of_prod_eq_one hw' k

/-- The mapped seventh equation implies the eighth, with the reflected-cover
compatibility proved rather than assumed. -/
theorem image_eight_of_seven {E : Type*} [Group E]
    (f : Cover E He) (h : Presentation →* E)
    (ht : f.toMonoidHom.comp h = presentationMap)
    (hseven : h (Subgroup.CosetWordCertificate.eval liftedGenerator
      (relationLetters 7)) = 1) :
    h (Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters 8)) = 1 := by
  rw [relation_eq_value] at hseven ⊢
  have hf := image_value_neg_eq_one f h ht _ hseven
  have hr : h (value (((relationIndices 7).map markedIndex).map
      (fun n => -n)).reverse) = 1 := by
    rw [value_reverse, map_inv, hf, inv_one]
  exact image_value_rotate h _ hr 10

/-- Reflection fixes a central word value, including a possible binary defect. -/
theorem image_value_neg_eq_of_central {E : Type*} [Group E]
    (f : Cover E He) (h : Presentation →* E)
    (ht : f.toMonoidHom.comp h = presentationMap)
    (w : List ℤ) (hw : h (value w) ∈ Subgroup.center E) :
    h (value (w.map (fun n => -n))) = h (value w) := by
  obtain ⟨c, hc⟩ := reflection_lift_of_inner f h ht
    ReflectionModel.reflector ReflectionModel.reflector_conj_a
    ReflectionModel.reflector_conj_b
  rw [← reflection_value, hc]
  rw [Subgroup.mem_center_iff.mp hw c⁻¹]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

private theorem prod_rotate_eq_of_central {E : Type*} [Group E]
    (w : List E) (hw : w.prod ∈ Subgroup.center E) (k : Nat) :
    (w.rotate k).prod = w.prod := by
  rw [List.rotate_eq_drop_append_take_mod, List.prod_append]
  have he : (w.take (k % w.length)).prod * (w.drop (k % w.length)).prod = w.prod := by
    rw [← List.prod_append, List.take_append_drop]
  calc
    _ = (w.take (k % w.length)).prod⁻¹ *
        ((w.take (k % w.length)).prod * (w.drop (k % w.length)).prod) *
        (w.take (k % w.length)).prod := by group
    _ = (w.take (k % w.length)).prod⁻¹ * w.prod *
        (w.take (k % w.length)).prod := by rw [he]
    _ = w.prod := by
      rw [Subgroup.mem_center_iff.mp hw (w.take (k % w.length)).prod⁻¹]
      simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- The eighth value is the inverse of the seventh central value. -/
theorem image_eight_eq_inverse_seven {E : Type*} [Group E]
    (f : Cover E He) (h : Presentation →* E)
    (ht : f.toMonoidHom.comp h = presentationMap)
    (hc : h (Subgroup.CosetWordCertificate.eval liftedGenerator
      (relationLetters 7)) ∈ Subgroup.center E) :
    h (Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters 8)) =
      (h (Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters 7)))⁻¹ := by
  rw [relation_eq_value] at hc ⊢
  rw [relation_eq_value]
  let w := (((relationIndices 7).map markedIndex).map (fun n => -n)).reverse
  have hw : h (value w) = (h (value ((relationIndices 7).map markedIndex)))⁻¹ := by
    rw [value_reverse, map_inv, image_value_neg_eq_of_central f h ht _ hc]
  have hc' : h (value w) ∈ Subgroup.center E := hw ▸ (Subgroup.center E).inv_mem hc
  have hp : ((w.rotate 10).map (fun n => h (conjugate n))).prod =
      (w.map (fun n => h (conjugate n))).prod := by
    rw [List.map_rotate]
    apply prod_rotate_eq_of_central
    simpa only [value, map_list_prod, List.map_map, Function.comp_def] using hc'
  have hrot : h (value (w.rotate 10)) = h (value w) := by
    simpa only [value, map_list_prod, List.map_map, Function.comp_def] using hp
  exact hrot.trans hw

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd
