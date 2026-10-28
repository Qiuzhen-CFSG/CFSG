module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.Levi
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.Generation
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.SplitRetraction.Grading
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.Collection
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.Curves

/-!
# Normality of the binary linear root radical

The positive-root exchange identities normalize the radical: after exchanging
a radical root past a positive root, all correction roots have height greater
than one, hence lie outside the end-node Levi. Root elements are involutions
in characteristic two, so the exchange is directly a conjugation formula.

For the two negative simple root groups, use their actual three-factor Weyl
words. The characteristic-two route comparison for the integral F₄ matrices
identifies Weyl conjugation with simple reflection. End-node reflections
preserve positivity and the nonzero middle coefficients of radical roots.
Thus these Weyl words normalize the radical, and the binary negative simple
elements do too. Closure of the seed generators proves relative normality.

The only additional premise is the positive-support binary exchange identity
from `RadicalCoordinates.wordInSubgroup_surjective_of_exchange`. This module
proves a conditional helper for the split retraction, without assuming
normality, any order formula, or a Levi product identification.

Source: the standard root Levi construction underlying Aschbacher–Smith,
F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.BinaryLinear
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open LargeLocalSeeds Subgroup

local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem coefficient_sub_simple (x : Vec 4) (t : ℝ) (i j : Fin 4) (h : i ≠ j) :
    typeF4SimpleCoefficient (x - t • typeF4SimpleRoot i) j =
      typeF4SimpleCoefficient x j := by
  fin_cases i <;> fin_cases j
  all_goals first | exact False.elim (h rfl) |
    (norm_num [typeF4SimpleCoefficient, typeF4SimpleRoot, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_two, Matrix.cons_val_three] <;> ring)

/-- End-node reflections preserve the positive radical support. -/
theorem isRadicalRoot_end_reflection (i : Fin 4) (hi : i ∈ leviNodes .linear)
    (r : F4Chevalley.Root) (hr : IsRadicalRoot .linear r) :
    IsRadicalRoot .linear (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) := by
  have hne : r ≠ typeF4SimpleRootIndex i := fun h =>
    isRadicalRoot_not_isLeviRoot hr ⟨i, hi, Or.inl h⟩
  have hs := (typeF4RootPairing_baseEquiv i).property
  have hpos := hr.1.add_zsmul hne hs
    (show typeF4RootPairing.root
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) =
      typeF4RootPairing.root r +
        (-typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i)) •
          typeF4RootPairing.root (typeF4SimpleRootIndex i) by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root' ℤ]
      simp only [neg_smul, sub_eq_add_neg])
  refine ⟨hpos, ?_⟩
  obtain ⟨j, hj, hc⟩ := hr.2
  refine ⟨j, hj, ?_⟩
  have hval : (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      r.val - typeF4RootPairing.pairing r (typeF4SimpleRootIndex i) • typeF4SimpleRoot i := by
    rw [← typeF4SimpleRootIndex_val]
    exact (typeF4RootPairing.root_reflectionPerm (typeF4SimpleRootIndex i) r).trans
        (typeF4RootPairing.reflection_apply_root (typeF4SimpleRootIndex i) r)
  rw [hval, coefficient_sub_simple _ _ i j (fun h => hj (h ▸ hi))]
  exact hc

/-- A simple Weyl word conjugates radical root matrices by its reflection. -/
theorem weylWord_conj_radical_root (i : Fin 4) (hi : i ∈ leviNodes .linear)
    (r : F4Chevalley.Root) (hr : IsRadicalRoot .linear r) (t : CoefficientField 0) :
    weylWord 0 (typeF4SimpleRootIndex i) 1 * rootGeneratorInGroup 0 r t *
      (weylWord 0 (typeF4SimpleRootIndex i) 1)⁻¹ =
      rootGeneratorInGroup 0
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t := by
  let route := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  have ht : reflectionWord (P := typeF4RootPairing)
      (typeF4RootPairing_baseEquiv i :: route.word) route.simple =
      typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r := by
    change typeF4RootPairing.reflectionPerm _ (reflectionWord route.word route.simple) = _
    rw [route.target]
    rfl
  apply Subtype.ext
  change (weylWord 0 (typeF4SimpleRootIndex i) 1).val * F4Chevalley.rootCurve r t *
    ((weylWord 0 (typeF4SimpleRootIndex i) 1).val)⁻¹ =
      F4Chevalley.rootCurve (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t
  rw [WordRelations.rootCurve_of_pos_transport _
    (isRadicalRoot_end_reflection i hi r hr).1 _ _ ht,
    WordRelations.rootCurve_of_pos_route r hr.1 t,
    WordRelations.titsUnit_cons]
  have hw : (weylWord 0 (typeF4SimpleRootIndex i) 1).val =
      F4Chevalley.rootCurve (typeF4RootPairing_baseEquiv i).val (1 : CoefficientField 0) *
      F4Chevalley.rootCurve (-(typeF4RootPairing_baseEquiv i).val) (-1) *
      F4Chevalley.rootCurve (typeF4RootPairing_baseEquiv i).val 1 := by
    simp only [weylWord, inv_one]
    rfl
  rw [hw]
  dsimp only [route]
  group


private theorem root_degree_levi_le_one {r : F4Chevalley.Root} (hr : IsLeviRoot r) :
    RadicalCoordinates.rootDegree r ≤ 1 := by
  have hd (i : Fin 4) : typeF4RootPairing_base.height (typeF4SimpleRootIndex i) = 1 :=
    typeF4RootPairing_base.height_one_of_mem_support
      (typeF4RootPairing_baseEquiv i).property
  rcases hr with ⟨i, _, rfl | rfl⟩
  · rw [RadicalCoordinates.rootDegree, hd]
    decide
  · rw [RadicalCoordinates.rootDegree,
      typeF4RootPairing_base.height_reflectionPerm_self, hd]
    decide

private theorem radical_of_degree_gt_one (r : RadicalCoordinates.Root .positive)
    (hr : 1 < RadicalCoordinates.rootDegree r.val) : IsRadicalRoot .linear r.val := by
  rcases isSeedRoot_radical_or_levi (Or.inl r.property) with h | h
  · exact h
  · have := root_degree_levi_le_one h
    omega

private theorem root_mul_self (r : F4Chevalley.Root) (t : CoefficientField 0) :
    rootGeneratorInGroup 0 r t * rootGeneratorInGroup 0 r t = 1 := by
  apply Subtype.ext
  change F4Chevalley.rootCurve r t * F4Chevalley.rootCurve r t = 1
  rw [← F4Chevalley.rootCurve_add, CharTwo.add_self_eq_zero,
    F4Chevalley.rootCurve_zero]

private theorem mem_radical_normalizer_of_conj_roots (g : SplitGroup 0)
    (h : ∀ (r : F4Chevalley.Root) (t : CoefficientField 0),
      IsRadicalRoot .linear r →
      g * rootGeneratorInGroup 0 r t * g⁻¹ ∈ splitRadical 0 .linear) :
    g ∈ normalizer (splitRadical 0 .linear) := by
  have hle : splitRadical 0 .linear ≤
      (splitRadical 0 .linear).comap (MulAut.conj g).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    exact h r t hr
  apply mem_normalizer_fintype
  intro x hx
  exact hle hx

/-- End-node Weyl words normalize the actual root-generated radical. -/
theorem weylWord_mem_radical_normalizer (i : Fin 4) (hi : i ∈ leviNodes .linear) :
    weylWord 0 (typeF4SimpleRootIndex i) 1 ∈ normalizer (splitRadical 0 .linear) := by
  apply mem_radical_normalizer_of_conj_roots
  intro r t hr
  rw [weylWord_conj_radical_root i hi r hr t]
  exact subset_closure ⟨_, t, isRadicalRoot_end_reflection i hi r hr, rfl⟩

/-- Positive root exchanges imply normality of the specified radical inside
its binary linear seed. The exchange identities remain the sole extra premise. -/
theorem splitRadicalInSeed_normal_of_positive_exchanges
    (hswap : ∀ (r s : RadicalCoordinates.Root .positive) (a b : CoefficientField 0), r ≠ s →
      ∃ correction : List (RadicalCoordinates.Root .positive × CoefficientField 0),
        (∀ z ∈ correction,
          max (RadicalCoordinates.rootDegree r.val) (RadicalCoordinates.rootDegree s.val) <
            RadicalCoordinates.rootDegree z.1.val) ∧
        rootGeneratorInGroup 0 r.val a * rootGeneratorInGroup 0 s.val b =
          rootGeneratorInGroup 0 s.val b * rootGeneratorInGroup 0 r.val a *
            FilteredCollection.wordProduct
              (fun q : RadicalCoordinates.Root .positive => rootGeneratorInGroup 0 q.val) correction) :
    (splitRadicalInSeed 0).Normal := by
  let N := splitRadical 0 .linear
  have hp (s : F4Chevalley.Root) (b : CoefficientField 0)
      (hs : typeF4RootPairing_base.IsPos s) :
      rootGeneratorInGroup 0 s b ∈ normalizer N := by
    by_cases hsr : IsRadicalRoot .linear s
    · exact N.le_normalizer (subset_closure ⟨s, b, hsr, rfl⟩)
    apply mem_radical_normalizer_of_conj_roots
    intro r a hr
    obtain ⟨c, hc, he⟩ := hswap ⟨r, hr.1⟩ ⟨s, hs⟩ a b (by
      intro heq
      have hrs : r = s := congrArg Subtype.val heq
      exact hsr (hrs ▸ hr))
    have hcmem : FilteredCollection.wordProduct
        (fun q : RadicalCoordinates.Root .positive => rootGeneratorInGroup 0 q.val) c ∈ N := by
      apply Subgroup.list_prod_mem
      intro x hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      apply Subgroup.subset_closure
      refine ⟨z.1.val, z.2, radical_of_degree_gt_one z.1 ?_, rfl⟩
      have hd := RadicalCoordinates.rootDegree_pos (⟨s, hs⟩ : RadicalCoordinates.Root .positive)
      have hc' := hc z hz
      have hm := Nat.le_max_right (RadicalCoordinates.rootDegree r) (RadicalCoordinates.rootDegree s)
      dsimp only at hd hc'
      omega
    have hinv : (rootGeneratorInGroup 0 s b)⁻¹ = rootGeneratorInGroup 0 s b :=
      inv_eq_of_mul_eq_one_left (root_mul_self s b)
    have he' : rootGeneratorInGroup 0 s b * rootGeneratorInGroup 0 r a *
        (rootGeneratorInGroup 0 s b)⁻¹ = rootGeneratorInGroup 0 r a *
          FilteredCollection.wordProduct
            (fun q : RadicalCoordinates.Root .positive => rootGeneratorInGroup 0 q.val) c := by
      rw [hinv, mul_assoc, he]
      rw [← mul_assoc (rootGeneratorInGroup 0 s b),
        ← mul_assoc (rootGeneratorInGroup 0 s b), root_mul_self s b, one_mul]
    rw [he']
    exact N.mul_mem (subset_closure ⟨r, a, hr, rfl⟩) hcmem
  have hn (i : Fin 4) (hi : i ∈ leviNodes .linear) (t : CoefficientField 0) :
      rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) t ∈ normalizer N := by
    have ht : t = 0 ∨ t = 1 := by
      apply eq_zero_or_one_of_sq_eq_self
      simpa using field_pow 0 t
    rcases ht with rfl | rfl
    · have he : rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 0 = 1 := by
        apply Subtype.ext
        exact F4Chevalley.rootCurve_zero _
      rw [he]
      exact Subgroup.one_mem _
    · let x := rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1
      have hx : x ∈ normalizer N := hp _ _
        (typeF4RootPairing_base.isPos_of_mem_support
          (typeF4RootPairing_baseEquiv i).property)
      have hw := weylWord_mem_radical_normalizer i hi
      have he : x * weylWord 0 (typeF4SimpleRootIndex i) 1 * x =
          rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 1 := by
        simp only [weylWord, inv_one, CharTwo.neg_eq]
        change x * (x * rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 1 * x) * x = _
        calc
          _ = (x * x) * rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 1 * (x * x) := by group
          _ = _ := by rw [root_mul_self]; simp
      rw [← he]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hw) hx
  apply normal_subgroupOf_of_le_normalizer
  apply (closure_le _).mpr
  rintro _ ⟨r, t, hr, rfl⟩
  rcases hr with hr | ⟨i, hi, rfl⟩
  · exact hp r t hr
  · exact hn i hi t

end ReeF4.Parabolics.BinaryLinear
