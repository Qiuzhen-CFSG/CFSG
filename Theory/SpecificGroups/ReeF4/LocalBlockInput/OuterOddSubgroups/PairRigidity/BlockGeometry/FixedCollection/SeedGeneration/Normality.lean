module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.Levi
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges

/-!
# Relative normality of both split Ree seed radicals

Positive root exchanges have correction roots in the positive cone of the
inputs. A radical input therefore keeps all corrections in the same radical.
Simple reflections at Levi nodes preserve this support. The all-parameter
simple Tits conjugation theorem then handles every negative simple generator,
so the entire seed normalizes its specified radical over every coefficient field.

This extends the argument of `BinaryLocals/SuzukiProjection/SplitFactorization/
RootNormalization.lean` to both sides and all fields, preserving that module.
Normality is relative to the seed throughout.
Source: GLS3, 2.3.7 and §2.4, `refs/KGroup/GLS3/chapter2.tex`, and the
Levi construction underlying Aschbacher–Smith F.1.12.
-/

public section
noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LargeLocalSeeds Parabolics Parabolics.RadicalCoordinates
open RootPairing.IntegralGeckConstruction
open PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {m : ℕ} {side : Side}

private lemma coefficient_add (x y : Vec 4) (i : Fin 4) :
    typeF4SimpleCoefficient (x + y) i =
      typeF4SimpleCoefficient x i + typeF4SimpleCoefficient y i := by
  fin_cases i <;> simp [typeF4SimpleCoefficient] <;> ring

private lemma coefficient_smul (c : ℝ) (x : Vec 4) (i : Fin 4) :
    typeF4SimpleCoefficient (c • x) i = c * typeF4SimpleCoefficient x i := by
  fin_cases i <;> simp [typeF4SimpleCoefficient] <;> ring

private lemma coefficient_simple (i j : Fin 4) :
    typeF4SimpleCoefficient (typeF4SimpleRoot i) j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [typeF4SimpleRoot, typeF4SimpleCoefficient, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

private lemma positive_coefficients {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) (i : Fin 4) :
    0 ≤ typeF4SimpleCoefficient r.val i := by
  apply hr.induction_on_add
  · intro r hr
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨r, hr⟩
    have h : typeF4SimpleRoot j = r.val := congrArg (fun x => x.val.val) hj
    rw [← h, coefficient_simple]
    split <;> norm_num
  · intro r s t h hr hs
    change t.val = r.val + s.val at h
    rw [h, coefficient_add]
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨s, hs⟩
    have h : typeF4SimpleRoot j = s.val := congrArg (fun x => x.val.val) hj
    rw [← h, coefficient_simple]
    split <;> linarith

/-- A correction root remains radical when its first input is radical and
its second input is any positive root. -/
private theorem positiveCone_radical_left {r s t : F4Chevalley.Root}
    (hr : IsRadicalRoot side r) (hs : typeF4RootPairing_base.IsPos s)
    (ht : PositiveCone r s t) : IsRadicalRoot side t := by
  have hp := (positiveCone_supported_degree (k := .positive) ⟨r, hr.1⟩ ⟨s, hs⟩ ht).1
  obtain ⟨p, q, hpp, hqp, he⟩ := ht
  obtain ⟨i, hi, hri⟩ := hr.2
  refine ⟨hp, i, hi, ?_⟩
  change t.val = p • r.val + q • s.val at he
  rw [he, coefficient_add, ← Nat.cast_smul_eq_nsmul ℝ,
    ← Nat.cast_smul_eq_nsmul ℝ, coefficient_smul, coefficient_smul]
  exact ne_of_gt (add_pos_of_pos_of_nonneg
    (mul_pos (by exact_mod_cast hpp)
      (lt_of_le_of_ne (positive_coefficients hr.1 i) (Ne.symm hri)))
    (mul_nonneg (Nat.cast_nonneg q) (positive_coefficients hs i)))

private lemma radical_ne_simple {r : F4Chevalley.Root}
    (hr : IsRadicalRoot side r) {i : Fin 4} (hi : i ∈ leviNodes side) :
    r ≠ typeF4SimpleRootIndex i := by
  rintro rfl
  obtain ⟨j, hj, he⟩ := hr.2
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  exact he (by simp only [typeF4SimpleRootIndex, coefficient_simple, if_neg hij])

/-- Reflection at either middle node preserves the Suzuki radical support.
The outside simple coefficients are unchanged, and the reflected root stays positive. -/
private theorem isRadicalRoot_simpleReflection {r : F4Chevalley.Root}
    (hr : IsRadicalRoot side r) {i : Fin 4} (hi : i ∈ leviNodes side) :
    IsRadicalRoot side (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) := by
  refine ⟨hr.1.reflectionPerm (typeF4RootPairing_baseEquiv i).property
    (radical_ne_simple hr hi), ?_⟩
  obtain ⟨j, hj, he⟩ := hr.2
  refine ⟨j, hj, ?_⟩
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  have heq : (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      r.val + (-typeF4RootPairing.pairing r (typeF4SimpleRootIndex i)) • typeF4SimpleRoot i := by
    change typeF4RootPairing.root _ = typeF4RootPairing.root r + _
    rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root]
    change r.val - _ • typeF4SimpleRoot i = r.val + (-_) • typeF4SimpleRoot i
    simp only [neg_smul, sub_eq_add_neg]
  simpa only [heq, coefficient_add, coefficient_smul, coefficient_simple,
    if_neg hij, mul_zero, add_zero] using he

private theorem rootGenerator_conj_radical_of_matrixExchange
    (r s : F4Chevalley.Root) (a b : CoefficientField m)
    (hr : typeF4RootPairing_base.IsPos r) (hs : IsRadicalRoot side s)
    (h : MatrixExchange s r b (-a)) :
    rootGeneratorInGroup m r a * rootGeneratorInGroup m s b *
      (rootGeneratorInGroup m r a)⁻¹ ∈ splitRadical m side := by
  obtain ⟨c, hc, he⟩ := h
  let W := (c.map (fun z => rootGeneratorInGroup m z.1 z.2)).prod
  have hW : W ∈ splitRadical m side := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact subset_closure ⟨_, _, positiveCone_radical_left hs hr (hc z hz), rfl⟩
  have hWval : W.val.val =
      (c.map (fun z => (F4Chevalley.rootCurve z.1 z.2).val)).prod := by
    let ρ : SplitGroup m →* MatrixCarrier m :=
      (Units.coeHom (MatrixCarrier m)).comp (SplitGroup m).subtype
    change ρ ((c.map (fun z => rootGeneratorInGroup m z.1 z.2)).prod) = _
    rw [map_list_prod, List.map_map]
    rfl
  have he' : rootGeneratorInGroup m s b * rootGeneratorInGroup m r (-a) =
      rootGeneratorInGroup m r (-a) * rootGeneratorInGroup m s b * W := by
    apply Subtype.ext
    apply Units.ext
    change (F4Chevalley.rootCurve s b).val * (F4Chevalley.rootCurve r (-a)).val =
      (F4Chevalley.rootCurve r (-a)).val * (F4Chevalley.rootCurve s b).val * W.val.val
    rw [hWval]
    exact he
  have hinv : rootGeneratorInGroup m r (-a) = (rootGeneratorInGroup m r a)⁻¹ :=
    (Subtype.ext (F4Chevalley.rootCurve_inv r a)).symm
  rw [hinv] at he'
  have he'' : rootGeneratorInGroup m r a * rootGeneratorInGroup m s b *
      (rootGeneratorInGroup m r a)⁻¹ = rootGeneratorInGroup m s b * W := by
    calc
      _ = rootGeneratorInGroup m r a *
        (rootGeneratorInGroup m s b * (rootGeneratorInGroup m r a)⁻¹) := by group
      _ = rootGeneratorInGroup m r a *
        ((rootGeneratorInGroup m r a)⁻¹ * rootGeneratorInGroup m s b * W) := by rw [he']
      _ = _ := by group
  rw [he'']
  exact (splitRadical m side).mul_mem (subset_closure ⟨s, b, hs, rfl⟩) hW

/-- Positive seed roots preserve the radical once the positive root-sum
identities are supplied. Absent sums and radical conjugators are discharged here. -/
private theorem positive_rootGenerator_conj_radical_of_rootSum_exchanges
    (hrootSum : ∀ (r s : F4Chevalley.Root),
      typeF4RootPairing_base.IsPos r → typeF4RootPairing_base.IsPos s → r ≠ s →
      typeF4RootPairing.root r + typeF4RootPairing.root s ∈ Set.range typeF4RootPairing.root →
      ∀ a b : CoefficientField m, MatrixExchange r s a b)
    (r s : F4Chevalley.Root) (a b : CoefficientField m)
    (hr : typeF4RootPairing_base.IsPos r) (hs : IsRadicalRoot side s) :
    rootGeneratorInGroup m r a * rootGeneratorInGroup m s b *
      (rootGeneratorInGroup m r a)⁻¹ ∈ splitRadical m side := by
  by_cases hR : IsRadicalRoot side r
  · exact (splitRadical m side).mul_mem
      ((splitRadical m side).mul_mem (subset_closure ⟨r, a, hR, rfl⟩)
        (subset_closure ⟨s, b, hs, rfl⟩))
      ((splitRadical m side).inv_mem (subset_closure ⟨r, a, hR, rfl⟩))
  · have hsr : s ≠ r := fun h => hR (h ▸ hs)
    by_cases hsum : typeF4RootPairing.root s + typeF4RootPairing.root r ∈
        Set.range typeF4RootPairing.root
    · exact rootGenerator_conj_radical_of_matrixExchange r s a b hr hs
        (hrootSum s r hs.1 hr hsr hsum b (-a))
    · have hc := rootGenerator_commute_of_no_sum m
        (k := .positive) ⟨s, hs.1⟩ ⟨r, hr⟩ hsum b a
      rw [← hc.eq, mul_assoc, mul_inv_cancel, mul_one]
      exact subset_closure ⟨s, b, hs, rfl⟩


private theorem positive_root_mem_normalizer (r : F4Chevalley.Root)
    (a : CoefficientField m) (hr : typeF4RootPairing_base.IsPos r) :
    rootGeneratorInGroup m r a ∈ normalizer (splitRadical m side) := by
  have hc : splitRadical m side ≤
      (splitRadical m side).comap (MulAut.conj (rootGeneratorInGroup m r a)).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨s, b, hs, rfl⟩
    apply positive_rootGenerator_conj_radical_of_rootSum_exchanges _ r s a b hr hs
    intro u v hu hv huv hsum c e
    by_cases hlen : IsLongRoot u ↔ IsLongRoot v
    · exact matrixExchange_of_equal_length_sum m u v hu hv huv hlen hsum c e
    · exact matrixExchange_of_mixed_length_sum m u v hu hv huv hlen hsum c e
  exact mem_normalizer_fintype (fun _ hx => hc hx)

private theorem simpleWeyl_conj (i : Fin 4) (r : F4Chevalley.Root)
    (t : CoefficientField m) :
    weylWord m (typeF4SimpleRootIndex i) 1 * rootGeneratorInGroup m r t *
      (weylWord m (typeF4SimpleRootIndex i) 1)⁻¹ =
    rootGeneratorInGroup m
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t := by
  have hw : (weylWord m (typeF4SimpleRootIndex i) 1).val =
      WordRelations.titsUnit [typeF4RootPairing_baseEquiv i] := by
    rw [WordRelations.titsUnit_cons, WordRelations.titsUnit_nil, mul_one]
    change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ *
      F4Chevalley.rootCurve _ _ = _
    simp only [inv_one, typeF4RootPairing_baseEquiv_val]
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, rootGeneratorInGroup_coe,
    hw, typeF4RootPairing_baseEquiv_val] using
    simple_conj (typeF4RootPairing_baseEquiv i) r t

private theorem simpleWeyl_mem_normalizer (i : Fin 4) (hi : i ∈ leviNodes side) :
    weylWord m (typeF4SimpleRootIndex i) 1 ∈ normalizer (splitRadical m side) := by
  have hc : splitRadical m side ≤ (splitRadical m side).comap
      (MulAut.conj (weylWord m (typeF4SimpleRootIndex i) 1)).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    change _ * rootGeneratorInGroup m r t * _ ∈ splitRadical m side
    rw [simpleWeyl_conj]
    exact subset_closure ⟨_, _, isRadicalRoot_simpleReflection hr hi, rfl⟩
  exact mem_normalizer_fintype (fun _ hx => hc hx)

/-- The positive-root radical is normalized by its entire split seed over
every coefficient field. Negative simple parameters are obtained by actual
simple Weyl conjugation, with no binary-field restriction. -/
theorem splitSeed_le_radical_normalizer (m : ℕ) (side : Side) :
    splitSeed m side ≤ normalizer (splitRadical m side) := by
  apply (closure_le _).mpr
  rintro _ ⟨r, a, hr, rfl⟩
  rcases hr with hr | ⟨i, hi, rfl⟩
  · exact positive_root_mem_normalizer r a hr
  · have hp := positive_root_mem_normalizer (side := side) (typeF4SimpleRootIndex i) a
      (typeF4RootPairing_base.isPos_of_mem_support
        (typeF4RootPairing_baseEquiv i).property)
    have hw := simpleWeyl_mem_normalizer (m := m) i hi
    have he := simpleWeyl_conj i (typeF4SimpleRootIndex i) a
    change _ = rootGeneratorInGroup m (-typeF4SimpleRootIndex i) a at he
    rw [← he]
    exact mul_mem (mul_mem hw hp) (inv_mem hw)

/-- Normality is relative to the actual seed, not the ambient split F₄ group. -/
theorem radicalInSplitSeed_normal (m : ℕ) (side : Side) :
    (radicalInSplitSeed m side).Normal :=
  (normal_subgroupOf_iff_le_normalizer
    ((splitRadical_le_unipotent m side).trans
      (splitUnipotent_le_splitSeed m side))).mpr
    (splitSeed_le_radical_normalizer m side)

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
