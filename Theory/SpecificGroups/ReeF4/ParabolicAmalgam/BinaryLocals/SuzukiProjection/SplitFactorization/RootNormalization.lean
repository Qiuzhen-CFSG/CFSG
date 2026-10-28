module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.Levi
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.RootSums
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.Commuting
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.EqualLength
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.MixedLength
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.Curves

/-!
# Root conjugation in the binary Suzuki seed

The positive radical support is closed under positive combinations with any
positive root and under reflection at either middle node. Integral Tits route
comparison gives the actual Weyl conjugation of the radical matrices. Over the
binary field, each negative simple generator is either the identity or a product
of its positive generator, its Weyl word, and its positive generator again.
Thus the negative seed-root cases reduce to the positive ones.

A reversed positive matrix exchange expresses the required conjugate as a
radical generator times a radical correction word. The absent-root-sum case
uses the proved integral operator and divided-power commutation theorem.
The equal- and mixed-length root-sum matrix identities discharge the remaining
cases, giving unconditional seed-root conjugation. No normality or
complementarity is assumed.

This is the matrix calculation underlying the binary parabolic Levi construction
in Aschbacher–Smith, F.1.12(I)(5), printed pp.263–264 (PDF pp.274–275) of
`refs/quasithin.pdf`. The actual root curves and their integral normalization
are those of `F4IntegralChevalleyRepresentation`.
-/

open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds Subgroup
open ReeF4.Parabolics.RadicalCoordinates
open scoped Classical
public section
noncomputable section
namespace ReeF4.Parabolics.BinarySuzuki.RootNormalization
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

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
theorem positiveCone_radical_left {r s t : F4Chevalley.Root}
    (hr : IsRadicalRoot .suzuki r) (hs : typeF4RootPairing_base.IsPos s)
    (ht : PositiveCone r s t) : IsRadicalRoot .suzuki t := by
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
    (hr : IsRadicalRoot .suzuki r) {i : Fin 4} (hi : i ∈ leviNodes .suzuki) :
    r ≠ typeF4SimpleRootIndex i := by
  rintro rfl
  obtain ⟨j, hj, he⟩ := hr.2
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  exact he (by simp only [typeF4SimpleRootIndex, coefficient_simple, if_neg hij])

/-- Reflection at either middle node preserves the Suzuki radical support.
The outside simple coefficients are unchanged, and the reflected root stays positive. -/
theorem isRadicalRoot_simpleReflection {r : F4Chevalley.Root}
    (hr : IsRadicalRoot .suzuki r) {i : Fin 4} (hi : i ∈ leviNodes .suzuki) :
    IsRadicalRoot .suzuki (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) := by
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

private lemma weylWord_val (i : Fin 4) :
    (weylWord 0 (typeF4SimpleRootIndex i) 1).val =
      WordRelations.titsUnit [typeF4RootPairing_baseEquiv i] := by
  rw [WordRelations.titsUnit_cons, WordRelations.titsUnit_nil, mul_one]
  change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ *
    F4Chevalley.rootCurve _ _ = _
  simp only [inv_one, typeF4RootPairing_baseEquiv_val]

/-- The actual simple Weyl matrix conjugates each radical root curve to
its reflected curve, by characteristic-two independence of integral Tits routes. -/
theorem weylWord_conj_radicalRoot {r : F4Chevalley.Root}
    (hr : IsRadicalRoot .suzuki r) {i : Fin 4} (hi : i ∈ leviNodes .suzuki)
    (t : CoefficientField 0) :
    weylWord 0 (typeF4SimpleRootIndex i) 1 * rootGeneratorInGroup 0 r t *
      (weylWord 0 (typeF4SimpleRootIndex i) 1)⁻¹ =
    rootGeneratorInGroup 0
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t := by
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  have hz : reflectionWord (P := typeF4RootPairing)
      (typeF4RootPairing_baseEquiv i :: z.word) z.simple =
      typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r := by
    simp only [reflectionWord, z.target, typeF4RootPairing_baseEquiv_val]
  have ht := WordRelations.rootCurve_of_pos_transport _
    (isRadicalRoot_simpleReflection hr hi).1 _ _ hz t
  apply Subtype.ext
  change (weylWord 0 (typeF4SimpleRootIndex i) 1).val * F4Chevalley.rootCurve r t *
    ((weylWord 0 (typeF4SimpleRootIndex i) 1).val)⁻¹ =
      F4Chevalley.rootCurve
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t
  rw [weylWord_val, ht, WordRelations.rootCurve_of_pos_route r hr.1]
  simp only [WordRelations.titsUnit_cons, WordRelations.titsUnit_nil, mul_one]
  dsimp only [z]
  group

/-- The two simple Weyl words normalize the specified radical without
any seed normality or factorization hypothesis. -/
theorem weylWord_mem_radical_normalizer {i : Fin 4} (hi : i ∈ leviNodes .suzuki) :
    weylWord 0 (typeF4SimpleRootIndex i) 1 ∈ normalizer (splitRadical 0 .suzuki) := by
  let w := weylWord 0 (typeF4SimpleRootIndex i) 1
  rw [mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    change w * rootGeneratorInGroup 0 r t * w⁻¹ ∈ splitRadical 0 .suzuki
    rw [weylWord_conj_radicalRoot hr hi]
    exact subset_closure ⟨_, _, isRadicalRoot_simpleReflection hr hi, rfl⟩
  · apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    refine ⟨rootGeneratorInGroup 0
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t,
      subset_closure ⟨_, _, isRadicalRoot_simpleReflection hr hi, rfl⟩, ?_⟩
    change w * rootGeneratorInGroup 0 _ t * w⁻¹ = _
    rw [weylWord_conj_radicalRoot (isRadicalRoot_simpleReflection hr hi) hi,
      typeF4RootPairing.reflectionPerm_involutive]

/-- A reversed matrix exchange gives radical membership directly: the
correction word lies in the radical, without further conjugation of that word. -/
theorem rootGenerator_conj_radical_of_matrixExchange
    (r s : F4Chevalley.Root) (a b : CoefficientField 0)
    (hr : typeF4RootPairing_base.IsPos r) (hs : IsRadicalRoot .suzuki s)
    (h : MatrixExchange s r b (-a)) :
    rootGeneratorInGroup 0 r a * rootGeneratorInGroup 0 s b *
      (rootGeneratorInGroup 0 r a)⁻¹ ∈ splitRadical 0 .suzuki := by
  obtain ⟨c, hc, he⟩ := h
  let W := (c.map (fun z => rootGeneratorInGroup 0 z.1 z.2)).prod
  have hW : W ∈ splitRadical 0 .suzuki := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact subset_closure ⟨_, _, positiveCone_radical_left hs hr (hc z hz), rfl⟩
  have hWval : W.val.val =
      (c.map (fun z => (F4Chevalley.rootCurve z.1 z.2).val)).prod := by
    let ρ : SplitGroup 0 →* MatrixCarrier 0 :=
      (Units.coeHom (MatrixCarrier 0)).comp (SplitGroup 0).subtype
    change ρ ((c.map (fun z => rootGeneratorInGroup 0 z.1 z.2)).prod) = _
    rw [map_list_prod, List.map_map]
    rfl
  have he' : rootGeneratorInGroup 0 s b * rootGeneratorInGroup 0 r (-a) =
      rootGeneratorInGroup 0 r (-a) * rootGeneratorInGroup 0 s b * W := by
    apply Subtype.ext
    apply Units.ext
    change (F4Chevalley.rootCurve s b).val * (F4Chevalley.rootCurve r (-a)).val =
      (F4Chevalley.rootCurve r (-a)).val * (F4Chevalley.rootCurve s b).val * W.val.val
    rw [hWval]
    exact he
  have hinv : rootGeneratorInGroup 0 r (-a) = (rootGeneratorInGroup 0 r a)⁻¹ :=
    (Subtype.ext (F4Chevalley.rootCurve_inv r a)).symm
  rw [hinv] at he'
  have he'' : rootGeneratorInGroup 0 r a * rootGeneratorInGroup 0 s b *
      (rootGeneratorInGroup 0 r a)⁻¹ = rootGeneratorInGroup 0 s b * W := by
    calc
      _ = rootGeneratorInGroup 0 r a *
        (rootGeneratorInGroup 0 s b * (rootGeneratorInGroup 0 r a)⁻¹) := by group
      _ = rootGeneratorInGroup 0 r a *
        ((rootGeneratorInGroup 0 r a)⁻¹ * rootGeneratorInGroup 0 s b * W) := by rw [he']
      _ = _ := by group
  rw [he'']
  exact (splitRadical 0 .suzuki).mul_mem (subset_closure ⟨s, b, hs, rfl⟩) hW

/-- Positive seed roots preserve the radical once the positive root-sum
identities are supplied. Absent sums and radical conjugators are discharged here. -/
theorem positive_rootGenerator_conj_radical_of_rootSum_exchanges
    (hrootSum : ∀ (r s : F4Chevalley.Root),
      typeF4RootPairing_base.IsPos r → typeF4RootPairing_base.IsPos s → r ≠ s →
      typeF4RootPairing.root r + typeF4RootPairing.root s ∈ Set.range typeF4RootPairing.root →
      ∀ a b : CoefficientField 0, MatrixExchange r s a b)
    (r s : F4Chevalley.Root) (a b : CoefficientField 0)
    (hr : typeF4RootPairing_base.IsPos r) (hs : IsRadicalRoot .suzuki s) :
    rootGeneratorInGroup 0 r a * rootGeneratorInGroup 0 s b *
      (rootGeneratorInGroup 0 r a)⁻¹ ∈ splitRadical 0 .suzuki := by
  by_cases hR : IsRadicalRoot .suzuki r
  · exact (splitRadical 0 .suzuki).mul_mem
      ((splitRadical 0 .suzuki).mul_mem (subset_closure ⟨r, a, hR, rfl⟩)
        (subset_closure ⟨s, b, hs, rfl⟩))
      ((splitRadical 0 .suzuki).inv_mem (subset_closure ⟨r, a, hR, rfl⟩))
  · have hsr : s ≠ r := fun h => hR (h ▸ hs)
    by_cases hsum : typeF4RootPairing.root s + typeF4RootPairing.root r ∈
        Set.range typeF4RootPairing.root
    · exact rootGenerator_conj_radical_of_matrixExchange r s a b hr hs
        (hrootSum s r hs.1 hr hsr hsum b (-a))
    · have hc := rootGenerator_commute_of_no_sum 0
        (k := .positive) ⟨s, hs.1⟩ ⟨r, hr⟩ hsum b a
      rw [← hc.eq, mul_assoc, mul_inv_cancel, mul_one]
      exact subset_closure ⟨s, b, hs, rfl⟩

private theorem positive_rootGenerator_mem_radical_normalizer
    (hpos : ∀ (r s : F4Chevalley.Root) (a b : CoefficientField 0),
      typeF4RootPairing_base.IsPos r → IsRadicalRoot .suzuki s →
      rootGeneratorInGroup 0 r a * rootGeneratorInGroup 0 s b *
        (rootGeneratorInGroup 0 r a)⁻¹ ∈ splitRadical 0 .suzuki)
    (r : F4Chevalley.Root) (a : CoefficientField 0)
    (hr : typeF4RootPairing_base.IsPos r) :
    rootGeneratorInGroup 0 r a ∈ normalizer (splitRadical 0 .suzuki) := by
  have hc (t : CoefficientField 0) : splitRadical 0 .suzuki ≤
      (splitRadical 0 .suzuki).comap (MulAut.conj (rootGeneratorInGroup 0 r t)) := by
    apply (closure_le _).mpr
    rintro _ ⟨s, b, hs, rfl⟩
    exact hpos r s t b hr hs
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hc a hy, fun hy => ?_⟩
  have he := hc (-a) hy
  change rootGeneratorInGroup 0 r (-a) *
    (rootGeneratorInGroup 0 r a * y * (rootGeneratorInGroup 0 r a)⁻¹) *
    (rootGeneratorInGroup 0 r (-a))⁻¹ ∈ splitRadical 0 .suzuki at he
  have hinv : rootGeneratorInGroup 0 r (-a) = (rootGeneratorInGroup 0 r a)⁻¹ :=
    (Subtype.ext (F4Chevalley.rootCurve_inv r a)).symm
  rw [hinv] at he
  simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using he

private theorem seed_rootGenerator_mem_radical_normalizer
    (hpos : ∀ (r s : F4Chevalley.Root) (a b : CoefficientField 0),
      typeF4RootPairing_base.IsPos r → IsRadicalRoot .suzuki s →
      rootGeneratorInGroup 0 r a * rootGeneratorInGroup 0 s b *
        (rootGeneratorInGroup 0 r a)⁻¹ ∈ splitRadical 0 .suzuki)
    (r : F4Chevalley.Root) (a : CoefficientField 0) (hr : IsSeedRoot .suzuki r) :
    rootGeneratorInGroup 0 r a ∈ normalizer (splitRadical 0 .suzuki) := by
  rcases hr with hr | ⟨i, hi, rfl⟩
  · exact positive_rootGenerator_mem_radical_normalizer hpos r a hr
  · have ha : a = 0 ∨ a = 1 := by
      apply eq_zero_or_one_of_sq_eq_self
      simpa using field_pow 0 a
    rcases ha with rfl | rfl
    · have h0 : rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 0 = 1 :=
        Subtype.ext (F4Chevalley.rootCurve_zero _)
      rw [h0]
      exact (normalizer (splitRadical 0 .suzuki : Set (SplitGroup 0))).one_mem
    · let x := rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1
      have hx : x ∈ normalizer (splitRadical 0 .suzuki) :=
        positive_rootGenerator_mem_radical_normalizer hpos _ _
          (typeF4RootPairing_base.isPos_of_mem_support
            (typeF4RootPairing_baseEquiv i).property)
      have hxx : x * x = 1 := by
        apply Subtype.ext
        change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ = 1
        rw [← F4Chevalley.rootCurve_add, CharTwo.add_self_eq_zero,
          F4Chevalley.rootCurve_zero]
      have he : x * weylWord 0 (typeF4SimpleRootIndex i) 1 * x =
          rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 1 := by
        simp only [weylWord, inv_one, CharTwo.neg_eq]
        change x * (x * rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 1 * x) * x = _
        calc
          _ = (x * x) * rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 1 * (x * x) := by group
          _ = _ := by rw [hxx, one_mul, mul_one]
      rw [← he]
      exact (normalizer (splitRadical 0 .suzuki : Set (SplitGroup 0))).mul_mem
        ((normalizer (splitRadical 0 .suzuki : Set (SplitGroup 0))).mul_mem hx
          (weylWord_mem_radical_normalizer hi)) hx

end ReeF4.Parabolics.BinarySuzuki.RootNormalization

namespace ReeF4.Parabolics.BinarySuzuki

/-- The exact generator-conjugation premise needed for relative seed
normality, reduced to positive root-sum matrix identities. Both negative simple
roots are included using their Weyl words and the two binary scalar values.
The root-sum identities remain explicit prerequisites of this conditional theorem. -/
theorem rootGenerator_conj_radical_of_rootSum_exchanges
    (hrootSum : ∀ (r s : F4Chevalley.Root),
      typeF4RootPairing_base.IsPos r → typeF4RootPairing_base.IsPos s → r ≠ s →
      typeF4RootPairing.root r + typeF4RootPairing.root s ∈ Set.range typeF4RootPairing.root →
      ∀ a b : CoefficientField 0, MatrixExchange r s a b)
    (r s : F4Chevalley.Root) (a b : CoefficientField 0)
    (hr : IsSeedRoot .suzuki r) (hs : IsRadicalRoot .suzuki s) :
    rootGeneratorInGroup 0 r a * rootGeneratorInGroup 0 s b *
      (rootGeneratorInGroup 0 r a)⁻¹ ∈ splitRadical 0 .suzuki := by
  have hn := RootNormalization.seed_rootGenerator_mem_radical_normalizer
    (RootNormalization.positive_rootGenerator_conj_radical_of_rootSum_exchanges hrootSum) r a hr
  exact (mem_normalizer_iff.mp hn _).mp (subset_closure ⟨s, b, hs, rfl⟩)

/-- Every binary Suzuki seed-root generator conjugates every radical-root
generator into the specified radical. The equal- and mixed-length matrix
exchanges discharge all positive root-sum cases; Weyl conjugation supplies
the negative simple roots at nodes 1 and 2. -/
theorem rootGenerator_conj_radical
    (r s : F4Chevalley.Root) (a b : CoefficientField 0)
    (hr : IsSeedRoot .suzuki r) (hs : IsRadicalRoot .suzuki s) :
    rootGeneratorInGroup 0 r a * rootGeneratorInGroup 0 s b *
      (rootGeneratorInGroup 0 r a)⁻¹ ∈ splitRadical 0 .suzuki := by
  refine rootGenerator_conj_radical_of_rootSum_exchanges ?_ r s a b hr hs
  intro u v hu hv huv hsum
  by_cases hlen : IsLongRoot u ↔ IsLongRoot v
  · exact matrixExchange_of_equal_length_sum 0 u v hu hv huv hlen hsum
  · exact matrixExchange_of_mixed_length_sum 0 u v hu hv huv hlen hsum

end ReeF4.Parabolics.BinarySuzuki
