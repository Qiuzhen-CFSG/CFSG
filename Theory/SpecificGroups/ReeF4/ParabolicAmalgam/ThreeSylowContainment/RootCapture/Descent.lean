module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.Levi
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.WordExchange.BlockSign
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.NormalizerWords


/-!
# A negative relative block from a nontrivial fixed Weyl element

Factor the inverse normalizer word as a torus element times a fixed simple
Weyl word. A nonidentity Weyl element has a simple descent; exceptional
duality makes both nodes of its orbit descend. The complete middle B₂ block
has the same sign by its two root-sum relations. Conjugating by the relative
reflection reverses the block, so the entire negative fixed block belongs
to the conjugate positive subgroup.

The sign and root-transport lemmas adapt `WordExchange/BlockSign.lean`;
the simple-descent argument adapts `QuotientGeometry/FixedWords.lean`.
The fixedness and torus-factorization inputs are the proved matrix results.
Conjugation is `x ↦ n * x * n⁻¹`, so the descent is taken for `n⁻¹`.

Source: GLS3 2.3.2–8, `refs/KGroup/GLS3/chapter2.tex`, underlying the
Ree case of Aschbacher–Smith Proposition 1.3.4, printed p.511.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.ThreeSylowContainment.RootCapture
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LargeLocalSeeds Binary.FixedGeometry
open Binary.FixedGeometry.BruhatCoverage.FixedWeyl
open LocalBlockInput.PairRigidity LocalBlockInput.PairRigidity.FixedCollection
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open NormalizerGeometry SectionGeometry.BNPair SectionGeometry.BNPair.QuotientGeometry
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
private theorem word_duality (l : List (Fin 4)) (r : F4Chevalley.Root) :
    exceptionalRootPermutation (typeF4RootPairing.weylGroupToPerm (rootWord l) r) =
      typeF4RootPairing.weylGroupToPerm (rootWord (l.map Fin.revPerm))
        (exceptionalRootPermutation r) := by
  simpa only [rootWord, List.map_map, Function.comp_def,
    WordRelations.simplePermutation_numbered] using
      WordRelations.exceptionalRootPermutation_wordProd
        (l.map typeF4RootPairing_baseEquiv) r

private theorem paired_sign {m : ℕ} (l : List (Fin 4))
    (hf : reeTwist m (simpleWord m l) = simpleWord m l) (i : Fin 4) :
    typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm (rootWord l)
      (typeF4SimpleRootIndex (Fin.revPerm i))) ↔
      typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm (rootWord l)
        (typeF4SimpleRootIndex i)) := by
  rw [reeTwist_simpleWord] at hf
  have hw := (simpleWord_eq_iff m _ _).mp hf
  have he := word_duality l (typeF4SimpleRootIndex i)
  rw [hw, exceptionalRootPermutation_simple] at he
  rw [← he]
  exact WordRelations.exceptionalRootPermutation_isPos _

private theorem positive_linear_roots {r : F4Chevalley.Root}
    (hr : IsSimpleBlockRoot .linear true r) :
    r = typeF4SimpleRootIndex 0 ∨ r = typeF4SimpleRootIndex 3 := by
  obtain ⟨i, hi, he | he⟩ := BinaryLinear.isLeviRoot_of_middle_coefficients_zero r
    (hr.1 1 (by simp [leviNodes])) (hr.1 2 (by simp [leviNodes]))
  · have hi' : i = 0 ∨ i = 3 := by simpa [leviNodes] using hi
    rcases hi' with rfl | rfl
    · exact Or.inl he
    · exact Or.inr he
  · have hp := typeF4RootPairing_base.isPos_of_mem_support (typeF4RootPairing_baseEquiv i).property
    have hn := hr.2
    rw [he, RootPairing.Base.IsPos.neg_iff_not] at hn
    exact (hn hp).elim

private theorem positive_block_image (s : Side) (w : typeF4RootPairing.weylGroup)
    (hs : ∀ i ∈ leviNodes s, typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm w (typeF4SimpleRootIndex i)))
    {r : F4Chevalley.Root} (hr : IsSimpleBlockRoot s true r) :
    typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm w r) := by
  cases s with
  | linear =>
    rcases positive_linear_roots hr with rfl | rfl
    · exact hs 0 (by simp [leviNodes])
    · exact hs 3 (by simp [leviNodes])
  | suzuki =>
    have h0 : typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm w (SuzukiChart.roots 0)) :=
      hs 1 (by simp [leviNodes])
    have h1 : typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm w (SuzukiChart.roots 1)) :=
      hs 2 (by simp [leviNodes])
    have ha : typeF4RootPairing.root (SuzukiChart.roots 2) =
        typeF4RootPairing.root (SuzukiChart.roots 0) +
          typeF4RootPairing.root (SuzukiChart.roots 1) := SuzukiChart.root_sum
    have hb : typeF4RootPairing.root (SuzukiChart.roots 3) =
        typeF4RootPairing.root (SuzukiChart.roots 2) +
          typeF4RootPairing.root (SuzukiChart.roots 1) := by
      change (SuzukiChart.roots 3).val = (SuzukiChart.roots 2).val + (SuzukiChart.roots 1).val
      rw [SuzukiChart.roots_val, SuzukiChart.roots_val, SuzukiChart.roots_val]
      ext i; fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
    have hmap {a b c : F4Chevalley.Root}
        (he : typeF4RootPairing.root c = typeF4RootPairing.root a + typeF4RootPairing.root b) :
        typeF4RootPairing.root (typeF4RootPairing.weylGroupToPerm w c) =
          typeF4RootPairing.root (typeF4RootPairing.weylGroupToPerm w a) +
            typeF4RootPairing.root (typeF4RootPairing.weylGroupToPerm w b) := by
      simpa only [smul_add, typeF4RootPairing.weylGroup_apply_root] using
        congrArg (fun z => w • z) he
    have h2 := h0.add h1 (hmap ha)
    have h3 := h2.add h1 (hmap hb)
    obtain ⟨i, rfl⟩ := (SuzukiChart.simpleBlockRoot_iff r).mp hr
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      r.val - (typeF4CorootScale (typeF4SimpleRootIndex i) * dot r.val (typeF4SimpleRoot i)) •
        typeF4SimpleRoot i := by
  change typeF4RootPairing.root _ = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, typeF4RootPairing_pairing]
  rfl

private theorem side_negates_simple (s : Side) (i : Fin 4) (hi : i ∈ leviNodes s) :
    typeF4RootPairing.weylGroupToPerm (rootWord (sideWord s)) (typeF4SimpleRootIndex i) =
      -typeF4SimpleRootIndex i := by
  apply Subtype.ext
  have hn : (-typeF4SimpleRootIndex i).val = -(typeF4SimpleRootIndex i).val := by
    change typeF4RootPairing.root (-typeF4SimpleRootIndex i) = -typeF4RootPairing.root (typeF4SimpleRootIndex i)
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  rw [hn]
  cases s with
  | linear =>
    have hi' : i = 0 ∨ i = 3 := by simpa [leviNodes] using hi
    rcases hi' with rfl | rfl
    all_goals
      change (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0)
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3) _)).val = _
      ext k; fin_cases k <;> norm_num [reflection_val, typeF4CorootScale_simpleRoot,
        typeF4SimpleRootIndex_val, typeF4SimpleRoot, dot, Fin.sum_univ_four, basisVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  | suzuki =>
    have hi' : i = 1 ∨ i = 2 := by simpa [leviNodes] using hi
    rcases hi' with rfl | rfl
    all_goals
      change (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1)
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2)
          (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1)
            (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2) _)))).val = _
      ext k; fin_cases k <;> norm_num [reflection_val, typeF4CorootScale_simpleRoot,
        typeF4SimpleRootIndex_val, typeF4SimpleRoot, dot, Fin.sum_univ_four, basisVector,
        Matrix.cons_val_two, Matrix.cons_val_three]

private theorem exists_descent (w : typeF4RootPairing.weylGroup) (hw : w ≠ 1) :
    ∃ i : Fin 4, ¬ typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm w (typeF4RootPairing_baseEquiv i)) := by
  classical
  obtain ⟨l, hlen, he⟩ := typeF4RootPairing_base.wordLength_spec w
  have hl : l ≠ [] := by
    intro hl
    apply hw
    rw [← he, hl]
    rfl
  let i := l.getLast hl
  obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective i
  refine ⟨j, ?_⟩
  rw [hj]
  have hprod : typeF4RootPairing_base.wordProd l.dropLast *
      typeF4RootPairing_base.simpleReflection i = w := by
    rw [← he, ← List.dropLast_append_getLast hl]
    simp [i]
  have hlength : l.dropLast.length + 1 = typeF4RootPairing_base.wordLength w := by
    simpa [hlen] using congrArg List.length (List.dropLast_append_getLast hl)
  intro hp
  have hup := typeF4RootPairing_base.wordLength_mul_simpleReflection_of_isPos w i hp
  have hlo := typeF4RootPairing_base.wordLength_le
    (w * typeF4RootPairing_base.simpleReflection i) l.dropLast (by
      rw [← hprod]
      simp [mul_assoc])
  omega

private theorem word_conj_root (m : ℕ) (l : List (Fin 4)) (r : F4Chevalley.Root)
    (t : CoefficientField m) :
    simpleWord m l * rootGeneratorInGroup m r t * (simpleWord m l)⁻¹ =
      rootGeneratorInGroup m (typeF4RootPairing.weylGroupToPerm (rootWord l) r) t := by
  induction l with
  | nil => simp [simpleWord, rootWord]
  | cons i l ih =>
    have he : simpleWord m (i :: l) = simpleWord m [i] * simpleWord m l := by
      simp [simpleWord]
    have hs (q : F4Chevalley.Root) :
        simpleWord m [i] * rootGeneratorInGroup m q t * (simpleWord m [i])⁻¹ =
          rootGeneratorInGroup m (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) q) t := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, rootGeneratorInGroup_coe,
        simpleWord_coe, List.map_cons, List.map_nil, WordRelations.titsUnit, typeF4RootPairing_baseEquiv_val] using
        RankOneTransport.simple_conj (typeF4RootPairing_baseEquiv i) q t
    rw [he]
    calc
      _ = simpleWord m [i] *
          (simpleWord m l * rootGeneratorInGroup m r t * (simpleWord m l)⁻¹) *
          (simpleWord m [i])⁻¹ := by group
      _ = _ := by rw [ih, hs]; rfl

private theorem word_conj_block {m : ℕ} (l : List (Fin 4)) (s : Side)
    (hp : ∀ r, IsSimpleBlockRoot s true r → typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord l) r)) {x : SplitGroup m}
    (hx : x ∈ splitSimpleBlock m s true) :
    simpleWord m l * x * (simpleWord m l)⁻¹ ∈ splitUnipotent m := by
  have h : splitSimpleBlock m s true ≤ (splitUnipotent m).comap
      (MulAut.conj (simpleWord m l)).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    change simpleWord m l * rootGeneratorInGroup m r t * (simpleWord m l)⁻¹ ∈ splitUnipotent m
    rw [word_conj_root]
    exact subset_closure ⟨_, t, hp r hr, rfl⟩
  exact h hx

private theorem torus_word_conj_block {m : ℕ} (l : List (Fin 4)) (s : Side)
    (hp : ∀ r, IsSimpleBlockRoot s true r → typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord l) r)) {t x : SplitGroup m}
    (ht : t ∈ splitTorus m) (hx : x ∈ splitSimpleBlock m s true) :
    (t * simpleWord m l) * x * (t * simpleWord m l)⁻¹ ∈ splitUnipotent m := by
  have h := (le_normalizer_iff.mp (splitTorus_normalizes_unipotent m)) t ht _
    (word_conj_block l s hp hx)
  convert h using 1
  group

private theorem negative_side {m : ℕ} (l : List (Fin 4))
    (hf : reeTwist m (simpleWord m l) = simpleWord m l) (hw : rootWord l ≠ 1) :
    ∃ s : Side, ∀ i ∈ leviNodes s, ¬ typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4SimpleRootIndex i)) := by
  obtain ⟨i, hi⟩ := exists_descent (rootWord l) hw
  have hj : ¬ typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4SimpleRootIndex (Fin.revPerm i))) :=
    fun h => hi ((paired_sign l hf i).mp h)
  have hlinear (h0 : ¬ typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4SimpleRootIndex 0)))
      (h3 : ¬ typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4SimpleRootIndex 3))) :
      ∀ j ∈ leviNodes .linear, ¬ typeF4RootPairing_base.IsPos
        (typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4SimpleRootIndex j)) := by
    intro j hj
    have hj' : j = 0 ∨ j = 3 := by simpa [leviNodes] using hj
    rcases hj' with rfl | rfl
    · exact h0
    · exact h3
  have hsuzuki (h1 : ¬ typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4SimpleRootIndex 1)))
      (h2 : ¬ typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4SimpleRootIndex 2))) :
      ∀ j ∈ leviNodes .suzuki, ¬ typeF4RootPairing_base.IsPos
        (typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4SimpleRootIndex j)) := by
    intro j hj
    have hj' : j = 1 ∨ j = 2 := by simpa [leviNodes] using hj
    rcases hj' with rfl | rfl
    · exact h1
    · exact h2
  fin_cases i
  · exact ⟨.linear, hlinear hi hj⟩
  · exact ⟨.suzuki, hsuzuki hi hj⟩
  · exact ⟨.suzuki, hsuzuki hj hi⟩
  · exact ⟨.linear, hlinear hj hi⟩

private theorem positive_after_side {m : ℕ} (l : List (Fin 4))
    (hf : reeTwist m (simpleWord m l) = simpleWord m l) (hw : rootWord l ≠ 1) :
    ∃ s : Side, ∀ r, IsSimpleBlockRoot s true r → typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord (l ++ sideWord s)) r) := by
  obtain ⟨s, hn⟩ := negative_side l hf hw
  refine ⟨s, fun r hr => positive_block_image s (rootWord (l ++ sideWord s)) ?_ hr⟩
  intro i hi
  rw [rootWord_append, map_mul, Equiv.Perm.mul_apply, side_negates_simple s i hi]
  have he : typeF4RootPairing.weylGroupToPerm (rootWord l) (-typeF4SimpleRootIndex i) =
      -(typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4SimpleRootIndex i)) := by
    apply typeF4RootPairing.root.injective
    have hneg (q : F4Chevalley.Root) : typeF4RootPairing.root (-q) = -typeF4RootPairing.root q := by
      simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    rw [hneg, ← typeF4RootPairing.weylGroup_apply_root,
      ← typeF4RootPairing.weylGroup_apply_root, hneg, smul_neg]
  rw [he, RootPairing.Base.IsPos.neg_iff_not]
  exact hn i hi

private theorem reflect_negative_block (m : ℕ) (s : Side) {x : Model m}
    (hx : toSplitGroup m x ∈ splitSimpleBlock m s false) :
    toSplitGroup m (weylLift m s * x * weylLift m s) ∈ splitSimpleBlock m s true := by
  let d := canonicalLocalBlockInput m
  have hc : splitSimpleBlock m s false ≤ (splitSimpleBlock m s true).comap
      (MulAut.conj (relativeWeyl d s).val).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    change (relativeWeyl d s).val * rootGeneratorInGroup m r t *
      (relativeWeyl d s).val⁻¹ ∈ splitSimpleBlock m s true
    rw [relativeWeyl_conj_block_root d s false r t hr]
    exact subset_closure ⟨_, t, (isSimpleBlockRoot_neg_iff s false r).mpr hr, rfl⟩
  have hv : (weylLift m s)⁻¹ = weylLift m s :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using weylLift_sq m s)
  have he : (relativeWeyl d s).val = toSplitGroup m (weylLift m s) := by
    rw [relativeWeyl_val, toSplitGroup_weylLift]
  have h := hc hx
  change (relativeWeyl d s).val * toSplitGroup m x * (relativeWeyl d s).val⁻¹ ∈ splitSimpleBlock m s true at h
  simpa only [he, ← map_inv, hv, ← map_mul] using h

/-- Every non-Borel normalizer word captures one entire negative simple
relative block in its conjugate positive subgroup. -/
theorem exists_negativeBlock_le_conjugate (m : ℕ) {n : Model m}
    (hn : n ∈ normalizerWords m) (hnb : n ∉ borel m) :
    ∃ s : Side, (splitSimpleBlock m s false).comap (toSplitGroup m) ≤
      (unipotent m).map (MulAut.conj n).toMonoidHom := by
  obtain ⟨t, ht, l, he⟩ := exists_torus_mul_simpleWord m
    (fun _ h => Overlap.normalizerWords_weylMonomial (splitTorus_eq_diagonalTorus m) h)
    (fun _ h htri => Overlap.normalizerWord_mem_diagonalTorus_of_heightTriangular
      (splitTorus_eq_diagonalTorus m) h htri)
    (show toSplitGroup m (n⁻¹) ∈ splitNormalizerWords m from (normalizerWords m).inv_mem hn)
  have hf := simpleWord_fixed_of_torus_mul m ht he
  have hw : rootWord l ≠ 1 := by
    intro hw
    have hl : simpleWord m l = 1 := by
      change simpleWord m l = simpleWord m []
      apply (simpleWord_eq_iff m _ _).mpr
      simpa [rootWord] using hw
    have hninv : n⁻¹ ∈ borel m := by
      change toSplitGroup m (n⁻¹) ∈ splitBorel m
      rw [he, hl, mul_one]
      exact (show splitTorus m ≤ splitBorel m from le_sup_right) ht
    exact hnb ((borel m).inv_mem_iff.mp hninv)
  obtain ⟨s, hp⟩ := positive_after_side l hf hw
  refine ⟨s, ?_⟩
  intro x hx
  refine ⟨n⁻¹ * x * n, ?_, ?_⟩
  · have hv : (weylLift m s)⁻¹ = weylLift m s :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using weylLift_sq m s)
    have heq : n⁻¹ * x * n =
        (n⁻¹ * weylLift m s) * (weylLift m s * x * weylLift m s) *
          (n⁻¹ * weylLift m s)⁻¹ := by
      have hww : weylLift m s * weylLift m s = 1 := by
        simpa only [pow_two] using weylLift_sq m s
      have hwleft (y : Model m) : weylLift m s * (weylLift m s * y) = y := by
        rw [← mul_assoc, hww, one_mul]
      rw [mul_inv_rev, inv_inv, hv]
      simp only [mul_assoc, hwleft]
    change toSplitGroup m (n⁻¹ * x * n) ∈ splitUnipotent m
    rw [heq, map_mul, map_mul, map_inv, map_mul, he, toSplitGroup_weylLift,
      mul_assoc t, ← simpleWord_append]
    exact torus_word_conj_block (l ++ sideWord s) s hp ht (reflect_negative_block m s hx)
  · change n * (n⁻¹ * x * n) * n⁻¹ = x
    group

end ReeF4.Parabolics.ThreeSylowContainment.RootCapture
