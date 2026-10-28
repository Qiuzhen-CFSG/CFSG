module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.WordExchange.RootFactors
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientGeometry.Factorization
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates.SplitBlock

/-!
# Uniform signs of complete relative root blocks

A fixed simple Weyl word commutes with exceptional duality, so the two simple
roots in either node orbit have the same image sign. The root sums in the
middle B₂ subsystem extend that sign to all four positive roots. Multiplying
by the relative reflection reverses the signs when necessary.

The two specified normalizer matrix facts factor an inverse normalizer word
as a torus element times a fixed simple Weyl word. Exact root conjugation and
torus normalization then put one entire signed relative block in the positive
unipotent subgroup. All conjugations use the actual fixed matrices; no quotient
normality or Tits-system assumption is involved.

Source: GLS3 2.3.2–8 and §2.4, Table 2.4 types V and VI,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LargeLocalSeeds Parabolics Parabolics.Binary.FixedGeometry
open Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl
open LocalBlockInput.PairRigidity LocalBlockInput.PairRigidity.FixedCollection
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open NormalizerGeometry QuotientGeometry
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

private theorem fixed_word_block_sign {m : ℕ} (l : List (Fin 4))
    (hf : reeTwist m (simpleWord m l) = simpleWord m l) (s : Side) :
    (∀ r, IsSimpleBlockRoot s true r → typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord l) r)) ∨
    (∀ r, IsSimpleBlockRoot s true r → typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord (l ++ sideWord s)) r)) := by
  have hs : (∀ i ∈ leviNodes s, typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4SimpleRootIndex i))) ∨
      (∀ i ∈ leviNodes s, ¬ typeF4RootPairing_base.IsPos
        (typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4SimpleRootIndex i))) := by
    cases s with
    | linear =>
      have hp := paired_sign l hf 0
      by_cases h : typeF4RootPairing_base.IsPos
          (typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4SimpleRootIndex 0))
      · left; intro i hi
        have hi' : i = 0 ∨ i = 3 := by simpa [leviNodes] using hi
        rcases hi' with rfl | rfl
        · exact h
        · exact hp.mpr h
      · right; intro i hi
        have hi' : i = 0 ∨ i = 3 := by simpa [leviNodes] using hi
        rcases hi' with rfl | rfl
        · exact h
        · exact fun hn => h (hp.mp hn)
    | suzuki =>
      have hp := paired_sign l hf 1
      by_cases h : typeF4RootPairing_base.IsPos
          (typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4SimpleRootIndex 1))
      · left; intro i hi
        have hi' : i = 1 ∨ i = 2 := by simpa [leviNodes] using hi
        rcases hi' with rfl | rfl
        · exact h
        · exact hp.mpr h
      · right; intro i hi
        have hi' : i = 1 ∨ i = 2 := by simpa [leviNodes] using hi
        rcases hi' with rfl | rfl
        · exact h
        · exact fun hn => h (hp.mp hn)
  rcases hs with hp | hn
  · exact Or.inl (fun r hr => positive_block_image s (rootWord l) hp hr)
  · right
    apply fun r hr => positive_block_image s (rootWord (l ++ sideWord s)) ?_ hr
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

/-- The permitted matrix facts give a uniform sign for each entire simple block. -/
theorem relativeBlockSign_of_monomial (m : ℕ)
    (hweyl : ∀ n ∈ splitNormalizerWords m,
      ∃ (w : typeF4RootPairing.weylGroup) (c : F4Chevalley.Root → (CoefficientField m)ˣ),
        RootMonomial n.val.val (typeF4RootPairing.weylGroupToPerm w) c)
    (hkernel : ∀ n ∈ splitNormalizerWords m,
      Overlap.IsHeightTriangular n → n ∈ diagonalTorus m) : RelativeBlockSign m := by
  intro s n hn
  obtain ⟨t, ht, l, he⟩ := exists_torus_mul_simpleWord m hweyl hkernel
    (show toSplitGroup m (n⁻¹) ∈ splitNormalizerWords m from (normalizerWords m).inv_mem hn)
  have hf := simpleWord_fixed_of_torus_mul m ht he
  rcases fixed_word_block_sign l hf s with hp | hp
  · left
    intro x hx
    apply unipotent_le_borel m
    change toSplitGroup m (n⁻¹ * x * n) ∈ splitUnipotent m
    rw [map_mul, map_mul,
      show toSplitGroup m n = (toSplitGroup m (n⁻¹))⁻¹ by simp, he]
    exact torus_word_conj_block l s hp ht hx
  · right
    intro x hx
    apply unipotent_le_borel m
    have hv : (weylLift m s)⁻¹ = weylLift m s :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using weylLift_sq m s)
    have heq : n⁻¹ * (weylLift m s * x * weylLift m s) * n =
        (n⁻¹ * weylLift m s) * x * (n⁻¹ * weylLift m s)⁻¹ := by
      rw [mul_inv_rev, inv_inv, hv]
      group
    rw [heq]
    change toSplitGroup m ((n⁻¹ * weylLift m s) * x * (n⁻¹ * weylLift m s)⁻¹) ∈
      splitUnipotent m
    rw [map_mul, map_mul, map_inv, map_mul, he, toSplitGroup_weylLift,
      mul_assoc t, ← simpleWord_append]
    exact torus_word_conj_block (l ++ sideWord s) s hp ht hx

end ReeF4.SectionGeometry.BNPair
