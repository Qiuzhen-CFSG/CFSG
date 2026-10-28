module

public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.Roots
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.Basic
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.Opposition
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.Orbits

/-!
# Weyl support of the central Ree root curve

The two split roots in `centralWord m 4 t` are the highest long root and
its short partner. The two actual relative Weyl lifts permute eight pairs:
the top pairs of the four positive B₂ blocks and their negatives. The
coordinate identities below prove this permutation on the actual F₄ roots;
Chevalley word conjugation transports both parameters without alteration.
Every positive pair lies in the linear radical. Every negative pair lies
in its opposite. The established graded-matrix opposition theorem therefore
puts a Weyl conjugate contained in the full linear parabolic in its radical.

This is the root calculation for Aschbacher--Smith E.1.14(1), printed p.214
of `refs/quasithin.pdf`, citing Aschbacher (1982), Lemma 4.7
(DOI 10.2307/2374202). Root conventions are GLS3 Table 2.4 and 2.4.5(d),
`refs/KGroup/GLS3/chapter2.tex`. The proof works also at the binary endpoint;
the later Borel-center reduction uses the positive-parameter hypothesis.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction.LinearRootOrbit
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations ReeF4.Parabolics.Binary.FixedGeometry
open ReeF4.LocalBlockInput.PairRigidity.FixedCollection
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def positivePair (i : Fin 4) (k : Fin 2) : F4Chevalley.Root :=
  if k = 0 then highRoot ⟨2 * i.val, by omega⟩ else mixedRoot ⟨2 * i.val, by omega⟩

private def pair (i : Fin 8) (k : Fin 2) : F4Chevalley.Root :=
  if h : i.val < 4 then positivePair ⟨i.val, h⟩ k
  else -positivePair ⟨i.val - 4, by omega⟩ k

private def pairVector : Fin 4 → Fin 2 → Vec 4 :=
  ![![![0,0,1,1], ![0,0,1,0]],
    ![![1,0,1,0], ![1/2,1/2,1/2,1/2]],
    ![![1,1,0,0], ![1,0,0,0]],
    ![![1,0,-1,0], ![1/2,1/2,-1/2,-1/2]]]

private def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 2, v 1, v 3]
  | 1, v => ![v 0, v 1, v 3, v 2]
  | 2, v => ![v 0, v 1, v 2, -v 3]
  | 3, v => ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectedVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> ring

private def longVector : Fin 4 → Vec 4 :=
  ![![0,0,1,-1], ![0,1,0,1], ![1,-1,0,0], ![0,1,0,-1]]
private def shortVector : Fin 4 → Vec 4 :=
  ![![0,0,0,1], ![1/2,-1/2,1/2,-1/2], ![0,1,0,0], ![1/2,-1/2,-1/2,1/2]]

private theorem long_val (i : Fin 4) :
    (longRoot ⟨2 * i.val, by omega⟩).val = longVector i := by
  rw [longRoot_eq_sum]
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [longVector, longRootCoefficients, Fin.sum_univ_four, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three]

private theorem short_val (i : Fin 4) :
    (shortRoot ⟨2 * i.val, by omega⟩).val = shortVector i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [shortVector, longRoot, shortRoot, relativeRotation, middleReflection,
      endReflection, Equiv.Perm.mul_apply, pow_succ,
      WordRelations.exceptionalRootPermutation_simple_reflection,
      exceptionalRootPermutation_simple, Fin.revPerm, Fin.rev,
      reflection_val, reflectedVector, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three]

private theorem positivePair_val (i : Fin 4) (k : Fin 2) :
    (positivePair i k).val = pairVector i k := by
  have he : (2 * i.val : ℕ) % 2 = 0 := by omega
  fin_cases k
  · change (highRoot ⟨2 * i.val, by omega⟩).val = _
    rw [highRoot_eq_add_two _ he, long_val, short_val]
    fin_cases i <;> ext j <;> fin_cases j <;>
      norm_num [pairVector, longVector, shortVector, Matrix.cons_val_two, Matrix.cons_val_three]
  · change (mixedRoot ⟨2 * i.val, by omega⟩).val = _
    rw [mixedRoot_eq_add _ he, long_val, short_val]
    fin_cases i <;> ext j <;> fin_cases j <;>
      norm_num [pairVector, longVector, shortVector, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem root_neg_val (r : F4Chevalley.Root) : (-r).val = -r.val := by
  change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
  simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self]

private theorem pair_val (i : Fin 8) (k : Fin 2) :
    (pair i k).val = if h : i.val < 4 then pairVector ⟨i.val, h⟩ k
      else -pairVector ⟨i.val - 4, by omega⟩ k := by
  unfold pair
  split_ifs
  · exact positivePair_val _ _
  · rw [root_neg_val, positivePair_val]

private def next : Side → Fin 8 → Fin 8
  | .suzuki => ![4,3,2,1,0,7,6,5]
  | .linear => ![3,2,1,0,7,6,5,4]

private theorem pair_reflection (s : Side) (i : Fin 8) (k : Fin 2) :
    wordAction (sideWord s) (pair i k) = pair (next s i) k := by
  apply Subtype.ext
  cases s <;>
    simp only [wordAction, sideWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, reflection_val, pair_val]
  all_goals
    fin_cases i <;> fin_cases k <;> ext j <;> fin_cases j <;>
      norm_num [next, pairVector, reflectedVector, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem positivePair_radical (i : Fin 4) (k : Fin 2) :
    IsRadicalRoot .linear (positivePair i k) := by
  have he : (2 * i.val : ℕ) % 2 = 0 := by omega
  have hmix := (longRoot_pos ⟨2 * i.val, by omega⟩).add
    (shortRoot_pos _) (mixedRoot_eq_add _ he)
  refine ⟨?_, 1, by simp [leviNodes], ?_⟩
  · unfold positivePair
    split_ifs
    · apply hmix.add (shortRoot_pos _)
      change (highRoot _).val = (mixedRoot _).val + (shortRoot _).val
      rw [highRoot_eq_add_two _ he, mixedRoot_eq_add _ he, two_smul]
      abel
    · exact hmix
  · rw [positivePair_val]
    fin_cases i <;> fin_cases k <;>
      norm_num [pairVector, typeF4SimpleCoefficient, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem weyl_pair (m : ℕ) (w : Model m) (hw : w ∈ weylSubgroup m) :
    ∀ i : Fin 8, ∃ j : Fin 8, ∀ (k : Fin 2) (t : CoefficientField m),
      toSplitGroup m w * rootGeneratorInGroup m (pair i k) t * (toSplitGroup m w)⁻¹ =
        rootGeneratorInGroup m (pair j k) t := by
  have hs (s : Side) (i : Fin 8) : ∃ j : Fin 8, ∀ (k : Fin 2) (t : CoefficientField m),
      toSplitGroup m (weylLift m s) * rootGeneratorInGroup m (pair i k) t *
          (toSplitGroup m (weylLift m s))⁻¹ = rootGeneratorInGroup m (pair j k) t := by
    refine ⟨next s i, ?_⟩
    intro k t
    rw [toSplitGroup_weylLift, simpleWord_conj_root, pair_reflection]
  change w ∈ closure (Set.range (weylLift m)) at hw
  induction hw using Subgroup.closure_induction'' with
  | mem x hx => obtain ⟨s, rfl⟩ := hx; exact hs s
  | inv_mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    have hinv : (weylLift m s)⁻¹ = weylLift m s :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using
        SectionGeometry.BNPair.weylLift_sq m s)
    rw [hinv]
    exact hs s
  | one => intro i; exact ⟨i, by intro k t; simp⟩
  | mul x y _ _ hx hy =>
    intro i
    obtain ⟨j, hj⟩ := hy i
    obtain ⟨l, hl⟩ := hx j
    refine ⟨l, ?_⟩
    intro k t
    rw [map_mul]
    calc
      _ = toSplitGroup m x *
          (toSplitGroup m y * rootGeneratorInGroup m (pair i k) t * (toSplitGroup m y)⁻¹) *
          (toSplitGroup m x)⁻¹ := by group
      _ = _ := by rw [hj, hl]

private def pairWord (m : ℕ) (i : Fin 8) (a b : CoefficientField m) : SplitGroup m :=
  rootGeneratorInGroup m (pair i 0) a * rootGeneratorInGroup m (pair i 1) b

private theorem pairWord_positive (m : ℕ) (i : Fin 8) (hi : i.val < 4)
    (a b : CoefficientField m) : pairWord m i a b ∈ splitRadical m .linear := by
  apply mul_mem <;> apply Subgroup.subset_closure
  · exact ⟨positivePair ⟨i.val, hi⟩ 0, a, positivePair_radical _ _, by simp [pair, hi]⟩
  · exact ⟨positivePair ⟨i.val, hi⟩ 1, b, positivePair_radical _ _, by simp [pair, hi]⟩

private theorem pairWord_negative (m : ℕ) (i : Fin 8) (hi : ¬ i.val < 4)
    (a b : CoefficientField m) :
    LocalBlockInput.PairNormalization.splitOpposition m * pairWord m i a b *
      (LocalBlockInput.PairNormalization.splitOpposition m)⁻¹ ∈ splitRadical m .linear := by
  have he : LocalBlockInput.PairNormalization.splitOpposition m * pairWord m i a b *
      (LocalBlockInput.PairNormalization.splitOpposition m)⁻¹ =
      rootGeneratorInGroup m (positivePair ⟨i.val - 4, by omega⟩ 0) a *
      rootGeneratorInGroup m (positivePair ⟨i.val - 4, by omega⟩ 1) b := by
    unfold pairWord
    rw [show ∀ (g x y : SplitGroup m), g * (x * y) * g⁻¹ =
      (g * x * g⁻¹) * (g * y * g⁻¹) by intros; group]
    simp only [LocalBlockInput.PairNormalization.splitOpposition_conj_root,
      pair, dif_neg hi, neg_neg]
  rw [he]
  apply mul_mem <;> apply Subgroup.subset_closure
  · exact ⟨_, a, positivePair_radical _ _, rfl⟩
  · exact ⟨_, b, positivePair_radical _ _, rfl⟩

/-- The actual Weyl conjugates of the central root curve have either positive
or negative linear-radical support, uniformly for the whole parameter curve. -/
theorem weyl_conjugate_radical_or_opposite (m : ℕ) (w : Model m)
    (hw : w ∈ weylSubgroup m) :
    (EvenInvolutionGeometry.longRootGroup m).map (MulAut.conj w).toMonoidHom ≤
        radical m .linear ∨
    (EvenInvolutionGeometry.longRootGroup m).map (MulAut.conj w).toMonoidHom ≤
      (radical m .linear).comap
        (MulAut.conj (SectionGeometry.Opposition.linearOpposition m)).toMonoidHom := by
  obtain ⟨i, hi⟩ := weyl_pair m w hw 2
  have hword (t : CoefficientField m) :
      toSplitGroup m w * centralWord m 4 t * (toSplitGroup m w)⁻¹ =
        pairWord m i t (rootFieldEnd m (longRoot 4) t) := by
    have h0 := hi 0 t
    have h1 := hi 1 (rootFieldEnd m (longRoot 4) t)
    change toSplitGroup m w * rootGeneratorInGroup m (highRoot 4) t *
      (toSplitGroup m w)⁻¹ = _ at h0
    change toSplitGroup m w * rootGeneratorInGroup m (mixedRoot 4)
      (rootFieldEnd m (longRoot 4) t) * (toSplitGroup m w)⁻¹ = _ at h1
    unfold centralWord pairWord
    rw [← h0, ← h1]
    group
  by_cases hp : i.val < 4
  · left
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := (EvenInvolutionGeometry.mem_longRootGroup m y).mp hy
    change toSplitGroup m (w * EvenInvolutionGeometry.longRootElement m t * w⁻¹) ∈ splitRadical m .linear
    rw [map_mul, map_mul, map_inv, EvenInvolutionGeometry.longRootElement_coe, hword]
    exact pairWord_positive m i hp _ _
  · right
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := (EvenInvolutionGeometry.mem_longRootGroup m y).mp hy
    change toSplitGroup m (SectionGeometry.Opposition.linearOpposition m *
      (w * EvenInvolutionGeometry.longRootElement m t * w⁻¹) *
      (SectionGeometry.Opposition.linearOpposition m)⁻¹) ∈ splitRadical m .linear
    simp only [map_mul, map_inv, SectionGeometry.Opposition.toSplitGroup_linearOpposition,
      EvenInvolutionGeometry.longRootElement_coe, hword]
    exact pairWord_negative m i hp _ _

/-- A Weyl conjugate contained in the full linear parabolic is in its radical.
The opposite case is eliminated by the proved graded-matrix intersection. -/
theorem weyl_conjugate_le_linear_radical (m : ℕ) (w : Model m)
    (hw : w ∈ weylSubgroup m)
    (hP : (EvenInvolutionGeometry.longRootGroup m).map (MulAut.conj w).toMonoidHom ≤
      parabolic m .linear) :
    (EvenInvolutionGeometry.longRootGroup m).map (MulAut.conj w).toMonoidHom ≤
      radical m .linear := by
  rcases weyl_conjugate_radical_or_opposite m w hw with h | h
  · exact h
  · intro x hx
    have hopinv : (SectionGeometry.Opposition.linearOpposition m)⁻¹ =
        SectionGeometry.Opposition.linearOpposition m := by
      apply toSplitGroup_injective m
      rw [map_inv, SectionGeometry.Opposition.toSplitGroup_linearOpposition,
        LocalBlockInput.PairNormalization.splitOpposition_inv]
    have he := Subgroup.disjoint_def.mp
      (SectionGeometry.Opposition.linear_radical_disjoint_opposite_parabolic m) (h hx)
      (show (MulAut.conj (SectionGeometry.Opposition.linearOpposition m)) x ∈
        (parabolic m .linear).comap
          (MulAut.conj (SectionGeometry.Opposition.linearOpposition m)).toMonoidHom by
        change (MulAut.conj (SectionGeometry.Opposition.linearOpposition m))
          ((MulAut.conj (SectionGeometry.Opposition.linearOpposition m)) x) ∈ parabolic m .linear
        have he (g : Model m) (hg : g⁻¹ = g) :
            (MulAut.conj g) ((MulAut.conj g) x) = x := by
          calc
            _ = g * (g * x * g⁻¹) * g⁻¹ := rfl
            _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hg]
            _ = x := by group
        rw [he _ hopinv]
        exact hP hx)
    have hx1 : x = 1 := (MulAut.conj (SectionGeometry.Opposition.linearOpposition m)).injective
      (he.trans (map_one _).symm)
    rw [hx1]
    exact one_mem _

end CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction.LinearRootOrbit
