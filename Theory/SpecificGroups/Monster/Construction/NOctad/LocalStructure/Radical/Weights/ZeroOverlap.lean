module

public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Radical.Weights.Lines

/-!
# Zero-half-overlap translations and the empty-subset fixed line

Every tetrad in an octad is realized by Golay restriction and has zero
half-overlap. Two tetrads sharing three points sum to any prescribed pair,
and pairs generate the even-subset space. Thus the realized zero-half-overlap
intersections generate all even subsets, already before complementation.

Applying this generation to the actual second-family block actors produces
positive translations between any two class vectors. Applying it to the binary
pairing shows that the restricted first-family characters still separate
complement classes. Their common fixed space is exactly the empty-subset line.
All action statements use only the published `GeneratorLaws`; no conjugation,
full-space fixedness or global radical collection is assumed.

Source: Aschbacher, *Sporadic Groups*, Lemma 30.1, printed pp. 162–163
(PDF p. 87), especially the generation assertion for intersections with
`C(e,c) = 0` and the common fixed-line argument using 29.12.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Even subsets realized by actual Golay words with zero half-overlap. -/
def zeroOverlapSubsets (c : Octad) : Set (EvenSubset c) :=
  {J | ∃ e : golay, golayHalfOverlap e c.val = 0 ∧ c.val.val * e.val = subsetWord c J}

/-- Every four-point subset is a zero-half-overlap Golay intersection. -/
theorem tetrad_mem_zeroOverlapSubsets (c : Octad) (J : EvenSubset c)
    (hJ : hammingNorm (subsetWord c J) = 4) : J ∈ zeroOverlapSubsets c := by
  obtain ⟨e, he⟩ := exists_golay_intersection c J
  refine ⟨e, ?_, he⟩
  rw [golayHalfOverlap_symmetric]
  change ((overlap c.val.val e.val / 2 : ℕ) : ParkerBit) = 0
  have hw : overlap c.val.val e.val = hammingNorm (c.val.val * e.val) := by
    simp only [hammingNorm, overlap, Pi.mul_apply, mul_ne_zero_iff]
  rw [hw, he, hJ]
  decide

private def finsetSubset (c : Octad) (s : Finset (Support c)) (hs : Even s.card) :
    EvenSubset c :=
  ⟨fun i => if i ∈ s then 1 else 0, by
    change (∑ i : Support c, if i ∈ s then (1 : ParkerBit) else 0) = 0
    simpa using (show (s.card : ParkerBit) = 0 from
      (ZMod.natCast_eq_zero_iff _ _).mpr hs.two_dvd)⟩

private theorem norm_finsetSubset (c : Octad) (s : Finset (Support c)) (hs : Even s.card) :
    hammingNorm (subsetWord c (finsetSubset c s hs)) = s.card := by
  have he : subsetWord c (finsetSubset c s hs) = supportWord (s.image Subtype.val) := by
    funext i
    by_cases hi : c.val.val i = 0
    · have hn : i ∉ s.image Subtype.val := by
        rintro him
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp him
        exact j.prop (hj ▸ hi)
      simp [subsetWord, supportWord, hi, hn]
    · have hm : i ∈ s.image Subtype.val ↔ (⟨i, hi⟩ : Support c) ∈ s := by
        constructor
        · rintro him
          obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp him
          exact (show j = ⟨i, hi⟩ from Subtype.ext hji) ▸ hj
        · intro him
          exact Finset.mem_image.mpr ⟨⟨i, hi⟩, him, rfl⟩
      simp [subsetWord, finsetSubset, supportWord, hi, hm]
  rw [he]
  have hw (t : Finset Omega) : hammingNorm (supportWord t) = t.card := by
    simp [hammingNorm, supportWord]
  rw [hw]
  exact Finset.card_image_of_injective s Subtype.val_injective

private def pairSubset (c : Octad) (i j : Support c) : EvenSubset c :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [BinaryPermutation.mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩

private theorem pair_mem_span (c : Octad) (i j : Support c) :
    pairSubset c i j ∈ Submodule.span ParkerBit (zeroOverlapSubsets c) := by
  by_cases hij : i = j
  · subst j
    have he : pairSubset c i i = 0 := by
      apply Subtype.ext
      funext k
      exact CharTwo.add_self_eq_zero _
    rw [he]
    exact Submodule.zero_mem _
  have hc : 3 ≤ (Finset.univ \ {i, j}).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, support_card]
    have hh : ({i, j} : Finset (Support c)).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hc
  have hi : i ∉ s := by
    intro hm
    have hh := (Finset.mem_sdiff.mp (hs hm)).2
    exact hh (by simp)
  have hj : j ∉ s := by
    intro hm
    have hh := (Finset.mem_sdiff.mp (hs hm)).2
    exact hh (by simp)
  have hci : (insert i s).card = 4 := by rw [Finset.card_insert_of_notMem hi, hcard]
  have hcj : (insert j s).card = 4 := by rw [Finset.card_insert_of_notMem hj, hcard]
  let I := finsetSubset c (insert i s) (by rw [hci]; decide)
  let J := finsetSubset c (insert j s) (by rw [hcj]; decide)
  have hI : I ∈ zeroOverlapSubsets c :=
    tetrad_mem_zeroOverlapSubsets c I ((norm_finsetSubset c _ _).trans hci)
  have hJ : J ∈ zeroOverlapSubsets c :=
    tetrad_mem_zeroOverlapSubsets c J ((norm_finsetSubset c _ _).trans hcj)
  have he : I + J = pairSubset c i j := by
    apply Subtype.ext
    funext k
    change (if k ∈ insert i s then (1 : ParkerBit) else 0) +
      (if k ∈ insert j s then 1 else 0) = (Pi.single i (1 : ParkerBit) : Support c → ParkerBit) k +
      (Pi.single j (1 : ParkerBit) : Support c → ParkerBit) k
    by_cases hki : k = i
    · subst k; simp [hi, hij]
    by_cases hkj : k = j
    · subst k; simp [hj, Ne.symm hij]
    by_cases hks : k ∈ s <;> simp [hki, hkj, hks]
  rw [← he]
  exact Submodule.add_mem _ (Submodule.subset_span hI) (Submodule.subset_span hJ)

/-- Realized zero-half-overlap intersections span the full even-subset space. -/
theorem zeroOverlapSubsets_span (c : Octad) :
    Submodule.span ParkerBit (zeroOverlapSubsets c) = ⊤ := by
  apply top_unique
  intro J _
  let a : Support c := Classical.choice inferInstance
  have he : (∑ i : Support c, J.val i • pairSubset c i a) = J := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, pairSubset]
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    have hsum : ∑ i, J.val i = 0 := J.prop
    rw [hsum, zero_smul, add_zero]
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single J.val
  rw [← he]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (pair_mem_span c i a)

/-- Additive generation holds before passing to complement classes. -/
theorem zeroOverlapSubsets_closure (c : Octad) :
    AddSubgroup.closure (zeroOverlapSubsets c) = ⊤ := by
  apply top_unique
  intro J htop
  clear htop
  have hJ : J ∈ Submodule.span ParkerBit (zeroOverlapSubsets c) := by
    rw [zeroOverlapSubsets_span]; trivial
  induction hJ using Submodule.span_induction with
  | mem J hJ => exact AddSubgroup.subset_closure hJ
  | zero => exact AddSubgroup.zero_mem _
  | add I J _ _ hI hJ => exact AddSubgroup.add_mem _ hI hJ
  | smul t J _ ih =>
    rcases bit_cases t with rfl | rfl
    · simp only [zero_smul]; exact AddSubgroup.zero_mem _
    · simpa only [one_smul] using ih

/-- Actual second-family actors with zero half-overlap generate this subgroup. -/
def zeroOverlapSecond (h : GeneratorLaws) (c : Octad) : Subgroup (blockActor c) :=
  Subgroup.closure {g | ∃ e : ParkerLoop, golayHalfOverlap e.1 c.val = 0 ∧
    g = secondActor h e c}

theorem secondActor_mem_zeroOverlapSecond (h : GeneratorLaws) (c : Octad)
    (e : ParkerLoop) (he : golayHalfOverlap e.1 c.val = 0) :
    secondActor h e c ∈ zeroOverlapSecond h c :=
  Subgroup.subset_closure ⟨e, he, rfl⟩

/-- A zero-half-overlap generator translates positively, with no residual sign. -/
theorem blockAction_second_zeroOverlap (h : GeneratorLaws) (c : Octad)
    (e : ParkerLoop) (he : golayHalfOverlap e.1 c.val = 0)
    (J K : EvenSubset c) (hJ : c.val.val * e.1.val = subsetWord c J) :
    blockAction c (secondActor h e c) (blockVector c (subsetClass c K)) =
      blockVector c (subsetClass c (K + J)) := by
  apply Subtype.ext
  change representation _ (vector (parameters c K 0)) = vector (parameters c (K + J) 0)
  refine (h.second e (parameters c K 0)).trans (congrArg vector ?_)
  apply parameters_ext
  · change parkerSign (golayHalfOverlap e.1 c.val) (c.val, 0) = (c.val, 0)
    rw [he, parkerSign_zero]
  · change subsetWord c K + c.val.val * e.1.val = subsetWord c (K + J)
    rw [hJ, subsetWord_add]

/-- Every even-subset translation has an actual, positively acting word in the
zero-half-overlap second-family generators. -/
theorem zeroOverlapSecond_translation (h : GeneratorLaws) (c : Octad) (J : EvenSubset c) :
    ∃ g ∈ zeroOverlapSecond h c, ∀ K : EvenSubset c,
      blockAction c g (blockVector c (subsetClass c K)) =
        blockVector c (subsetClass c (K + J)) := by
  have hJ : J ∈ Submodule.span ParkerBit (zeroOverlapSubsets c) := by
    rw [zeroOverlapSubsets_span]; trivial
  induction hJ using Submodule.span_induction with
  | mem J hJ =>
    obtain ⟨e, he, hJe⟩ := hJ
    exact ⟨secondActor h (e, 0) c, Subgroup.subset_closure ⟨(e, 0), he, rfl⟩,
      fun K => blockAction_second_zeroOverlap h c (e, 0) he J K hJe⟩
  | zero => exact ⟨1, (zeroOverlapSecond h c).one_mem, by intro K; simp⟩
  | add I J _ _ hI hJ =>
    obtain ⟨g, hg, hgv⟩ := hI
    obtain ⟨k, hk, hkv⟩ := hJ
    refine ⟨k * g, (zeroOverlapSecond h c).mul_mem hk hg, ?_⟩
    intro K
    rw [map_mul, Module.End.mul_apply, hgv, hkv, add_assoc]
  | smul t J _ ih =>
    rcases bit_cases t with rfl | rfl
    · exact ⟨1, (zeroOverlapSecond h c).one_mem, by intro K; simp⟩
    · simpa only [one_smul] using ih

/-- Positive transitivity on the literal complement-class vectors, as required
in the coefficient argument of 30.1. -/
theorem zeroOverlapSecond_transitive (h : GeneratorLaws) (c : Octad)
    (a b : SubsetClass c) :
    ∃ g ∈ zeroOverlapSecond h c,
      blockAction c g (blockVector c a) = blockVector c b := by
  refine Quotient.inductionOn₂ a b fun J K => ?_
  obtain ⟨g, hg, hgv⟩ := zeroOverlapSecond_translation h c (J + K)
  refine ⟨g, hg, ?_⟩
  have he : J + (J + K) = K := by
    apply Subtype.ext
    funext i
    change J.val i + (J.val i + K.val i) = K.val i
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  change blockAction c g (blockVector c (subsetClass c J)) = blockVector c (subsetClass c K)
  simpa only [he] using hgv J

private theorem subsetWord_smul (c : Octad) (t : ParkerBit) (J : EvenSubset c) :
    subsetWord c (t • J) = t • subsetWord c J := by
  funext i
  by_cases hi : c.val.val i = 0 <;> simp [subsetWord, hi]

/-- Zero-half-overlap restrictions have the same annihilator as all even subsets. -/
theorem zeroOverlapSubsets_annihilator (c : Octad) (w : BinaryWord) :
    (∀ J ∈ zeroOverlapSubsets c, binaryDot (subsetWord c J) w = 0) ↔
      c.val.val * w = 0 ∨ c.val.val * w = c.val.val := by
  rw [← evenSubset_annihilator]
  constructor
  · intro hw J
    have hJ : J ∈ Submodule.span ParkerBit (zeroOverlapSubsets c) := by
      rw [zeroOverlapSubsets_span]; trivial
    induction hJ using Submodule.span_induction with
    | mem J hJ => exact hw J hJ
    | zero => simp
    | add I J _ _ hI hJ => rw [subsetWord_add, LinearMap.map_add₂, hI, hJ, add_zero]
    | smul t J _ ih => rw [subsetWord_smul, LinearMap.map_smul₂, ih, smul_zero]
  · exact fun hw J _ => hw J

private theorem subsetWord_mul_octad (c : Octad) (J : EvenSubset c) :
    c.val.val * subsetWord c J = subsetWord c J := by
  funext i
  by_cases hi : c.val.val i = 0
  · simp [subsetWord, hi]
  · have hc : c.val.val i = 1 := (bit_cases _).resolve_left hi
    simp [hc]

private theorem subsetWord_dot_intersection (c : Octad) (J : EvenSubset c) (w : BinaryWord) :
    binaryDot (subsetWord c J) (c.val.val * w) = binaryDot (subsetWord c J) w := by
  change (∑ i : Omega, subsetWord c J i * (c.val.val i * w i)) =
    ∑ i : Omega, subsetWord c J i * w i
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : c.val.val i = 0
  · simp [subsetWord, hi]
  · have hc : c.val.val i = 1 := (bit_cases _).resolve_left hi
    simp [hc]

/-- The restricted first-family characters still separate complement classes. -/
theorem firstCharacter_zeroOverlap_separates (c : Octad) (a b : SubsetClass c) :
    (∀ d : ParkerLoop, golayHalfOverlap d.1 c.val = 0 →
      firstCharacter c d a = firstCharacter c d b) ↔ a = b := by
  refine Quotient.inductionOn₂ a b fun J K => ?_
  constructor
  · intro h
    have hz (d : ParkerLoop) (hd : golayHalfOverlap d.1 c.val = 0) :
        binaryDot (subsetWord c (J + K)) d.1.val = 0 := by
      rw [subsetWord_add, LinearMap.map_add₂, ← firstCharacter_mk, ← firstCharacter_mk,
        show firstCharacter c d (subsetClass c J) = firstCharacter c d (subsetClass c K) from
          h d hd, CharTwo.add_self_eq_zero]
    have ha : c.val.val * subsetWord c (J + K) = 0 ∨
        c.val.val * subsetWord c (J + K) = c.val.val := by
      apply (zeroOverlapSubsets_annihilator c _).mp
      rintro L ⟨e, he0, he⟩
      rw [binaryDot_symmetric, ← he, subsetWord_dot_intersection]
      exact hz (e, 0) he0
    rw [subsetWord_mul_octad, subsetWord_add] at ha
    apply (subsetClass_eq c J K).mpr
    rcases ha with he | he
    · left
      apply subsetWord_injective c
      funext i
      have hi := congrFun he i
      exact (eq_neg_of_add_eq_zero_left hi).trans (CharTwo.neg_eq _)
    · right
      apply subsetWord_injective c
      rw [subsetWord_complement]
      calc
        subsetWord c J = (subsetWord c J + subsetWord c K) + subsetWord c K := by
          funext i
          change _ = (_ + _) + subsetWord c K i
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        _ = c.val.val + subsetWord c K := by rw [he]
        _ = _ := add_comm _ _
  · intro he d _
    exact congrArg (firstCharacter c d) he

theorem firstWeight_zeroOverlap_separates (c : Octad) (a b : SubsetClass c) :
    (∀ d : ParkerLoop, golayHalfOverlap d.1 c.val = 0 →
      firstWeight c d a = firstWeight c d b) ↔ a = b := by
  simp_rw [firstWeight_eq_iff]
  exact firstCharacter_zeroOverlap_separates c a b

/-- The empty subset has eigenvalue positive one for exactly the family used here. -/
theorem firstWeight_zeroOverlap_empty (c : Octad) (d : ParkerLoop)
    (hd : golayHalfOverlap d.1 c.val = 0) :
    firstWeight c d (subsetClass c 0) = 1 := by
  simp [firstWeight, golayHalfOverlap_symmetric c.val, hd]

/-- Fixedness under the restricted first family characterizes the empty-subset line. -/
theorem first_zeroOverlap_fixed_iff (h : GeneratorLaws) (c : Octad) (v : block c) :
    (∀ d : ParkerLoop, golayHalfOverlap d.1 c.val = 0 →
      blockAction c (firstActor h d c) v = v) ↔
      v ∈ Submodule.span ℝ {blockVector c (subsetClass c 0)} := by
  constructor
  · intro hv
    have hzero (b : SubsetClass c) (hb : b ≠ subsetClass c 0) :
        (blockBasis c).repr v b = 0 := by
      by_contra hn
      apply hb
      apply (firstWeight_zeroOverlap_separates c b (subsetClass c 0)).mp
      intro d hd
      have he := congrArg (fun w => (blockBasis c).repr w b) (hv d hd)
      rw [blockAction_first_coeff] at he
      rw [firstWeight_zeroOverlap_empty c d hd]
      exact mul_right_cancel₀ hn (he.trans (one_mul _).symm)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨(blockBasis c).repr v (subsetClass c 0), ?_⟩
    apply (blockBasis c).repr.injective
    ext b
    rw [← blockBasis_apply, map_smul, Module.Basis.repr_self]
    by_cases hb : b = subsetClass c 0
    · subst b; simp
    · simp [Ne.symm hb, hzero b hb]
  · intro hv d hd
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, blockAction_first_blockVector, firstWeight_zeroOverlap_empty c d hd, one_smul]

/-- The common fixed space inside the actual octad block. -/
def zeroOverlapFirstFixedSpace (h : GeneratorLaws) (c : Octad) : Submodule ℝ (block c) :=
  ⨅ d : {d : ParkerLoop // golayHalfOverlap d.1 c.val = 0},
    LinearMap.ker (blockAction c (firstActor h d.val c) - LinearMap.id)

theorem zeroOverlapFirstFixedSpace_eq (h : GeneratorLaws) (c : Octad) :
    zeroOverlapFirstFixedSpace h c = Submodule.span ℝ {blockVector c (subsetClass c 0)} := by
  ext v
  simpa only [zeroOverlapFirstFixedSpace, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, Subtype.forall]
    using first_zeroOverlap_fixed_iff h c v

end Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
