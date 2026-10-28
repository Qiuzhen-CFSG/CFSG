module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.RelativeRootFiberQuotient
public import Theory.GroupTheory.FilteredCollection
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicCoordinateHom
public import Theory.AlgebraicGroup.Tori.Basic

universe u

set_option linter.style.haveILetI false

/-!
Exact-height coordinates on adjacent relative-root layers attached directly to
`RelativeRootRepresentationSource`.

For a source `S`, this module proves that the positive adjacent quotient
`relativeRootLayerQuotient S` is commutative and identifies it
multiplicatively with the product of additive `k`-coordinates indexed by the
absolute roots of relative height `S.height`.  The coordinate homomorphism
sends a single coordinate to the corresponding Chevalley root class; its
inverse therefore sends every such class to `Pi.single`.

The proof uses only the fields recorded by the representation source in
`theorem_1_14_6`: its rational root pairing and base, root realization,
simple-root expansion, finite root set, and Chevalley system.  Filtered
Chevalley collection raises relative height on every commutator correction.
For injectivity, a kernel relation is collected at exact height and conjugated
by pairs of coroot elements.  The nonzero Cartan determinant separates
distinct roots, including in positive characteristic by evaluating a suitable
unit, so induction on finite support forces every parameter to be zero.
Surjectivity is the complementary closure induction: exact-height root
generators are single-coordinate images and all higher-height generators die
in the adjacent quotient.

For geometric consumers, the collected-word argument is also exported as a
fixed finite product parametrization of each positive source layer.  Its root
factors are the stored Chevalley elements, so the corresponding regular map can
be built from the source's one-parameter parametrizations.

This is the source-coordinate input for the relative-root representation
construction following the GLS3 development.  It does not pass through
`ParabolicRelativeRootSetup`, whose additional integral and standard-parabolic
fields are absent from `RelativeRootRepresentationSource`, and it does not use
`theorem_1_13_5` or `theorem_1_14_7`.
-/

namespace Theory.AlgebraicGroup

open scoped BigOperators IsMulCommutative

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The relative height used by the source-layer filtration. -/
@[expose]
public noncomputable def relativeRootSourceHeight
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (alpha : S.D.Root) : Int :=
  RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J alpha

private def SourceExactHeightRoot
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) :=
  {alpha : S.D.Root // relativeRootSourceHeight S alpha = n}

omit [IsAlgClosed k] in
private theorem source_base_support
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    S.base.support = S.D.simple.toFinite.toFinset := by
  letI := Fintype.ofFinite S.D.Root
  ext alpha
  simp only [Set.Finite.mem_toFinset]
  exact (S.rootSystemRealization.2.2.2.1 alpha).symm

omit [IsAlgClosed k] in
private lemma source_height_eq_base
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (alpha : S.D.Root) :
    relativeRootSourceHeight S alpha =
      RelativeRootHeight S.coeff S.base.support S.J alpha := by
  unfold relativeRootSourceHeight
  rw [← source_base_support S]

omit [IsAlgClosed k] in
private lemma source_positive_roots_linearlyIndependent
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) {alpha beta : S.D.Root}
    (halpha : 0 < relativeRootSourceHeight S alpha)
    (hbeta : 0 < relativeRootSourceHeight S beta) (hne : alpha ≠ beta) :
    AreLinearlyIndependentRoots S.D S.pairing (Equiv.refl S.D.Root) alpha beta := by
  letI := Fintype.ofFinite S.D.Root
  let P := S.pairing
  let _ := P.indexNeg
  have halphaPos : S.base.IsPos alpha :=
    base_isPos_of_relativeRootHeight_pos P S.base S.J S.coeff
      S.simpleRootExpansion (by simpa [source_height_eq_base S alpha] using halpha)
  have hbetaPos : S.base.IsPos beta :=
    base_isPos_of_relativeRootHeight_pos P S.base S.J S.coeff
      S.simpleRootExpansion (by simpa [source_height_eq_base S beta] using hbeta)
  have hnotopp : P.root alpha ≠ -P.root beta := by
    intro hneg
    have hidx : alpha = P.reflectionPerm beta beta := P.root_eq_neg_iff.mp hneg
    have halphaNeg : S.base.IsPos (-beta) := by
      simpa [hidx] using halphaPos
    exact ((RootPairing.Base.IsPos.neg_iff_not
      (P := P) (b := S.base) (i := beta)).mp halphaNeg) hbetaPos
  have hlin : LinearIndependent ℚ ![P.root alpha, P.root beta] :=
    RootPairing.IsReduced.linearIndependent (P := P) hne hnotopp
  rw [LinearIndependent.pair_iff] at hlin
  simpa [AreLinearlyIndependentRoots] using hlin

private noncomputable def sourceDegree
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (alpha : S.D.Root) : Nat :=
  (relativeRootSourceHeight S alpha).toNat

omit [IsAlgClosed k] in
private lemma source_validTerm_positive_and_degree_gt
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) {alpha beta : S.D.Root}
    (halpha : 0 < relativeRootSourceHeight S alpha)
    (hbeta : 0 < relativeRootSourceHeight S beta)
    (q : ChevalleyCommutatorTerm S.D.Root)
    (hq : IsValidChevalleyCommutatorTerm S.D S.pairing (Equiv.refl S.D.Root)
      alpha beta q) :
    0 < relativeRootSourceHeight S q.root ∧
      max (sourceDegree S alpha) (sourceDegree S beta) < sourceDegree S q.root := by
  letI := Fintype.ofFinite S.D.Root
  have hheight := relativeRootHeight_of_validChevalleyCommutatorTerm
    S.D S.pairing (Equiv.refl S.D.Root) S.base S.J S.coeff
      S.simpleRootExpansion q hq
  simp only [Equiv.refl_apply] at hheight
  rw [← source_height_eq_base S q.root,
    ← source_height_eq_base S alpha, ← source_height_eq_base S beta] at hheight
  have hqi : (1 : Int) ≤ q.i := by exact_mod_cast Nat.succ_le_iff.mp hq.1
  have hqj : (1 : Int) ≤ q.j := by exact_mod_cast Nat.succ_le_iff.mp hq.2.1
  have hqalpha : relativeRootSourceHeight S alpha < relativeRootSourceHeight S q.root := by
    rw [hheight]
    nlinarith
  have hqbeta : relativeRootSourceHeight S beta < relativeRootSourceHeight S q.root := by
    rw [hheight]
    nlinarith
  have hqpos : 0 < relativeRootSourceHeight S q.root := lt_trans halpha hqalpha
  exact (And.intro hqpos
    (max_lt ((Int.toNat_lt_toNat hqpos).mpr hqalpha)
      ((Int.toNat_lt_toNat hqpos).mpr hqbeta)))

/-- Source roots whose relative height is at least `n`. -/
public abbrev RelativeRootSourceAtLeastIndex
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) :=
  {alpha : S.D.Root // (n : Int) ≤ relativeRootSourceHeight S alpha}

/-- A fixed list containing every source root of height at least `n`. -/
public noncomputable def sourceRelativeRootAtLeastList
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) :
    List (RelativeRootSourceAtLeastIndex S n) := by
  letI : Finite (RelativeRootSourceAtLeastIndex S n) := by
    unfold RelativeRootSourceAtLeastIndex
    infer_instance
  letI := Fintype.ofFinite (RelativeRootSourceAtLeastIndex S n)
  classical
  exact Finset.univ.toList

omit [IsAlgClosed k] in
/-- Every source root of height at least `n` occurs in the fixed list. -/
public lemma sourceRelativeRootAtLeastList_mem
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat)
    (alpha : RelativeRootSourceAtLeastIndex S n) :
    alpha ∈ sourceRelativeRootAtLeastList S n := by
  letI : Finite (RelativeRootSourceAtLeastIndex S n) := by
    unfold RelativeRootSourceAtLeastIndex
    infer_instance
  letI := Fintype.ofFinite (RelativeRootSourceAtLeastIndex S n)
  classical
  simp [sourceRelativeRootAtLeastList]

omit [IsAlgClosed k] in
/-- The fixed source root list has no repetitions. -/
public lemma sourceRelativeRootAtLeastList_nodup
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) :
    (sourceRelativeRootAtLeastList S n).Nodup := by
  letI : Finite (RelativeRootSourceAtLeastIndex S n) := by
    unfold RelativeRootSourceAtLeastIndex
    infer_instance
  letI := Fintype.ofFinite (RelativeRootSourceAtLeastIndex S n)
  classical
  exact Finset.nodup_toList _

private noncomputable def sourceMaxDegree
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) : Nat := by
  letI := Fintype.ofFinite S.D.Root
  classical
  exact Finset.univ.sup (sourceDegree S)

omit [IsAlgClosed k] in
private lemma sourceDegree_le_max
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (alpha : S.D.Root) :
    sourceDegree S alpha ≤ sourceMaxDegree S := by
  letI := Fintype.ofFinite S.D.Root
  classical
  exact Finset.le_sup (f := sourceDegree S) (Finset.mem_univ alpha)

omit [IsAlgClosed k] in
private theorem sourceRelativeRootAtLeast_exchange
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) (hn : 0 < n)
    (alpha beta : RelativeRootSourceAtLeastIndex S n)
    (a b : k) (hne : alpha ≠ beta) :
    ∃ correction : List (RelativeRootSourceAtLeastIndex S n × k),
      (∀ z ∈ correction,
        z.1 ∈ sourceRelativeRootAtLeastList S n ∧
          max (sourceDegree S alpha.1) (sourceDegree S beta.1) <
            sourceDegree S z.1.1) ∧
      S.C.x alpha.1 a * S.C.x beta.1 b =
        S.C.x beta.1 b * S.C.x alpha.1 a *
          FilteredCollection.wordProduct (fun gamma => S.C.x gamma.1)
            correction := by
  letI := Fintype.ofFinite S.D.Root
  have halpha : 0 < relativeRootSourceHeight S alpha.1 := by
    have : (0 : Int) < n := by exact_mod_cast hn
    exact lt_of_lt_of_le this alpha.2
  have hbeta : 0 < relativeRootSourceHeight S beta.1 := by
    have : (0 : Int) < n := by exact_mod_cast hn
    exact lt_of_lt_of_le this beta.2
  have hrootne : alpha.1 ≠ beta.1 := fun heq => hne (Subtype.ext heq)
  have hLI := source_positive_roots_linearlyIndependent S halpha hbeta hrootne
  obtain ⟨order, coeff, hnodup, hpairwise, hvalid, hcoeff, hformula⟩ :=
    S.chevalleySystem.2.2.2.2.1 alpha.1 beta.1 hLI
  have hterm (q : ChevalleyCommutatorTerm S.D.Root) (hq : q ∈ order) :
      (n : Int) ≤ relativeRootSourceHeight S q.root ∧
        max (sourceDegree S alpha.1) (sourceDegree S beta.1) <
          sourceDegree S q.root := by
    have hqdata := source_validTerm_positive_and_degree_gt S halpha hbeta q
      ((hvalid q).mp hq)
    have halphaDegree : sourceDegree S alpha.1 ≤ sourceDegree S q.root :=
      le_of_lt (lt_of_le_of_lt (le_max_left _ _) hqdata.2)
    have hnDegree : n ≤ sourceDegree S alpha.1 := by
      rw [sourceDegree]
      exact (Int.le_toNat (le_trans (Int.natCast_nonneg n) alpha.2)).mpr alpha.2
    have hnqDegree : n ≤ sourceDegree S q.root := le_trans hnDegree halphaDegree
    have hqnonneg : 0 ≤ relativeRootSourceHeight S q.root := le_of_lt hqdata.1
    exact (And.intro ((Int.le_toNat hqnonneg).mp hnqDegree) hqdata.2)
  let correction : List (RelativeRootSourceAtLeastIndex S n × k) :=
    order.attach.map fun q =>
      ((Subtype.mk q.1.root (hterm q.1 q.2).1),
        coeff q.1 * a ^ q.1.i * b ^ q.1.j)
  refine Exists.intro correction (And.intro ?_ ?_)
  · intro z hz
    rw [List.mem_map] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    exact And.intro (sourceRelativeRootAtLeastList_mem S n _)
      (hterm q.1 q.2).2
  · have hcorrection :
        FilteredCollection.wordProduct (fun gamma => S.C.x gamma.1)
            correction =
          (order.map fun q =>
            S.C.x q.root (coeff q * a ^ q.i * b ^ q.j)).prod := by
      rw [FilteredCollection.wordProduct]
      dsimp [correction]
      rw [List.map_map]
      change
        (order.attach.map fun q =>
          S.C.x q.1.root (coeff q.1 * a ^ q.1.i * b ^ q.1.j)).prod = _
      exact congrArg List.prod (List.attach_map_val
        (l := order)
        (f := fun q => S.C.x q.root (coeff q * a ^ q.i * b ^ q.j)))
    rw [hcorrection, ← hformula a b]
    group

omit [IsAlgClosed k] in
private theorem sourceRelativeRootAtLeast_collection
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) (hn : 0 < n)
    (word : List (RelativeRootSourceAtLeastIndex S n × k))
    (hword : ∀ z ∈ word, z.1 ∈ sourceRelativeRootAtLeastList S n) :
    ∃ params : RelativeRootSourceAtLeastIndex S n → k,
      FilteredCollection.wordProduct (fun alpha => S.C.x alpha.1) word =
        ((sourceRelativeRootAtLeastList S n).map fun alpha =>
          S.C.x alpha.1 (params alpha)).prod := by
  letI := Fintype.ofFinite S.D.Root
  apply FilteredCollection.filteredCollection_exists_params
    (fun alpha : RelativeRootSourceAtLeastIndex S n => sourceDegree S alpha.1)
      (fun alpha : RelativeRootSourceAtLeastIndex S n => S.C.x alpha.1)
      (sourceRelativeRootAtLeastList S n)
      (sourceRelativeRootAtLeastList_nodup S n) (sourceMaxDegree S + 1)
  · intro alpha halpha
    exact Nat.lt_succ_iff.mpr (sourceDegree_le_max S alpha.1)
  · intro alpha a b
    exact S.chevalleySystem.2.2.2.1 alpha.1 a b
  · intro alpha beta a b halpha hbeta hne
    exact sourceRelativeRootAtLeast_exchange S n hn alpha beta a b hne
  · exact hword

omit [IsAlgClosed k] in
private lemma source_chevalleyRoot_zero
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (alpha : S.D.Root) :
    S.C.x alpha 0 = 1 := by
  simpa using S.chevalleySystem.2.2.2.1 alpha 0 0

omit [IsAlgClosed k] in
private lemma source_chevalleyRoot_neg
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (alpha : S.D.Root) (a : k) :
    S.C.x alpha (-a) = (S.C.x alpha a)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [S.chevalleySystem.2.2.2.1]
  simpa using source_chevalleyRoot_zero S alpha

private noncomputable def sourceLayer
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) :
    Subgroup (Variety.Point K) :=
  sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J n

omit [IsAlgClosed k] in
private theorem sourceLayer_succ_le
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) :
    sourceLayer S (n + 1) ≤ sourceLayer S n := by
  letI := Fintype.ofFinite S.D.Root
  exact relativeRootSeries_antitone S.D (Equiv.refl S.D.Root)
    S.D.simple.toFinite.toFinset S.coeff S.J (Nat.le_succ n)

omit [IsAlgClosed k] in
private theorem sourceLayer_next_normal
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) (hn : 0 < n) :
    ((sourceLayer S (n + 1)).subgroupOf (sourceLayer S n)).Normal := by
  letI := Fintype.ofFinite S.D.Root
  rw [sourceLayer, sourceLayer, sourceRelativeRootLayer, ← source_base_support S]
  exact relativeRootSeries_next_layer_normal S.D S.C S.pairing
    (Equiv.refl S.D.Root) S.base S.coeff S.simpleRootExpansion
      S.chevalleySystem S.J n hn

omit [IsAlgClosed k] in
private theorem sourceLayer_quotient_commutative
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) (hn : 0 < n) :
    let hN := sourceLayer_next_normal S n hn
    let _ := hN
    IsMulCommutative
      (sourceLayer S n ⧸ (sourceLayer S (n + 1)).subgroupOf (sourceLayer S n)) := by
  dsimp only
  letI := Fintype.ofFinite S.D.Root
  let _ := sourceLayer_next_normal S n hn
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
  have hcomm : ⁅sourceLayer S n, sourceLayer S n⁆ ≤ sourceLayer S (n + 1) := by
    simpa only [sourceLayer, sourceRelativeRootLayer, ← source_base_support S] using
      relativeRootSeries_commutator_same_layer_le_next_layer S.D S.C
        S.pairing (Equiv.refl S.D.Root) S.base S.coeff
          S.simpleRootExpansion S.chevalleySystem S.J n hn
  have hmap : (_root_.commutator (sourceLayer S n)).map
      (sourceLayer S n).subtype ≤ sourceLayer S (n + 1) := by
    rw [Subgroup.map_subtype_commutator]
    exact hcomm
  simpa [Subgroup.comap_subtype] using
    (Subgroup.map_le_iff_le_comap.mp hmap)

omit [IsAlgClosed k] in
private theorem source_chevalleyRoot_mem_layer
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat)
    (alpha : S.D.Root) (t : k)
    (halpha : (n : Int) ≤ relativeRootSourceHeight S alpha) :
    S.C.x alpha t ∈ sourceLayer S n := by
  rw [sourceLayer, sourceRelativeRootLayer, RelativeRootSeries,
    RootSubgroupGenerated]
  apply Subgroup.subset_closure
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨alpha, by simpa [relativeRootSourceHeight] using halpha, ?_⟩
  rw [← (S.chevalleySystem.1 alpha).2]
  exact ⟨t, rfl⟩

omit [IsAlgClosed k] in
private theorem sourceLayer_exists_word
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) (_hn : 0 < n)
    (z : Variety.Point K) (hz : z ∈ sourceLayer S n) :
    ∃ word : List (RelativeRootSourceAtLeastIndex S n × k),
      (∀ q ∈ word, q.1 ∈ sourceRelativeRootAtLeastList S n) ∧
      z = FilteredCollection.wordProduct (fun alpha => S.C.x alpha.1) word := by
  classical
  have hwordInv : ∀ word : List (RelativeRootSourceAtLeastIndex S n × k),
      (FilteredCollection.wordProduct (fun alpha => S.C.x alpha.1) word)⁻¹ =
        FilteredCollection.wordProduct (fun alpha => S.C.x alpha.1)
          (word.reverse.map fun q => (q.1, -q.2)) := by
    intro word
    let f : RelativeRootSourceAtLeastIndex S n × k → Variety.Point K :=
      fun q => S.C.x q.1.1 q.2
    let negParam : RelativeRootSourceAtLeastIndex S n × k →
        RelativeRootSourceAtLeastIndex S n × k := fun q => (q.1, -q.2)
    have hneg (q : RelativeRootSourceAtLeastIndex S n × k) :
        f (negParam q) = (f q)⁻¹ := source_chevalleyRoot_neg S q.1.1 q.2
    change (word.map f).prod⁻¹ = ((word.reverse.map negParam).map f).prod
    induction word with
    | nil => simp
    | cons q tail ih =>
        simp only [List.map_cons, List.prod_cons, List.reverse_cons,
          List.map_append, List.map_map, List.prod_append, mul_inv_rev]
        rw [ih, hneg]
        simp [Function.comp_def]
  rw [sourceLayer, sourceRelativeRootLayer, RelativeRootSeries,
    RootSubgroupGenerated] at hz
  have hz' : z ∈ Subgroup.closure
      (⋃ alpha ∈ {alpha | (n : Int) ≤ relativeRootSourceHeight S alpha},
        (S.D.rootSubgroup alpha : Set (Variety.Point K))) := by
    simpa [relativeRootSourceHeight] using hz
  refine Subgroup.closure_induction
    (p := fun z _ => ∃ word : List (RelativeRootSourceAtLeastIndex S n × k),
      (∀ q ∈ word, q.1 ∈ sourceRelativeRootAtLeastList S n) ∧
      z = FilteredCollection.wordProduct (fun alpha => S.C.x alpha.1) word)
    (k := ⋃ alpha ∈ {alpha | (n : Int) ≤ relativeRootSourceHeight S alpha},
      (S.D.rootSubgroup alpha : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hz'
  · intro x hx
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hx
    obtain ⟨alpha, halpha, hxalpha⟩ := hx
    have hxRange : x ∈ Set.range (S.C.x alpha) := by
      rw [(S.chevalleySystem.1 alpha).2]
      exact hxalpha
    obtain ⟨t, rfl⟩ := hxRange
    let alpha' : RelativeRootSourceAtLeastIndex S n := ⟨alpha, halpha⟩
    refine ⟨[(alpha', t)], ?_, ?_⟩
    · simp [sourceRelativeRootAtLeastList_mem S n alpha']
    · simp [FilteredCollection.wordProduct, alpha']
  · exact ⟨[], by simp, by simp [FilteredCollection.wordProduct]⟩
  · intro x y hx hy
    rintro ⟨wordX, hwordX, rfl⟩ ⟨wordY, hwordY, rfl⟩
    refine ⟨wordX ++ wordY, ?_, ?_⟩
    · intro q hq
      exact (List.mem_append.mp hq).elim (hwordX q) (hwordY q)
    · simp [FilteredCollection.wordProduct]
  · intro x hx
    rintro ⟨word, hword, rfl⟩
    refine ⟨word.reverse.map fun q => (q.1, -q.2), ?_, hwordInv word⟩
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    exact hword r (List.mem_reverse.mp hr)

omit [IsAlgClosed k] in
private theorem sourceLayer_exists_collected
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) (hn : 0 < n)
    (z : Variety.Point K) (hz : z ∈ sourceLayer S n) :
    ∃ params : RelativeRootSourceAtLeastIndex S n → k,
      z = ((sourceRelativeRootAtLeastList S n).map fun alpha =>
        S.C.x alpha.1 (params alpha)).prod := by
  obtain ⟨word, hword, rfl⟩ := sourceLayer_exists_word S n hn z hz
  obtain ⟨params, hparams⟩ :=
    sourceRelativeRootAtLeast_collection S n hn word hword
  exact ⟨params, hparams⟩

omit [IsAlgClosed k] in
/-- Every point of a positive source layer is a fixed-order product of the
Chevalley elements indexed by the roots of at least that height. -/
public theorem sourceRelativeRootLayer_exists_collected
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) (hn : 0 < n)
    (z : Variety.Point K)
    (hz : z ∈ sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
      S.coeff S.J n) :
    ∃ params : RelativeRootSourceAtLeastIndex S n → k,
      z = ((sourceRelativeRootAtLeastList S n).map fun alpha =>
        S.C.x alpha.1 (params alpha)).prod := by
  simpa [sourceLayer] using sourceLayer_exists_collected S n hn z hz

private theorem source_positiveRoots_exists_pairingSeparator
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (alpha beta : S.D.Root)
    (halpha : 0 < relativeRootSourceHeight S alpha)
    (hbeta : 0 < relativeRootSourceHeight S beta) (hne : alpha ≠ beta) :
    ∃ u v : kˣ,
      u ^ S.D.pairing alpha beta * v ^ S.D.pairing alpha alpha = 1 ∧
      u ^ S.D.pairing beta beta * v ^ S.D.pairing beta alpha ≠ 1 := by
  letI := Fintype.ofFinite S.D.Root
  let P := S.pairing
  let _ := P.indexNeg
  have halphaPos : S.base.IsPos alpha :=
    base_isPos_of_relativeRootHeight_pos P S.base S.J S.coeff
      S.simpleRootExpansion (by simpa [source_height_eq_base S alpha] using halpha)
  have hbetaPos : S.base.IsPos beta :=
    base_isPos_of_relativeRootHeight_pos P S.base S.J S.coeff
      S.simpleRootExpansion (by simpa [source_height_eq_base S beta] using hbeta)
  have hnotopp : P.root alpha ≠ -P.root beta := by
    intro hneg
    have hidx : alpha = P.reflectionPerm beta beta := P.root_eq_neg_iff.mp hneg
    have halphaNeg : S.base.IsPos (-beta) := by simpa [hidx] using halphaPos
    exact ((RootPairing.Base.IsPos.neg_iff_not
      (P := P) (b := S.base) (i := beta)).mp halphaNeg) hbetaPos
  have hlin : LinearIndependent ℚ ![P.root alpha, P.root beta] :=
    RootPairing.IsReduced.linearIndependent (P := P) hne hnotopp
  have hcox : P.coxeterWeight alpha beta ≠ 4 :=
    (P.linearIndependent_iff_coxeterWeight_ne_four).mp hlin
  let z : Int := 4 - S.D.pairing alpha beta * S.D.pairing beta alpha
  have hz : z ≠ 0 := by
    intro hz0
    apply hcox
    rw [RootPairing.coxeterWeight]
    have hab : (S.D.pairing alpha beta : ℚ) = P.pairing alpha beta := by
      simpa only [Equiv.refl_apply] using S.rootSystemRealization.1 alpha beta
    have hba : (S.D.pairing beta alpha : ℚ) = P.pairing beta alpha := by
      simpa only [Equiv.refl_apply] using S.rootSystemRealization.1 beta alpha
    rw [← hab, ← hba]
    have hzprod : S.D.pairing alpha beta * S.D.pairing beta alpha = 4 := by
      dsimp [z] at hz0
      omega
    exact_mod_cast hzprod
  obtain ⟨c, hc⟩ := exists_unit_zpow_ne_one (k := k) hz
  let a := S.D.pairing alpha beta
  let b := S.D.pairing beta alpha
  refine ⟨c ^ (2 : Int), c ^ (-a), ?_, ?_⟩
  · rw [S.isRealization.2.2.2.2.2.2.1 alpha]
    dsimp [a]
    rw [← zpow_mul, ← zpow_mul, ← zpow_add]
    convert zpow_zero c using 1
    all_goals ring_nf
  · rw [S.isRealization.2.2.2.2.2.2.1 beta]
    dsimp [a, b, z] at hc ⊢
    rw [← zpow_mul, ← zpow_mul, ← zpow_add]
    convert hc using 1
    all_goals ring_nf

private def sourceCorootPairScale
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (alpha beta gamma : S.D.Root) (u v : kˣ) : k :=
  (u : k) ^ S.D.pairing gamma beta *
    (v : k) ^ S.D.pairing gamma alpha

omit [IsAlgClosed k] in
private theorem sourceCorootPair_conjugates_root
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (alpha beta gamma : S.D.Root) (u v : kˣ) (t : k) :
    (S.C.h beta u * S.C.h alpha v)⁻¹ * S.C.x gamma t *
        (S.C.h beta u * S.C.h alpha v) =
      S.C.x gamma (sourceCorootPairScale S alpha beta gamma u v * t) := by
  have hconj := S.chevalleySystem.2.2.2.2.2.2.2.2.2.2.2.1
  calc
    (S.C.h beta u * S.C.h alpha v)⁻¹ * S.C.x gamma t *
        (S.C.h beta u * S.C.h alpha v) =
        (S.C.h alpha v)⁻¹ *
          ((S.C.h beta u)⁻¹ * S.C.x gamma t * S.C.h beta u) *
            S.C.h alpha v := by group
    _ = (S.C.h alpha v)⁻¹ *
          S.C.x gamma ((u : k) ^ S.D.pairing gamma beta * t) *
            S.C.h alpha v := by rw [hconj gamma beta t u]
    _ = S.C.x gamma
        ((v : k) ^ S.D.pairing gamma alpha *
          ((u : k) ^ S.D.pairing gamma beta * t)) :=
      hconj gamma alpha ((u : k) ^ S.D.pairing gamma beta * t) v
    _ = _ := by
      apply congrArg (S.C.x gamma)
      simp only [sourceCorootPairScale]
      ring

omit [IsAlgClosed k] in
private theorem sourceCorootPair_conjugates_word
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (alpha beta : S.D.Root) (u v : kˣ)
    (word : List (S.D.Root × k)) :
    (S.C.h beta u * S.C.h alpha v)⁻¹ *
        FilteredCollection.wordProduct S.C.x word *
          (S.C.h beta u * S.C.h alpha v) =
      FilteredCollection.wordProduct S.C.x
        (word.map fun q =>
          (q.1, sourceCorootPairScale S alpha beta q.1 u v * q.2)) := by
  induction word with
  | nil => simp [FilteredCollection.wordProduct]
  | cons q tail ih =>
      rw [show FilteredCollection.wordProduct S.C.x (q :: tail) =
          S.C.x q.1 q.2 * FilteredCollection.wordProduct S.C.x tail by rfl]
      rw [show FilteredCollection.wordProduct S.C.x
          ((q :: tail).map fun r =>
            (r.1, sourceCorootPairScale S alpha beta r.1 u v * r.2)) =
          S.C.x q.1 (sourceCorootPairScale S alpha beta q.1 u v * q.2) *
            FilteredCollection.wordProduct S.C.x
              (tail.map fun r =>
                (r.1, sourceCorootPairScale S alpha beta r.1 u v * r.2)) by rfl]
      calc
        (S.C.h beta u * S.C.h alpha v)⁻¹ *
            (S.C.x q.1 q.2 * FilteredCollection.wordProduct S.C.x tail) *
              (S.C.h beta u * S.C.h alpha v) =
            ((S.C.h beta u * S.C.h alpha v)⁻¹ * S.C.x q.1 q.2 *
              (S.C.h beta u * S.C.h alpha v)) *
            ((S.C.h beta u * S.C.h alpha v)⁻¹ *
              FilteredCollection.wordProduct S.C.x tail *
                (S.C.h beta u * S.C.h alpha v)) := by group
        _ = _ := by rw [sourceCorootPair_conjugates_root, ih]

omit [IsAlgClosed k] in
private theorem sourceCorootPair_conjugates_layer
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) (hn : 0 < n)
    (alpha beta : S.D.Root) (u v : kˣ)
    (z : Variety.Point K) (hz : z ∈ sourceLayer S n) :
    (S.C.h beta u * S.C.h alpha v)⁻¹ * z *
      (S.C.h beta u * S.C.h alpha v) ∈ sourceLayer S n := by
  obtain ⟨word, hword, rfl⟩ := sourceLayer_exists_word S n hn z hz
  let rawWord : List (S.D.Root × k) := word.map fun q => (q.1.1, q.2)
  have hraw : FilteredCollection.wordProduct
      (fun gamma : RelativeRootSourceAtLeastIndex S n => S.C.x gamma.1) word =
      FilteredCollection.wordProduct S.C.x rawWord := by
    simp [rawWord, FilteredCollection.wordProduct, List.map_map,
      Function.comp_def]
  rw [hraw, sourceCorootPair_conjugates_word]
  apply Subgroup.list_prod_mem
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  rw [List.mem_map] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  rw [List.mem_map] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  exact source_chevalleyRoot_mem_layer S n s.1.1 _ s.1.2

omit [IsAlgClosed k] in
private theorem source_exactWord_difference_mem_next
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (i : Nat) (hi : 0 < i)
    (word : List (S.D.Root × k))
    (hexact : ∀ q ∈ word, relativeRootSourceHeight S q.1 = i)
    (alpha beta : S.D.Root) (u v : kˣ)
    (hrelation :
      FilteredCollection.wordProduct S.C.x
          (word.map fun q =>
            (q.1, sourceCorootPairScale S alpha beta q.1 u v * q.2)) *
        (FilteredCollection.wordProduct S.C.x word)⁻¹ ∈ sourceLayer S (i + 1)) :
    FilteredCollection.wordProduct S.C.x
      (word.map fun q =>
        (q.1,
          (sourceCorootPairScale S alpha beta q.1 u v - 1) * q.2)) ∈
        sourceLayer S (i + 1) := by
  classical
  let hN := sourceLayer_next_normal S i hi
  letI := hN
  let hcomm := sourceLayer_quotient_commutative S i hi
  letI := hcomm
  let N := (sourceLayer S (i + 1)).subgroupOf (sourceLayer S i)
  let Q := sourceLayer S i ⧸ N
  have horigLayer : FilteredCollection.wordProduct S.C.x word ∈ sourceLayer S i := by
    apply Subgroup.list_prod_mem
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact source_chevalleyRoot_mem_layer S i q.1 q.2 (by rw [hexact q hq])
  have hscaledLayer : FilteredCollection.wordProduct S.C.x
      (word.map fun q =>
        (q.1, sourceCorootPairScale S alpha beta q.1 u v * q.2)) ∈
      sourceLayer S i := by
    apply Subgroup.list_prod_mem
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    rw [List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    exact source_chevalleyRoot_mem_layer S i r.1 _ (by rw [hexact r hr])
  let original (q : {q // q ∈ word}) : Q :=
    QuotientGroup.mk' N
      ⟨S.C.x q.1.1 q.1.2, source_chevalleyRoot_mem_layer S i q.1.1 q.1.2 (by
        rw [hexact q.1 q.2])⟩
  let scaled (q : {q // q ∈ word}) : Q :=
    QuotientGroup.mk' N
      ⟨S.C.x q.1.1
          (sourceCorootPairScale S alpha beta q.1.1 u v * q.1.2),
        source_chevalleyRoot_mem_layer S i q.1.1 _ (by rw [hexact q.1 q.2])⟩
  let difference (q : {q // q ∈ word}) : Q :=
    QuotientGroup.mk' N
      ⟨S.C.x q.1.1
          ((sourceCorootPairScale S alpha beta q.1.1 u v - 1) *
            q.1.2),
        source_chevalleyRoot_mem_layer S i q.1.1 _ (by rw [hexact q.1 q.2])⟩
  have hfactor (q : {q // q ∈ word}) :
      difference q = scaled q * (original q)⁻¹ := by
    have hparam :
        (sourceCorootPairScale S alpha beta q.1.1 u v - 1) * q.1.2 =
          sourceCorootPairScale S alpha beta q.1.1 u v * q.1.2 +
            (-q.1.2) := by ring
    have hx : S.C.x q.1.1
        ((sourceCorootPairScale S alpha beta q.1.1 u v - 1) * q.1.2) =
        S.C.x q.1.1
          (sourceCorootPairScale S alpha beta q.1.1 u v * q.1.2) *
            (S.C.x q.1.1 q.1.2)⁻¹ := by
      rw [hparam, ← S.chevalleySystem.2.2.2.1, source_chevalleyRoot_neg S]
    change QuotientGroup.mk' N ⟨S.C.x q.1.1 _, _⟩ =
      QuotientGroup.mk' N ⟨S.C.x q.1.1 _, _⟩ *
        (QuotientGroup.mk' N ⟨S.C.x q.1.1 q.1.2, _⟩)⁻¹
    rw [← map_inv, ← map_mul]
    apply congrArg (QuotientGroup.mk' N)
    apply Subtype.ext
    exact hx
  have hprod :
      (word.attach.map difference).prod =
        (word.attach.map scaled).prod * (word.attach.map original).prod⁻¹ := by
    induction word.attach with
    | nil => simp
    | cons q tail ih =>
        simp only [List.map_cons, List.prod_cons]
        rw [hfactor, ih, mul_inv_rev]
        ac_rfl
  have horiginal :
      (word.attach.map original).prod =
        QuotientGroup.mk' N
          ⟨FilteredCollection.wordProduct S.C.x word,
            horigLayer⟩ := by
    calc
      (word.attach.map original).prod =
          ((word.attach.map fun q =>
            (⟨S.C.x q.1.1 q.1.2,
              source_chevalleyRoot_mem_layer S i q.1.1 q.1.2 (by
                rw [hexact q.1 q.2])⟩ : sourceLayer S i)).map
              (QuotientGroup.mk' N)).prod := by
            simp only [List.map_map]
            rfl
      _ = QuotientGroup.mk' N
          (word.attach.map fun q =>
            (⟨S.C.x q.1.1 q.1.2,
              source_chevalleyRoot_mem_layer S i q.1.1 q.1.2 (by
                rw [hexact q.1 q.2])⟩ : sourceLayer S i)).prod :=
            (map_list_prod (QuotientGroup.mk' N) _).symm
      _ = QuotientGroup.mk' N
          ⟨FilteredCollection.wordProduct S.C.x word,
            horigLayer⟩ := by
            apply congrArg (QuotientGroup.mk' N)
            apply Subtype.ext
            rw [SubmonoidClass.coe_list_prod]
            simp only [List.map_map]
            exact congrArg List.prod (List.attach_map_val
              (l := word) (f := fun q => S.C.x q.1 q.2))
  have hscaled' :
      (word.attach.map scaled).prod =
        QuotientGroup.mk' N
          ⟨FilteredCollection.wordProduct S.C.x
            (word.map fun q =>
              (q.1, sourceCorootPairScale S alpha beta q.1 u v * q.2)),
            hscaledLayer⟩ := by
    calc
      (word.attach.map scaled).prod =
          ((word.attach.map fun q =>
            (⟨S.C.x q.1.1
                (sourceCorootPairScale S alpha beta q.1.1 u v * q.1.2),
              source_chevalleyRoot_mem_layer S i q.1.1 _ (by
                rw [hexact q.1 q.2])⟩ : sourceLayer S i)).map
              (QuotientGroup.mk' N)).prod := by
            simp only [List.map_map]
            rfl
      _ = QuotientGroup.mk' N
          (word.attach.map fun q =>
            (⟨S.C.x q.1.1
                (sourceCorootPairScale S alpha beta q.1.1 u v * q.1.2),
              source_chevalleyRoot_mem_layer S i q.1.1 _ (by
                rw [hexact q.1 q.2])⟩ : sourceLayer S i)).prod :=
            (map_list_prod (QuotientGroup.mk' N) _).symm
      _ = QuotientGroup.mk' N
          ⟨FilteredCollection.wordProduct S.C.x
            (word.map fun q =>
              (q.1, sourceCorootPairScale S alpha beta q.1 u v * q.2)),
            hscaledLayer⟩ := by
            apply congrArg (QuotientGroup.mk' N)
            apply Subtype.ext
            rw [SubmonoidClass.coe_list_prod]
            simp only [List.map_map]
            rw [FilteredCollection.wordProduct]
            simp only [List.map_map]
            change (word.attach.map fun q => S.C.x q.1.1
              (sourceCorootPairScale S alpha beta q.1.1 u v *
                q.1.2)).prod = _
            exact congrArg List.prod (List.attach_map_val
              (l := word)
              (f := fun q => S.C.x q.1
                (sourceCorootPairScale S alpha beta q.1 u v * q.2)))
  have hrelationOne :
      (word.attach.map scaled).prod * (word.attach.map original).prod⁻¹ = 1 := by
    rw [hscaled', horiginal, ← map_inv, ← map_mul]
    exact (QuotientGroup.eq_one_iff (N := N)
      (⟨FilteredCollection.wordProduct S.C.x
          (word.map fun q : S.D.Root × k =>
            (q.1, sourceCorootPairScale S alpha beta q.1 u v * q.2)) *
        (FilteredCollection.wordProduct S.C.x word)⁻¹, by
          exact sourceLayer S i |>.mul_mem hscaledLayer (sourceLayer S i |>.inv_mem horigLayer)⟩ :
        sourceLayer S i)).2 hrelation
  have hdifferenceOne : (word.attach.map difference).prod = 1 := by
    rw [hprod, hrelationOne]
  let differencePoint : sourceLayer S i :=
    ⟨FilteredCollection.wordProduct S.C.x
      (word.map fun q =>
        (q.1,
          (sourceCorootPairScale S alpha beta q.1 u v - 1) * q.2)), by
      apply Subgroup.list_prod_mem
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      rw [List.mem_map] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      exact source_chevalleyRoot_mem_layer S i r.1 _ (by rw [hexact r hr])⟩
  have hdifference :
      (word.attach.map difference).prod = QuotientGroup.mk' N differencePoint := by
    calc
      (word.attach.map difference).prod =
          ((word.attach.map fun q =>
            (⟨S.C.x q.1.1
                ((sourceCorootPairScale S alpha beta q.1.1 u v - 1) *
                  q.1.2),
              source_chevalleyRoot_mem_layer S i q.1.1 _ (by
                rw [hexact q.1 q.2])⟩ : sourceLayer S i)).map
              (QuotientGroup.mk' N)).prod := by
            simp only [List.map_map]
            rfl
      _ = QuotientGroup.mk' N
          (word.attach.map fun q =>
            (⟨S.C.x q.1.1
                ((sourceCorootPairScale S alpha beta q.1.1 u v - 1) *
                  q.1.2),
              source_chevalleyRoot_mem_layer S i q.1.1 _ (by
                rw [hexact q.1 q.2])⟩ : sourceLayer S i)).prod :=
            (map_list_prod (QuotientGroup.mk' N) _).symm
      _ = QuotientGroup.mk' N differencePoint := by
            apply congrArg (QuotientGroup.mk' N)
            apply Subtype.ext
            rw [SubmonoidClass.coe_list_prod]
            simp only [List.map_map]
            dsimp [differencePoint]
            rw [FilteredCollection.wordProduct]
            simp only [List.map_map]
            change (word.attach.map fun q => S.C.x q.1.1
              ((sourceCorootPairScale S alpha beta q.1.1 u v - 1) *
                q.1.2)).prod = _
            exact congrArg List.prod (List.attach_map_val
              (l := word)
              (f := fun q => S.C.x q.1
                ((sourceCorootPairScale S alpha beta q.1 u v - 1) * q.2)))
  rw [hdifference] at hdifferenceOne
  exact (QuotientGroup.eq_one_iff (N := N) differencePoint).1 hdifferenceOne

omit [IsAlgClosed k] in
private theorem source_word_mul_exactHeightPart_inv_mem_next
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (e : Nat) (he : 0 < e)
    (word : List (S.D.Root × k))
    (hzeroBelow : ∀ q ∈ word, relativeRootSourceHeight S q.1 < e → q.2 = 0) :
    FilteredCollection.wordProduct S.C.x word *
        (FilteredCollection.wordProduct S.C.x
          (word.filter fun q => relativeRootSourceHeight S q.1 = e))⁻¹ ∈
      sourceLayer S (e + 1) := by
  classical
  let hN := sourceLayer_next_normal S e he
  induction word with
  | nil => simp [FilteredCollection.wordProduct]
  | cons q tail ih =>
      have hzeroTail : ∀ r ∈ tail, relativeRootSourceHeight S r.1 < e → r.2 = 0 := by
        intro r hr
        exact hzeroBelow r (by simp [hr])
      have ih' := ih hzeroTail
      have hqLayer : S.C.x q.1 q.2 ∈ sourceLayer S e := by
        by_cases hle : (e : Int) ≤ relativeRootSourceHeight S q.1
        · exact source_chevalleyRoot_mem_layer S e q.1 q.2 hle
        · have hqzero := hzeroBelow q (by simp) (by omega)
          rw [hqzero, source_chevalleyRoot_zero S]
          exact Subgroup.one_mem _
      by_cases hqExact : relativeRootSourceHeight S q.1 = e
      · have hconj := hN.conj_mem
          (⟨FilteredCollection.wordProduct S.C.x tail *
              (FilteredCollection.wordProduct S.C.x
                (tail.filter fun r => relativeRootSourceHeight S r.1 = e))⁻¹,
            sourceLayer_succ_le S e ih'⟩ : sourceLayer S e)
          ih' (⟨S.C.x q.1 q.2, hqLayer⟩ : sourceLayer S e)
        change S.C.x q.1 q.2 *
            (FilteredCollection.wordProduct S.C.x tail *
              (FilteredCollection.wordProduct S.C.x
                (tail.filter fun r => relativeRootSourceHeight S r.1 = e))⁻¹) *
              (S.C.x q.1 q.2)⁻¹ ∈ sourceLayer S (e + 1) at hconj
        simpa [FilteredCollection.wordProduct, hqExact, mul_inv_rev, mul_assoc]
          using hconj
      · have hqNotBelowOrAbove :
            relativeRootSourceHeight S q.1 < e ∨ (e + 1 : Int) ≤ relativeRootSourceHeight S q.1 := by
          omega
        rcases hqNotBelowOrAbove with hqBelow | hqAbove
        · have hqzero := hzeroBelow q (by simp) hqBelow
          simpa [FilteredCollection.wordProduct, hqExact, hqzero,
            source_chevalleyRoot_zero S] using ih'
        · have hqNext : S.C.x q.1 q.2 ∈ sourceLayer S (e + 1) :=
            source_chevalleyRoot_mem_layer S (e + 1) q.1 q.2 hqAbove
          have hmul := (sourceLayer S (e + 1)).mul_mem hqNext ih'
          simpa [FilteredCollection.wordProduct, hqExact, mul_assoc] using hmul

omit [IsAlgClosed k] in
private theorem source_minimalHeight_difference_mem_next
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (e : Nat) (he : 0 < e)
    (word : List (S.D.Root × k))
    (hzeroBelow : ∀ q ∈ word, relativeRootSourceHeight S q.1 < e → q.2 = 0)
    (alpha beta : S.D.Root) (u v : kˣ)
    (heq : FilteredCollection.wordProduct S.C.x
      (word.map fun q =>
        (q.1, sourceCorootPairScale S alpha beta q.1 u v * q.2)) =
      FilteredCollection.wordProduct S.C.x word) :
    FilteredCollection.wordProduct S.C.x
      ((word.filter fun q => relativeRootSourceHeight S q.1 = e).map fun q =>
        (q.1,
          (sourceCorootPairScale S alpha beta q.1 u v - 1) * q.2)) ∈
      sourceLayer S (e + 1) := by
  classical
  let scaledWord := word.map fun q =>
    (q.1, sourceCorootPairScale S alpha beta q.1 u v * q.2)
  let exactWord := word.filter fun q => relativeRootSourceHeight S q.1 = e
  have hscaledZeroBelow : ∀ q ∈ scaledWord,
      relativeRootSourceHeight S q.1 < e → q.2 = 0 := by
    intro q hq hqBelow
    rw [List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    rw [hzeroBelow r hr hqBelow, mul_zero]
  have horigApprox :=
    source_word_mul_exactHeightPart_inv_mem_next S e he word hzeroBelow
  have hscaledApprox :=
    source_word_mul_exactHeightPart_inv_mem_next S e he scaledWord
      hscaledZeroBelow
  have hfilter :
      scaledWord.filter (fun q => relativeRootSourceHeight S q.1 = e) =
        exactWord.map fun q =>
          (q.1, sourceCorootPairScale S alpha beta q.1 u v * q.2) := by
    dsimp [scaledWord, exactWord]
    rw [List.filter_map]
    rfl
  have hrelation :
      FilteredCollection.wordProduct S.C.x
          (exactWord.map fun q =>
            (q.1, sourceCorootPairScale S alpha beta q.1 u v * q.2)) *
        (FilteredCollection.wordProduct S.C.x exactWord)⁻¹ ∈ sourceLayer S (e + 1) := by
    have hmul := (sourceLayer S (e + 1)).mul_mem
      ((sourceLayer S (e + 1)).inv_mem hscaledApprox) horigApprox
    rw [hfilter] at hmul
    dsimp [exactWord] at hmul ⊢
    convert hmul using 1
    all_goals
      rw [heq]
      group
  apply source_exactWord_difference_mem_next S e he exactWord
  · intro q hq
    dsimp [exactWord] at hq
    exact of_decide_eq_true (List.mem_filter.mp hq |>.2)
  · exact hrelation

omit [IsAlgClosed k] in
private theorem chevalleyWord_eq_one_of_params_eq_zero
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (word : List (S.D.Root × k))
    (hzero : ∀ q ∈ word, q.2 = 0) :
    FilteredCollection.wordProduct S.C.x word = 1 := by
  induction word with
  | nil => simp [FilteredCollection.wordProduct]
  | cons q tail ih =>
      have hq := hzero q (by simp)
      have htail : ∀ r ∈ tail, r.2 = 0 := by
        intro r hr
        exact hzero r (by simp [hr])
      rw [show FilteredCollection.wordProduct S.C.x (q :: tail) =
        S.C.x q.1 q.2 * FilteredCollection.wordProduct S.C.x tail by rfl]
      rw [hq, source_chevalleyRoot_zero S, ih htail, one_mul]

omit [IsAlgClosed k] in
private theorem chevalleyWord_eq_single_of_other_params_eq_zero
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (word : List (S.D.Root × k)) (q : S.D.Root × k) (hq : q ∈ word)
    (hnodup : (word.map Prod.fst).Nodup)
    (hzero : ∀ r ∈ word, r ≠ q → r.2 = 0) :
    FilteredCollection.wordProduct S.C.x word = S.C.x q.1 q.2 := by
  induction word with
  | nil => simp at hq
  | cons r tail ih =>
      have hnodup' := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hq with rfl | hqtail
      · have htail : ∀ z ∈ tail, z.2 = 0 := by
          intro z hz
          apply hzero z (by simp [hz])
          intro heq
          subst z
          exact hnodup'.1 (List.mem_map.mpr ⟨q, hz, rfl⟩)
        rw [show FilteredCollection.wordProduct S.C.x (q :: tail) =
          S.C.x q.1 q.2 * FilteredCollection.wordProduct S.C.x tail by rfl]
        rw [chevalleyWord_eq_one_of_params_eq_zero S tail htail, mul_one]
      · have hrzero : r.2 = 0 := hzero r (by simp) (by
          intro heq
          subst r
          exact hnodup'.1 (List.mem_map.mpr ⟨q, hqtail, rfl⟩))
        have htail : ∀ z ∈ tail, z ≠ q → z.2 = 0 := by
          intro z hz hzne
          exact hzero z (by simp [hz]) hzne
        rw [show FilteredCollection.wordProduct S.C.x (r :: tail) =
          S.C.x r.1 r.2 * FilteredCollection.wordProduct S.C.x tail by rfl]
        rw [hrzero, source_chevalleyRoot_zero S, one_mul, ih hqtail hnodup'.2 htail]

private noncomputable def nonzeroRootSupport
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (word : List (S.D.Root × k)) : Finset S.D.Root := by
  classical
  exact (word.toFinset.filter fun q => q.2 ≠ 0).image Prod.fst

omit [IsAlgClosed k] in
private theorem mem_nonzeroRootSupport_iff
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (word : List (S.D.Root × k)) (alpha : S.D.Root) :
    alpha ∈ nonzeroRootSupport S word ↔
      ∃ q ∈ word, q.1 = alpha ∧ q.2 ≠ 0 := by
  classical
  simp [nonzeroRootSupport]

omit [IsAlgClosed k] in
private theorem pair_eq_of_mem_of_root_eq
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (word : List (S.D.Root × k))
    (hnodup : (word.map Prod.fst).Nodup)
    {q r : S.D.Root × k} (hq : q ∈ word) (hr : r ∈ word)
    (hroot : q.1 = r.1) : q = r := by
  induction word with
  | nil => simp at hq
  | cons z tail ih =>
      have hnodup' := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hq with rfl | hqtail
      · rcases List.mem_cons.mp hr with rfl | hrtail
        · rfl
        · exact False.elim (hnodup'.1
            (List.mem_map.mpr ⟨r, hrtail, hroot.symm⟩))
      · rcases List.mem_cons.mp hr with rfl | hrtail
        · exact False.elim (hnodup'.1
            (List.mem_map.mpr ⟨q, hqtail, hroot⟩))
        · exact ih hnodup'.2 hqtail hrtail

private theorem source_exactWord_parameters_eq_zero_of_singleRoot
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (i : Nat) (hi : 0 < i)
    (hsingle : ∀ alpha t,
      relativeRootSourceHeight S alpha = i → S.C.x alpha t ∈ sourceLayer S (i + 1) → t = 0)
    (word : List (S.D.Root × k))
    (hnodup : (word.map Prod.fst).Nodup)
    (hexact : ∀ q ∈ word, relativeRootSourceHeight S q.1 = i)
    (hmem : FilteredCollection.wordProduct S.C.x word ∈ sourceLayer S (i + 1)) :
    ∀ q ∈ word, q.2 = 0 := by
  classical
  by_cases hempty : nonzeroRootSupport S word = ∅
  · intro q hq
    by_contra hqzero
    have hqsupport : q.1 ∈ nonzeroRootSupport S word :=
      (mem_nonzeroRootSupport_iff S word q.1).2 ⟨q, hq, rfl, hqzero⟩
    simp [hempty] at hqsupport
  · have hsupportNonempty : (nonzeroRootSupport S word).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨alpha, halphaSupport⟩ := hsupportNonempty
    obtain ⟨qa, hqa, hqaRoot, hqaNonzero⟩ :=
      (mem_nonzeroRootSupport_iff S word alpha).1 halphaSupport
    by_cases hcard : (nonzeroRootSupport S word).card = 1
    · have hcardLe : (nonzeroRootSupport S word).card ≤ 1 := by omega
      have hzeroOther : ∀ r ∈ word, r ≠ qa → r.2 = 0 := by
        intro r hr hrne
        by_contra hrzero
        have hrSupport : r.1 ∈ nonzeroRootSupport S word :=
          (mem_nonzeroRootSupport_iff S word r.1).2 ⟨r, hr, rfl, hrzero⟩
        have hroot : r.1 = qa.1 :=
          (Finset.card_le_one.mp hcardLe r.1 hrSupport qa.1
            ((mem_nonzeroRootSupport_iff S word qa.1).2
              ⟨qa, hqa, rfl, hqaNonzero⟩))
        exact hrne (pair_eq_of_mem_of_root_eq S word hnodup hr hqa hroot)
      have hproduct := chevalleyWord_eq_single_of_other_params_eq_zero
        S word qa hqa hnodup hzeroOther
      have hqaMem : S.C.x qa.1 qa.2 ∈ sourceLayer S (i + 1) := by
        rw [← hproduct]
        exact hmem
      exact False.elim (hqaNonzero
        (hsingle qa.1 qa.2 (hexact qa hqa) hqaMem))
    · have hcardGt : 1 < (nonzeroRootSupport S word).card := by
        have hcardPos : 0 < (nonzeroRootSupport S word).card :=
          Finset.card_pos.mpr ⟨alpha, halphaSupport⟩
        omega
      obtain ⟨beta, hbetaSupport, hbetaNe⟩ :=
        Finset.exists_mem_ne hcardGt alpha
      obtain ⟨qb, hqb, hqbRoot, hqbNonzero⟩ :=
        (mem_nonzeroRootSupport_iff S word beta).1 hbetaSupport
      have halphaPos : 0 < relativeRootSourceHeight S qa.1 := by
        rw [hexact qa hqa]
        exact_mod_cast hi
      have hbetaPos : 0 < relativeRootSourceHeight S qb.1 := by
        rw [hexact qb hqb]
        exact_mod_cast hi
      have hrootNe : qa.1 ≠ qb.1 := by
        rw [hqaRoot, hqbRoot]
        exact hbetaNe.symm
      obtain ⟨u, v, hfix, hmove⟩ :=
        source_positiveRoots_exists_pairingSeparator S qa.1 qb.1
          halphaPos hbetaPos hrootNe
      let differenceWord := word.map fun q =>
        (q.1,
          (sourceCorootPairScale S qa.1 qb.1 q.1 u v - 1) * q.2)
      have hscaledMem :
          FilteredCollection.wordProduct S.C.x
              (word.map fun q =>
                (q.1, sourceCorootPairScale S qa.1 qb.1 q.1 u v * q.2)) ∈
            sourceLayer S (i + 1) := by
        have hconj := sourceCorootPair_conjugates_layer S (i + 1)
          (by omega) qa.1 qb.1 u v
            (FilteredCollection.wordProduct S.C.x word) hmem
        rw [sourceCorootPair_conjugates_word] at hconj
        exact hconj
      have hrelation :
          FilteredCollection.wordProduct S.C.x
              (word.map fun q =>
                (q.1, sourceCorootPairScale S qa.1 qb.1 q.1 u v * q.2)) *
            (FilteredCollection.wordProduct S.C.x word)⁻¹ ∈ sourceLayer S (i + 1) :=
        (sourceLayer S (i + 1)).mul_mem hscaledMem ((sourceLayer S (i + 1)).inv_mem hmem)
      have hdifferenceMem :
          FilteredCollection.wordProduct S.C.x differenceWord ∈ sourceLayer S (i + 1) := by
        exact source_exactWord_difference_mem_next S i hi word hexact
          qa.1 qb.1 u v hrelation
      have hdifferenceNodup : (differenceWord.map Prod.fst).Nodup := by
        simpa [differenceWord, List.map_map, Function.comp_def] using hnodup
      have hdifferenceExact : ∀ q ∈ differenceWord,
          relativeRootSourceHeight S q.1 = i := by
        intro q hq
        rw [List.mem_map] at hq
        obtain ⟨r, hr, rfl⟩ := hq
        exact hexact r hr
      have hsupportSubset : nonzeroRootSupport S differenceWord ⊆
          nonzeroRootSupport S word := by
        intro gamma hgamma
        obtain ⟨q, hq, hqRoot, hqNonzero⟩ :=
          (mem_nonzeroRootSupport_iff S differenceWord gamma).1 hgamma
        rw [List.mem_map] at hq
        obtain ⟨r, hr, rfl⟩ := hq
        apply (mem_nonzeroRootSupport_iff S word gamma).2
        refine ⟨r, hr, hqRoot, ?_⟩
        intro hrzero
        apply hqNonzero
        rw [hrzero, mul_zero]
      have hqaNotDifference : qa.1 ∉ nonzeroRootSupport S differenceWord := by
        intro hqaDifference
        obtain ⟨q, hq, hqRoot, hqNonzero⟩ :=
          (mem_nonzeroRootSupport_iff S differenceWord qa.1).1 hqaDifference
        rw [List.mem_map] at hq
        obtain ⟨r, hr, rfl⟩ := hq
        have hrRoot : r.1 = qa.1 := hqRoot
        apply hqNonzero
        rw [hrRoot]
        have hfixField :
            (u : k) ^ S.D.pairing qa.1 qb.1 *
              (v : k) ^ S.D.pairing qa.1 qa.1 = 1 := by
          simpa using congrArg Units.val hfix
        rw [sourceCorootPairScale, hfixField, sub_self, zero_mul]
      have hqaOriginal : qa.1 ∈ nonzeroRootSupport S word :=
        (mem_nonzeroRootSupport_iff S word qa.1).2
          ⟨qa, hqa, rfl, hqaNonzero⟩
      have hproper : nonzeroRootSupport S differenceWord ⊂
          nonzeroRootSupport S word :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hsupportSubset, fun heq =>
          hqaNotDifference (heq.symm ▸ hqaOriginal)⟩
      have hrec := source_exactWord_parameters_eq_zero_of_singleRoot
        S i hi hsingle differenceWord hdifferenceNodup hdifferenceExact hdifferenceMem
      have hqbDifference :
          (qb.1,
            (sourceCorootPairScale S qa.1 qb.1 qb.1 u v - 1) * qb.2) ∈
            differenceWord := by
        exact List.mem_map.mpr ⟨qb, hqb, rfl⟩
      have hbetaDifferenceZero := hrec _ hqbDifference
      have hmoveField :
          sourceCorootPairScale S qa.1 qb.1 qb.1 u v ≠ 1 := by
        intro heq
        apply hmove
        apply Units.ext
        simpa [sourceCorootPairScale] using heq
      exact False.elim ((mul_ne_zero (sub_ne_zero.mpr hmoveField) hqbNonzero)
        hbetaDifferenceZero)
termination_by (nonzeroRootSupport S word).card
decreasing_by exact Finset.card_lt_card hproper

/-- A collected word with one factor for each root of exact positive relative
height has no nonzero parameter when its product lies in the next layer. -/
private theorem source_exactHeight_parameters_eq_zero_of_wordProduct_mem_next
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (i : Nat) (hi : 0 < i)
    (word : List (S.D.Root × k))
    (hnodup : (word.map Prod.fst).Nodup)
    (hexact : ∀ q ∈ word, relativeRootSourceHeight S q.1 = i)
    (hmem : FilteredCollection.wordProduct S.C.x word ∈ sourceLayer S (i + 1)) :
    ∀ q ∈ word, q.2 = 0 := by
  classical
  have hsingle : ∀ alpha t,
      relativeRootSourceHeight S alpha = i →
        S.C.x alpha t ∈ sourceLayer S (i + 1) → t = 0 := by
    intro alpha t halpha hrootMem
    obtain ⟨params, hparams⟩ :=
      sourceLayer_exists_collected S (i + 1) (by omega)
        (S.C.x alpha t) hrootMem
    let highWord : List (S.D.Root × k) :=
      (sourceRelativeRootAtLeastList S (i + 1)).map fun gamma =>
        (gamma.1, params gamma)
    have hhighProduct :
        FilteredCollection.wordProduct S.C.x highWord = S.C.x alpha t := by
      calc
        FilteredCollection.wordProduct S.C.x highWord =
            ((sourceRelativeRootAtLeastList S (i + 1)).map fun gamma =>
              S.C.x gamma.1 (params gamma)).prod := by
                simp [highWord, FilteredCollection.wordProduct, List.map_map,
                  Function.comp_def]
        _ = S.C.x alpha t := hparams.symm
    have hhighNodup : (highWord.map Prod.fst).Nodup := by
      have hsubtypeNodup := sourceRelativeRootAtLeastList_nodup S (i + 1)
      have hrootListNodup := hsubtypeNodup.map
        (fun _ _ h => Subtype.ext h)
      dsimp [highWord]
      rw [List.map_map]
      change (List.map (fun gamma : RelativeRootSourceAtLeastIndex S (i + 1) => gamma.1)
        (sourceRelativeRootAtLeastList S (i + 1))).Nodup
      exact hrootListNodup
    have hparamsZero : ∀ gamma : RelativeRootSourceAtLeastIndex S (i + 1),
        params gamma = 0 := by
      letI : Finite (RelativeRootSourceAtLeastIndex S (i + 1)) := by
        unfold RelativeRootSourceAtLeastIndex
        infer_instance
      letI := Fintype.ofFinite (RelativeRootSourceAtLeastIndex S (i + 1))
      by_contra hnotAllZero
      push Not at hnotAllZero
      let support : Finset (RelativeRootSourceAtLeastIndex S (i + 1)) :=
        Finset.univ.filter fun gamma => params gamma ≠ 0
      have hsupportNonempty : support.Nonempty := by
        obtain ⟨gamma, hgamma⟩ := hnotAllZero
        exact ⟨gamma, by simp [support, hgamma]⟩
      let heights : Finset Nat := support.image fun gamma => sourceDegree S gamma.1
      have hheightsNonempty : heights.Nonempty := hsupportNonempty.image _
      let e : Nat := heights.min' hheightsNonempty
      have heMem : e ∈ heights := Finset.min'_mem heights hheightsNonempty
      obtain ⟨beta, hbetaSupport, hbetaDegree⟩ :=
        Finset.mem_image.mp heMem
      have hbetaParam : params beta ≠ 0 := by
        simpa [support] using hbetaSupport
      have hbetaPos : 0 < relativeRootSourceHeight S beta.1 := by
        have hiCast : (0 : Int) < i + 1 := by omega
        exact lt_of_lt_of_le hiCast beta.2
      have hbetaHeight : relativeRootSourceHeight S beta.1 = e := by
        calc
          relativeRootSourceHeight S beta.1 = ((relativeRootSourceHeight S beta.1).toNat : Int) :=
            (Int.toNat_of_nonneg (le_of_lt hbetaPos)).symm
          _ = (sourceDegree S beta.1 : Int) := by
            rfl
          _ = (e : Int) := by exact_mod_cast hbetaDegree
      have hie : i < e := by
        have := beta.2
        rw [hbetaHeight] at this
        omega
      have he : 0 < e := lt_trans hi hie
      have heMax : e ≤ sourceMaxDegree S := by
        have hle := sourceDegree_le_max S beta.1
        simpa [sourceDegree, hbetaHeight] using hle
      have hzeroBelow : ∀ q ∈ highWord,
          relativeRootSourceHeight S q.1 < e → q.2 = 0 := by
        intro q hq hqBelow
        rw [List.mem_map] at hq
        obtain ⟨gamma, hgammaList, rfl⟩ := hq
        by_contra hgammaParam
        have hgammaSupport : gamma ∈ support := by
          simp [support, hgammaParam]
        have hgammaHeightPos : 0 < relativeRootSourceHeight S gamma.1 := by
          have hiCast : (0 : Int) < i + 1 := by omega
          exact lt_of_lt_of_le hiCast gamma.2
        have hmin : e ≤ sourceDegree S gamma.1 := by
          apply Finset.min'_le heights (sourceDegree S gamma.1)
          exact Finset.mem_image_of_mem _ hgammaSupport
        have hcast : ((relativeRootSourceHeight S gamma.1).toNat : Int) =
            relativeRootSourceHeight S gamma.1 :=
          Int.toNat_of_nonneg (le_of_lt hgammaHeightPos)
        change e ≤ (relativeRootSourceHeight S gamma.1).toNat at hmin
        have hminCast : (e : Int) ≤ ((relativeRootSourceHeight S gamma.1).toNat : Int) := by
          exact_mod_cast hmin
        rw [hcast] at hminCast
        change relativeRootSourceHeight S gamma.1 < (e : Int) at hqBelow
        exact (not_lt_of_ge hminCast hqBelow).elim
      have hrootNe : alpha ≠ beta.1 := by
        intro heq
        have := hbetaHeight
        rw [← heq, halpha] at this
        omega
      have halphaPos : 0 < relativeRootSourceHeight S alpha := by
        rw [halpha]
        exact_mod_cast hi
      obtain ⟨u, v, hfix, hmove⟩ :=
        source_positiveRoots_exists_pairingSeparator S alpha beta.1
          halphaPos hbetaPos hrootNe
      have hfixField :
          sourceCorootPairScale S alpha beta.1 alpha u v = 1 := by
        have hfixVal :
            (u : k) ^ S.D.pairing alpha beta.1 *
              (v : k) ^ S.D.pairing alpha alpha = 1 := by
          simpa using congrArg Units.val hfix
        simpa [sourceCorootPairScale] using hfixVal
      have hscaledProduct :
          FilteredCollection.wordProduct S.C.x
              (highWord.map fun q =>
                (q.1, sourceCorootPairScale S alpha beta.1 q.1 u v * q.2)) =
            FilteredCollection.wordProduct S.C.x highWord := by
        calc
          FilteredCollection.wordProduct S.C.x
              (highWord.map fun q =>
                (q.1, sourceCorootPairScale S alpha beta.1 q.1 u v * q.2)) =
              (S.C.h beta.1 u * S.C.h alpha v)⁻¹ *
                FilteredCollection.wordProduct S.C.x highWord *
                  (S.C.h beta.1 u * S.C.h alpha v) :=
            (sourceCorootPair_conjugates_word S alpha beta.1 u v
              highWord).symm
          _ = (S.C.h beta.1 u * S.C.h alpha v)⁻¹ *
                S.C.x alpha t * (S.C.h beta.1 u * S.C.h alpha v) := by
            rw [hhighProduct]
          _ = S.C.x alpha
              (sourceCorootPairScale S alpha beta.1 alpha u v * t) :=
            sourceCorootPair_conjugates_root S alpha beta.1 alpha u v t
          _ = S.C.x alpha t := by rw [hfixField, one_mul]
          _ = FilteredCollection.wordProduct S.C.x highWord := hhighProduct.symm
      let exactDifferenceWord : List (S.D.Root × k) :=
        ((highWord.filter fun q => relativeRootSourceHeight S q.1 = e).map fun q =>
          (q.1,
            (sourceCorootPairScale S alpha beta.1 q.1 u v - 1) * q.2))
      have hexactDifferenceMem :
          FilteredCollection.wordProduct S.C.x exactDifferenceWord ∈
            sourceLayer S (e + 1) := by
        exact source_minimalHeight_difference_mem_next S e he highWord
          hzeroBelow alpha beta.1 u v hscaledProduct
      have hfilteredNodup :
          ((highWord.filter fun q => relativeRootSourceHeight S q.1 = e).map Prod.fst).Nodup := by
        have hpairNodup : highWord.Nodup := List.Nodup.of_map Prod.fst hhighNodup
        apply (hpairNodup.filter _).map_on
        intro q hq r hr hroot
        apply pair_eq_of_mem_of_root_eq S highWord hhighNodup
        · exact List.mem_of_mem_filter hq
        · exact List.mem_of_mem_filter hr
        · exact hroot
      have hexactDifferenceNodup :
          (exactDifferenceWord.map Prod.fst).Nodup := by
        simpa [exactDifferenceWord, List.map_map, Function.comp_def] using
          hfilteredNodup
      have hexactDifferenceHeight : ∀ q ∈ exactDifferenceWord,
          relativeRootSourceHeight S q.1 = e := by
        intro q hq
        rw [List.mem_map] at hq
        obtain ⟨r, hr, rfl⟩ := hq
        exact of_decide_eq_true (List.mem_filter.mp hr).2
      have hrecursive :=
        source_exactHeight_parameters_eq_zero_of_wordProduct_mem_next
          S e he exactDifferenceWord hexactDifferenceNodup
            hexactDifferenceHeight hexactDifferenceMem
      have hbetaList : beta ∈ sourceRelativeRootAtLeastList S (i + 1) :=
        sourceRelativeRootAtLeastList_mem S (i + 1) beta
      have hbetaHigh : (beta.1, params beta) ∈ highWord :=
        List.mem_map.mpr ⟨beta, hbetaList, rfl⟩
      have hbetaFiltered : (beta.1, params beta) ∈
          highWord.filter fun q => relativeRootSourceHeight S q.1 = e := by
        exact List.mem_filter.mpr ⟨hbetaHigh, by simp [hbetaHeight]⟩
      have hbetaDifference :
          (beta.1,
            (sourceCorootPairScale S alpha beta.1 beta.1 u v - 1) *
              params beta) ∈ exactDifferenceWord :=
        List.mem_map.mpr ⟨(beta.1, params beta), hbetaFiltered, rfl⟩
      have hbetaDifferenceZero := hrecursive _ hbetaDifference
      have hmoveField :
          sourceCorootPairScale S alpha beta.1 beta.1 u v ≠ 1 := by
        intro hscale
        apply hmove
        apply Units.ext
        simpa [sourceCorootPairScale] using hscale
      exact (mul_ne_zero (sub_ne_zero.mpr hmoveField) hbetaParam)
        hbetaDifferenceZero
    have hhighOne := chevalleyWord_eq_one_of_params_eq_zero S highWord (by
      intro q hq
      rw [List.mem_map] at hq
      obtain ⟨gamma, hgamma, rfl⟩ := hq
      exact hparamsZero gamma)
    have hxOne : S.C.x alpha t = 1 := by rw [← hhighProduct, hhighOne]
    have hxZero : S.C.x alpha 0 = 1 := source_chevalleyRoot_zero S alpha
    exact (S.chevalleySystem.1 alpha).1 (hxOne.trans hxZero.symm)
  exact source_exactWord_parameters_eq_zero_of_singleRoot
    S i hi hsingle word hnodup hexact hmem
termination_by sourceMaxDegree S + 1 - i
decreasing_by
  exact Nat.sub_lt_sub_left (by omega) hie

/-- Exact-height subtype form of lowest-layer extraction, intended for the
coordinate-homomorphism construction. -/
private theorem source_exactHeight_collected_parameters_eq_zero
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (i : Nat) (hi : 0 < i)
    (roots : List (SourceExactHeightRoot S i)) (hnodup : roots.Nodup)
    (params : SourceExactHeightRoot S i → k)
    (hmem : (roots.map fun alpha => S.C.x alpha.1 (params alpha)).prod ∈
      sourceLayer S (i + 1)) :
    ∀ alpha ∈ roots, params alpha = 0 := by
  classical
  let word : List (S.D.Root × k) := roots.map fun alpha =>
    (alpha.1, params alpha)
  have hwordNodup : (word.map Prod.fst).Nodup := by
    have hrootNodup := hnodup.map Subtype.val_injective
    dsimp [word]
    rw [List.map_map]
    change (roots.map fun alpha => alpha.1).Nodup
    exact hrootNodup
  have hwordExact : ∀ q ∈ word, relativeRootSourceHeight S q.1 = i := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨alpha, halpha, rfl⟩ := hq
    exact alpha.2
  have hwordProduct : FilteredCollection.wordProduct S.C.x word =
      (roots.map fun alpha => S.C.x alpha.1 (params alpha)).prod := by
    simp [word, FilteredCollection.wordProduct, List.map_map, Function.comp_def]
  have hwordMem : FilteredCollection.wordProduct S.C.x word ∈ sourceLayer S (i + 1) := by
    rw [hwordProduct]
    exact hmem
  have hzero :=
    source_exactHeight_parameters_eq_zero_of_wordProduct_mem_next
      S i hi word hwordNodup hwordExact hwordMem
  intro alpha halpha
  exact hzero (alpha.1, params alpha)
    (List.mem_map.mpr ⟨alpha, halpha, rfl⟩)

omit [IsAlgClosed k] in
/-- The adjacent quotient attached to a positive representation-source layer
is commutative. -/
public theorem relativeRootLayerQuotient_commutative
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    IsMulCommutative (relativeRootLayerQuotient S) := by
  letI : ((sourceLayer S (S.height + 1)).subgroupOf
      (sourceLayer S S.height)).Normal :=
    sourceLayer_next_normal S S.height S.height_pos
  change IsMulCommutative
    (sourceLayer S S.height ⧸
      (sourceLayer S (S.height + 1)).subgroupOf (sourceLayer S S.height))
  exact sourceLayer_quotient_commutative S S.height S.height_pos

/-- The Chevalley element in the source layer indexed by an absolute root of
exactly the source height. -/
public noncomputable def relativeRootLayerExactElement
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height}) (t : k) :
    sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
      S.height :=
  ⟨S.C.x gamma.1 t, by
    rw [sourceRelativeRootLayer, RelativeRootSeries, RootSubgroupGenerated]
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨gamma.1, ?_, ?_⟩
    · have hgamma : relativeRootSourceHeight S gamma.1 = S.height := gamma.2
      simpa [relativeRootSourceHeight] using
        (show (S.height : Int) ≤ relativeRootSourceHeight S gamma.1 by omega)
    · rw [← (S.chevalleySystem.1 gamma.1).2]
      exact ⟨t, rfl⟩⟩

omit [IsAlgClosed k] in
@[simp] public theorem relativeRootLayerExactElement_value
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height}) (t : k) :
    (relativeRootLayerExactElement S gamma t : Variety.Point K) =
      S.C.x gamma.1 t := by
  rfl

private noncomputable def relativeRootLayerQuotient_rootCoordinateHom
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height}) :
    Multiplicative k →* relativeRootLayerQuotient S := by
  let N := (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
    (S.height + 1)).subgroupOf
      (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
        S.height)
  refine
    { toFun := fun t => QuotientGroup.mk' N
        (relativeRootLayerExactElement S gamma t.toAdd)
      map_one' := ?_
      map_mul' := ?_ }
  · have hzero : S.C.x gamma.1 0 = 1 := source_chevalleyRoot_zero S gamma.1
    change QuotientGroup.mk' N (relativeRootLayerExactElement S gamma 0) = 1
    rw [show relativeRootLayerExactElement S gamma 0 = 1 by
      apply Subtype.ext
      exact hzero, map_one]
  · intro a b
    change QuotientGroup.mk' N
        (relativeRootLayerExactElement S gamma (a.toAdd + b.toAdd)) =
      QuotientGroup.mk' N (relativeRootLayerExactElement S gamma a.toAdd) *
        QuotientGroup.mk' N (relativeRootLayerExactElement S gamma b.toAdd)
    rw [← map_mul]
    apply congrArg (QuotientGroup.mk' N)
    apply Subtype.ext
    exact (S.chevalleySystem.2.2.2.1 gamma.1 a.toAdd b.toAdd).symm

omit [IsAlgClosed k] in
private lemma relativeRootLayerQuotient_rootCoordinateHom_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height}) (t : Multiplicative k) :
    relativeRootLayerQuotient_rootCoordinateHom S gamma t =
      QuotientGroup.mk'
        ((sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          (S.height + 1)).subgroupOf
            (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
              S.height))
        (relativeRootLayerExactElement S gamma t.toAdd) := by
  rfl

private noncomputable def sourceCoordinateMulEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Multiplicative ({gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} → k) ≃*
      ({gamma : S.D.Root //
        RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
          S.height} → Multiplicative k) := by
  change ({gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} → Multiplicative k) ≃*
    ({gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} → Multiplicative k)
  exact MulEquiv.refl _

omit [IsAlgClosed k] in
private lemma sourceCoordinateMulEquiv_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (a : Multiplicative ({gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} → k)) (gamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height}) :
    sourceCoordinateMulEquiv S a gamma = Multiplicative.ofAdd (a.toAdd gamma) := by
  rfl

omit [IsAlgClosed k] in
private lemma sourceCoordinateMulEquiv_single
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height}) (t : k) :
    letI : DecidableEq {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Classical.decEq _
    sourceCoordinateMulEquiv S (Multiplicative.ofAdd (Pi.single gamma t)) =
      Pi.mulSingle gamma (Multiplicative.ofAdd t) := by
  classical
  rfl

private noncomputable def relativeRootLayerQuotient_pointwiseCoordinateHom
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    ((gamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height}) → Multiplicative k) →* relativeRootLayerQuotient S := by
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Fintype.ofFinite _
  letI : DecidableEq {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Classical.decEq _
  letI : IsMulCommutative (relativeRootLayerQuotient S) :=
    relativeRootLayerQuotient_commutative S
  exact (Pi.monoidHomMulEquiv
    (fun _ : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} => Multiplicative k)
      (relativeRootLayerQuotient S)).symm
        (fun gamma => relativeRootLayerQuotient_rootCoordinateHom S gamma)

omit [IsAlgClosed k] in
private lemma relativeRootLayerQuotient_pointwiseCoordinateHom_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (a : (gamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height}) → Multiplicative k) :
    letI : Fintype S.D.Root := Fintype.ofFinite _
    letI : Fintype {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Fintype.ofFinite _
    letI : IsMulCommutative (relativeRootLayerQuotient S) :=
      relativeRootLayerQuotient_commutative S
    relativeRootLayerQuotient_pointwiseCoordinateHom S a =
      ∏ gamma : {gamma : S.D.Root //
        RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
          S.height},
        relativeRootLayerQuotient_rootCoordinateHom S gamma (a gamma) := by
  classical
  simp [relativeRootLayerQuotient_pointwiseCoordinateHom,
    Pi.monoidHomMulEquiv]

omit [IsAlgClosed k] in
private lemma relativeRootLayerQuotient_pointwiseCoordinateHom_mulSingle
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height}) (t : k) :
    letI : DecidableEq {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Classical.decEq _
    relativeRootLayerQuotient_pointwiseCoordinateHom S
        (Pi.mulSingle gamma (Multiplicative.ofAdd t)) =
      relativeRootLayerQuotient_rootCoordinateHom S gamma
        (Multiplicative.ofAdd t) := by
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Fintype.ofFinite _
  letI : DecidableEq {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Classical.decEq _
  letI : IsMulCommutative (relativeRootLayerQuotient S) :=
    relativeRootLayerQuotient_commutative S
  rw [relativeRootLayerQuotient_pointwiseCoordinateHom]
  have h := congrArg
    (fun g => g gamma)
    ((Pi.monoidHomMulEquiv
      (fun _ : {gamma : S.D.Root //
        RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
          S.height} => Multiplicative k)
        (relativeRootLayerQuotient S)).apply_symm_apply
          (fun beta => relativeRootLayerQuotient_rootCoordinateHom S beta))
  simpa [Pi.monoidHomMulEquiv] using
    DFunLike.congr_fun h (Multiplicative.ofAdd t)

/-- Multiply the exact-height Chevalley coordinates in the adjacent source
quotient. -/
public noncomputable def relativeRootLayerQuotient_coordinateHom
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Multiplicative ({gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} → k) →* relativeRootLayerQuotient S := by
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Fintype.ofFinite _
  letI : IsMulCommutative (relativeRootLayerQuotient S) :=
    relativeRootLayerQuotient_commutative S
  exact (relativeRootLayerQuotient_pointwiseCoordinateHom S).comp
    (sourceCoordinateMulEquiv S).toMonoidHom

omit [IsAlgClosed k] in
private lemma relativeRootLayerQuotient_coordinateHom_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (a : Multiplicative ({gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} → k)) :
    letI : Fintype S.D.Root := Fintype.ofFinite _
    letI : Fintype {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Fintype.ofFinite _
    letI : IsMulCommutative (relativeRootLayerQuotient S) :=
      relativeRootLayerQuotient_commutative S
    relativeRootLayerQuotient_coordinateHom S a =
      ∏ gamma : {gamma : S.D.Root //
        RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
          S.height},
        relativeRootLayerQuotient_rootCoordinateHom S gamma
          (Multiplicative.ofAdd (a.toAdd gamma)) := by
  classical
  change relativeRootLayerQuotient_pointwiseCoordinateHom S
      (sourceCoordinateMulEquiv S a) = _
  rw [relativeRootLayerQuotient_pointwiseCoordinateHom_apply]
  rfl

omit [IsAlgClosed k] in
/-- A single exact-height additive coordinate maps to the corresponding
Chevalley root class. -/
public theorem relativeRootLayerQuotient_coordinateHom_single
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height}) (t : k) :
    letI : DecidableEq {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Classical.decEq _
    relativeRootLayerQuotient_coordinateHom S
        (Multiplicative.ofAdd (Pi.single gamma t)) =
      QuotientGroup.mk'
        ((sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          (S.height + 1)).subgroupOf
            (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
              S.height))
        (relativeRootLayerExactElement S gamma t) := by
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Fintype.ofFinite _
  letI : IsMulCommutative (relativeRootLayerQuotient S) :=
    relativeRootLayerQuotient_commutative S
  rw [relativeRootLayerQuotient_coordinateHom]
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
  rw [sourceCoordinateMulEquiv_single]
  rw [relativeRootLayerQuotient_pointwiseCoordinateHom_mulSingle]
  exact relativeRootLayerQuotient_rootCoordinateHom_apply S gamma
    (Multiplicative.ofAdd t)

private noncomputable def sourceExactHeightRootList
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    List {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := by
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Fintype.ofFinite _
  exact Finset.univ.toList

private noncomputable def sourceExactHeightFactor
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (a : Multiplicative ({gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} → k))
    (gamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height}) :
    sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
      S.height :=
  relativeRootLayerExactElement S gamma (a.toAdd gamma)

private noncomputable def sourceExactHeightProduct
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (a : Multiplicative ({gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} → k)) :
    sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
      S.height :=
  ((sourceExactHeightRootList S).map (sourceExactHeightFactor S a)).prod

omit [IsAlgClosed k] in
private lemma relativeRootLayerQuotient_coordinateHom_eq_one_iff
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (a : Multiplicative ({gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} → k)) :
    relativeRootLayerQuotient_coordinateHom S a = 1 ↔
      ((sourceExactHeightProduct S a :
          sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
            S.height) : Variety.Point K) ∈
        sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          (S.height + 1) := by
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Fintype.ofFinite _
  letI : IsMulCommutative (relativeRootLayerQuotient S) :=
    relativeRootLayerQuotient_commutative S
  letI : ((sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
      (S.height + 1)).subgroupOf
        (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          S.height)).Normal := sourceRelativeRootLayer_next_normal S
  letI : IsMulCommutative
      (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
        S.height ⧸
          (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
            (S.height + 1)).subgroupOf
              (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
                S.height)) := by
    change IsMulCommutative (relativeRootLayerQuotient S)
    exact relativeRootLayerQuotient_commutative S
  rw [relativeRootLayerQuotient_coordinateHom_apply]
  simp_rw [relativeRootLayerQuotient_rootCoordinateHom_apply]
  change (∏ gamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height},
      QuotientGroup.mk'
        ((sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          (S.height + 1)).subgroupOf
            (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
              S.height))
        (sourceExactHeightFactor S a gamma)) = 1 ↔ _
  rw [← Finset.prod_map_toList]
  rw [show (Finset.univ.toList.map fun gamma =>
      QuotientGroup.mk'
        ((sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          (S.height + 1)).subgroupOf
            (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
              S.height))
        (sourceExactHeightFactor S a gamma)).prod =
      QuotientGroup.mk'
        ((sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          (S.height + 1)).subgroupOf
            (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
              S.height))
        (Finset.univ.toList.map (sourceExactHeightFactor S a)).prod by
    rw [map_list_prod]
    simp [List.map_map, Function.comp_def]]
  change QuotientGroup.mk'
      ((sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
        (S.height + 1)).subgroupOf
          (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
            S.height))
      (sourceExactHeightProduct S a) = 1 ↔ _
  change ((sourceExactHeightProduct S a :
      sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
        S.height) :
      (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
        S.height ⧸
          (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
            (S.height + 1)).subgroupOf
              (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
                S.height))) = 1 ↔ _
  simpa only [Subgroup.mem_subgroupOf] using
    (QuotientGroup.eq_one_iff
      (N := (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
        (S.height + 1)).subgroupOf
          (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
            S.height))
      (sourceExactHeightProduct S a))

/-- The exact-height coordinate homomorphism is injective. -/
public theorem relativeRootLayerQuotient_coordinateHom_injective
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Function.Injective (relativeRootLayerQuotient_coordinateHom S) := by
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Fintype.ofFinite _
  letI : IsMulCommutative (relativeRootLayerQuotient S) :=
    relativeRootLayerQuotient_commutative S
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro a ha
    have hproductMem :=
      (relativeRootLayerQuotient_coordinateHom_eq_one_iff S a).mp ha
    let roots := sourceExactHeightRootList S
    have hrootsNodup : roots.Nodup := Finset.nodup_toList _
    have hlistProductMem :
        (roots.map fun gamma => S.C.x gamma.1 (a.toAdd gamma)).prod ∈
          sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
            (S.height + 1) := by
      simpa [roots, sourceExactHeightProduct, sourceExactHeightFactor,
        relativeRootLayerExactElement, Function.comp_def] using hproductMem
    have hzero := source_exactHeight_collected_parameters_eq_zero S S.height
      S.height_pos roots hrootsNodup (fun gamma => a.toAdd gamma) hlistProductMem
    apply Multiplicative.toAdd.injective
    apply funext
    intro gamma
    simpa [roots, sourceExactHeightRootList] using hzero gamma (by
      change gamma ∈ Finset.univ.toList
      exact Finset.mem_toList.mpr (Finset.mem_univ gamma))
  · exact bot_le

omit [IsAlgClosed k] in
/-- The exact-height Chevalley coordinates generate the whole adjacent source
quotient. -/
public theorem relativeRootLayerQuotient_coordinateHom_surjective
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Function.Surjective (relativeRootLayerQuotient_coordinateHom S) := by
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Fintype.ofFinite _
  letI : DecidableEq {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Classical.decEq _
  letI : IsMulCommutative (relativeRootLayerQuotient S) :=
    relativeRootLayerQuotient_commutative S
  change ∀ q :
      (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
        S.height ⧸
          (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
            (S.height + 1)).subgroupOf
              (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
                S.height)),
    ∃ a, relativeRootLayerQuotient_coordinateHom S a = q
  let N :=
    (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
      (S.height + 1)).subgroupOf
        (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          S.height)
  letI : N.Normal := by
    dsimp only [N]
    exact sourceRelativeRootLayer_next_normal S
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  have hx' : x.1 ∈ Subgroup.closure
      (⋃ alpha ∈ {alpha | (S.height : Int) ≤
          RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J alpha},
        ↑(S.D.rootSubgroup alpha : Set (Variety.Point K))) := by
    simpa [sourceRelativeRootLayer, RelativeRootSeries,
      RootSubgroupGenerated] using x.2
  refine Subgroup.closure_induction
    (p := fun y hy => ∃ a,
      relativeRootLayerQuotient_coordinateHom S a = QuotientGroup.mk' N
      (⟨y, by
        simpa [sourceRelativeRootLayer, RelativeRootSeries,
          RootSubgroupGenerated] using hy⟩ :
        sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          S.height))
    (k := ⋃ alpha ∈ {alpha | (S.height : Int) ≤
        RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J alpha},
      ↑(S.D.rootSubgroup alpha : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hx'
  · intro y hy
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hy
    rcases hy with ⟨alpha, halpha, hyalpha⟩
    by_cases hexact :
        RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J alpha =
          S.height
    · have hyRange : y ∈ Set.range (S.C.x alpha) := by
        rw [(S.chevalleySystem.1 alpha).2]
        exact hyalpha
      obtain ⟨t, rfl⟩ := hyRange
      let gamma : {gamma : S.D.Root //
          RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
            S.height} := ⟨alpha, hexact⟩
      refine ⟨Multiplicative.ofAdd (Pi.single gamma t), ?_⟩
      rw [relativeRootLayerQuotient_coordinateHom_single S gamma t]
      apply congrArg (QuotientGroup.mk' N)
      apply Subtype.ext
      rfl
    · have hnext : (S.height + 1 : Int) ≤
          RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J alpha := by
        omega
      have hynext : y ∈ sourceRelativeRootLayer S.D
          S.D.simple.toFinite.toFinset S.coeff S.J (S.height + 1) := by
        rw [sourceRelativeRootLayer, RelativeRootSeries,
          RootSubgroupGenerated]
        apply Subgroup.subset_closure
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
        refine ⟨alpha, ?_, hyalpha⟩
        have himage : (Equiv.refl S.D.Root : S.D.Root → S.D.Root) '' S.J =
            S.J := by
          ext beta
          simp
        rw [himage]
        simp only [Equiv.refl_apply]
        omega
      refine ⟨1, ?_⟩
      rw [map_one]
      symm
      apply (QuotientGroup.eq_one_iff _).2
      exact hynext
  · refine ⟨1, ?_⟩
    rw [map_one]
    rfl
  · intro y z hy hz ihy ihz
    rcases ihy with ⟨a, ha⟩
    rcases ihz with ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [map_mul, ha, hb]
    exact (map_mul (QuotientGroup.mk' N)
      (⟨y, by
        simpa [sourceRelativeRootLayer, RelativeRootSeries,
          RootSubgroupGenerated] using hy⟩ :
        sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          S.height)
      (⟨z, by
        simpa [sourceRelativeRootLayer, RelativeRootSeries,
          RootSubgroupGenerated] using hz⟩ :
        sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          S.height)).symm
  · intro y hy ihy
    rcases ihy with ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    rw [map_inv, ha]
    exact (map_inv (QuotientGroup.mk' N)
      (⟨y, by
        simpa [sourceRelativeRootLayer, RelativeRootSeries,
          RootSubgroupGenerated] using hy⟩ :
        sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          S.height)).symm

/-- The exact-height coordinate homomorphism is bijective. -/
public theorem relativeRootLayerQuotient_coordinateHom_bijective
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Function.Bijective (relativeRootLayerQuotient_coordinateHom S) :=
  ⟨relativeRootLayerQuotient_coordinateHom_injective S,
    relativeRootLayerQuotient_coordinateHom_surjective S⟩

/-- The inverse coordinate equivalence from the adjacent source quotient to
the product of exact-height additive root coordinates. -/
public noncomputable def relativeRootLayerQuotient_coordinateEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    relativeRootLayerQuotient S ≃*
      Multiplicative ({gamma : S.D.Root //
        RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
          S.height} → k) :=
  (MulEquiv.ofBijective (relativeRootLayerQuotient_coordinateHom S)
    (relativeRootLayerQuotient_coordinateHom_bijective S)).symm

/-- The quotient class of a Chevalley root element has the corresponding
single exact-height additive coordinate. -/
public theorem relativeRootLayerQuotient_coordinateEquiv_root
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height}) (t : k) :
    letI : DecidableEq {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Classical.decEq _
    relativeRootLayerQuotient_coordinateEquiv S
        (QuotientGroup.mk'
          ((sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
            (S.height + 1)).subgroupOf
              (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
                S.height))
          (relativeRootLayerExactElement S gamma t)) =
      Multiplicative.ofAdd (Pi.single gamma t) := by
  letI : DecidableEq {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Classical.decEq _
  let e := MulEquiv.ofBijective (relativeRootLayerQuotient_coordinateHom S)
    (relativeRootLayerQuotient_coordinateHom_bijective S)
  change e.symm
      (show relativeRootLayerQuotient S from QuotientGroup.mk'
        ((sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          (S.height + 1)).subgroupOf
            (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
              S.height))
        (relativeRootLayerExactElement S gamma t)) =
    Multiplicative.ofAdd (Pi.single gamma t)
  apply e.symm_apply_eq.mpr
  exact (relativeRootLayerQuotient_coordinateHom_single S gamma t).symm

end Theory.AlgebraicGroup
