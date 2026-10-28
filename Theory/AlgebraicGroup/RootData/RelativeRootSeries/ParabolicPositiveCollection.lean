module

public import Theory.GroupTheory.FilteredCollection
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicCoordinateHom
public import Theory.AlgebraicGroup.Tori.Basic

universe u

set_option linter.style.haveILetI false

/-!
Positive relative-height Chevalley collection and lowest-layer parameter
extraction for a standard parabolic.

All actual roots of positive relative height, and more generally all roots of
height at least a fixed positive integer, are enumerated and collected using
the Chevalley system.  The rational root-addition realization identifies the
degree-one correction with actual root addition, while
`relativeRootHeight_of_validChevalleyCommutatorTerm` shows that every
commutator correction has strictly larger relative height.

For uniqueness in the lowest layer, an element of the next layer is first
collected in higher-root coordinates.  Two-coroot conjugations separate any
two distinct positive roots through a nonzero integral Cartan determinant;
choosing a detecting unit remains valid in positive characteristic.  Repeated
separation reduces finite support.  Descending induction on relative height
then proves that a collected exact-height word in the next layer has only zero
parameters.  This is the coordinate-extraction input for
`ParabolicCoordinateIndependence` and uses no Borel root-product uniqueness.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose] public noncomputable def
    StandardParabolicRelativeRootSetup.relativeHeight
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (alpha : S.D.Root) : Int :=
  RelativeRootHeight S.coeff S.rationalBase.support (S.rootEquiv '' S.J)
    (S.rootEquiv alpha)

@[expose] public def StandardParabolicRelativeRootSetup.PositiveRelativeRoot
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) :=
  {alpha : S.D.Root // 0 < S.relativeHeight alpha}

@[expose] public noncomputable def
    StandardParabolicRelativeRootSetup.positiveRelativeRootList
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) : List S.PositiveRelativeRoot := by
  letI : Finite S.PositiveRelativeRoot := by
    unfold StandardParabolicRelativeRootSetup.PositiveRelativeRoot
    infer_instance
  letI := Fintype.ofFinite S.PositiveRelativeRoot
  classical
  exact Finset.univ.toList

omit [IsAlgClosed k] in
public theorem StandardParabolicRelativeRootSetup.mem_positiveRelativeRootList
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (alpha : S.PositiveRelativeRoot) :
    alpha ∈ S.positiveRelativeRootList := by
  letI : Finite S.PositiveRelativeRoot := by
    unfold StandardParabolicRelativeRootSetup.PositiveRelativeRoot
    infer_instance
  letI := Fintype.ofFinite S.PositiveRelativeRoot
  classical
  simp [StandardParabolicRelativeRootSetup.positiveRelativeRootList]

omit [IsAlgClosed k] in
public theorem StandardParabolicRelativeRootSetup.positiveRelativeRootList_nodup
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) :
    S.positiveRelativeRootList.Nodup := by
  letI : Finite S.PositiveRelativeRoot := by
    unfold StandardParabolicRelativeRootSetup.PositiveRelativeRoot
    infer_instance
  letI := Fintype.ofFinite S.PositiveRelativeRoot
  classical
  exact Finset.nodup_toList _

omit [IsAlgClosed k] in
private lemma positiveRelativeRoots_linearlyIndependent
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
    {alpha beta : S.D.Root}
    (halpha : 0 < S.relativeHeight alpha)
    (hbeta : 0 < S.relativeHeight beta)
    (hne : alpha ≠ beta) :
    AreLinearlyIndependentRoots S.D S.rationalPairing S.rootEquiv alpha beta := by
  letI := Fintype.ofFinite S.ι
  let P := S.rationalPairing
  let _ := P.indexNeg
  have halphaPos : S.rationalBase.IsPos (S.rootEquiv alpha) :=
    base_isPos_of_relativeRootHeight_pos P S.rationalBase
      (S.rootEquiv '' S.J) S.coeff S.rationalSimpleRootExpansion halpha
  have hbetaPos : S.rationalBase.IsPos (S.rootEquiv beta) :=
    base_isPos_of_relativeRootHeight_pos P S.rationalBase
      (S.rootEquiv '' S.J) S.coeff S.rationalSimpleRootExpansion hbeta
  have hnotopp :
      P.root (S.rootEquiv alpha) ≠ -P.root (S.rootEquiv beta) := by
    intro hneg
    have hidx : S.rootEquiv alpha =
        P.reflectionPerm (S.rootEquiv beta) (S.rootEquiv beta) :=
      P.root_eq_neg_iff.mp hneg
    have halphaNeg : S.rationalBase.IsPos (-S.rootEquiv beta) := by
      simpa [hidx] using halphaPos
    exact ((RootPairing.Base.IsPos.neg_iff_not
      (P := P) (b := S.rationalBase) (i := S.rootEquiv beta)).mp
        halphaNeg) hbetaPos
  have hrootne : S.rootEquiv alpha ≠ S.rootEquiv beta :=
    fun heq => hne (S.rootEquiv.injective heq)
  have hlin : LinearIndependent ℚ
      ![P.root (S.rootEquiv alpha), P.root (S.rootEquiv beta)] :=
    RootPairing.IsReduced.linearIndependent (P := P) hrootne hnotopp
  rw [LinearIndependent.pair_iff] at hlin
  simpa [AreLinearlyIndependentRoots] using hlin

@[expose] public noncomputable def
    StandardParabolicRelativeRootSetup.relativeDegree
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (alpha : S.D.Root) : Nat :=
  (S.relativeHeight alpha).toNat

omit [IsAlgClosed k] in
private lemma validTerm_positive_and_degree_gt
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
    {alpha beta : S.D.Root}
    (halpha : 0 < S.relativeHeight alpha)
    (hbeta : 0 < S.relativeHeight beta)
    (q : ChevalleyCommutatorTerm S.D.Root)
    (hq : IsValidChevalleyCommutatorTerm S.D S.rationalPairing S.rootEquiv
      alpha beta q) :
    0 < S.relativeHeight q.root ∧
      max (S.relativeDegree alpha) (S.relativeDegree beta) <
        S.relativeDegree q.root ∧
      (q.i = 1 → q.j = 1 → S.D.add alpha beta = some q.root) := by
  letI := Fintype.ofFinite S.ι
  have hheight := relativeRootHeight_of_validChevalleyCommutatorTerm
    S.D S.rationalPairing S.rootEquiv S.rationalBase
      (S.rootEquiv '' S.J) S.coeff S.rationalSimpleRootExpansion q hq
  change S.relativeHeight q.root =
    (q.i : Int) * S.relativeHeight alpha +
      (q.j : Int) * S.relativeHeight beta at hheight
  have hqi : (1 : Int) <= q.i := by exact_mod_cast Nat.succ_le_iff.mp hq.1
  have hqj : (1 : Int) <= q.j := by exact_mod_cast Nat.succ_le_iff.mp hq.2.1
  have hqalpha : S.relativeHeight alpha < S.relativeHeight q.root := by
    rw [hheight]
    nlinarith
  have hqbeta : S.relativeHeight beta < S.relativeHeight q.root := by
    rw [hheight]
    nlinarith
  have hqpos : 0 < S.relativeHeight q.root := lt_trans halpha hqalpha
  refine ⟨hqpos, ?_, ?_⟩
  · exact max_lt ((Int.toNat_lt_toNat hqpos).mpr hqalpha)
      ((Int.toNat_lt_toNat hqpos).mpr hqbeta)
  · intro hi hj
    apply S.rationalRootAdditionRealization.add_of_root_eq_add
    simpa [hi, hj] using hq.2.2

omit [IsAlgClosed k] in
/-- Two parameters in the same positive relative-root subgroup combine by
addition. -/
public theorem standardParabolic_positiveRelativeRoot_add
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
    (alpha : S.PositiveRelativeRoot) (a b : k) :
    S.C.x alpha.1 a * S.C.x alpha.1 b = S.C.x alpha.1 (a + b) :=
  S.chevalleySystem.2.2.2.1 alpha.1 a b

omit [IsAlgClosed k] in
public theorem standardParabolic_positiveRelativeRoot_exchange
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
    (alpha beta : S.PositiveRelativeRoot)
    (a b : k) (hne : alpha ≠ beta) :
    ∃ correction : List (S.PositiveRelativeRoot × k),
      (∀ z ∈ correction,
        z.1 ∈ S.positiveRelativeRootList ∧
          max (S.relativeDegree alpha.1) (S.relativeDegree beta.1) <
            S.relativeDegree z.1.1) ∧
      S.C.x alpha.1 a * S.C.x beta.1 b =
        S.C.x beta.1 b * S.C.x alpha.1 a *
          FilteredCollection.wordProduct (fun gamma => S.C.x gamma.1)
            correction := by
  letI := Fintype.ofFinite S.ι
  have hrootne : alpha.1 ≠ beta.1 := fun heq => hne (Subtype.ext heq)
  have hLI := positiveRelativeRoots_linearlyIndependent S
    alpha.2 beta.2 hrootne
  obtain ⟨order, coeff, hnodup, hpairwise, hvalid, hcoeff, hformula⟩ :=
    S.chevalleySystem.2.2.2.2.1 alpha.1 beta.1 hLI
  let correction : List (S.PositiveRelativeRoot × k) :=
    order.attach.map fun q =>
      (⟨q.1.root, (validTerm_positive_and_degree_gt S alpha.2 beta.2 q.1
        ((hvalid q.1).mp q.2)).1⟩,
        coeff q.1 * a ^ q.1.i * b ^ q.1.j)
  refine ⟨correction, ?_, ?_⟩
  · intro z hz
    rw [List.mem_map] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    have hqdata := validTerm_positive_and_degree_gt S alpha.2 beta.2 q.1
      ((hvalid q.1).mp q.2)
    exact ⟨S.mem_positiveRelativeRootList _, hqdata.2.1⟩
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
public theorem standardParabolic_positiveRelativeRoot_collection
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
    (word : List (S.PositiveRelativeRoot × k))
    (hword : ∀ z ∈ word, z.1 ∈ S.positiveRelativeRootList) :
    ∃ params : S.PositiveRelativeRoot → k,
      FilteredCollection.wordProduct (fun alpha => S.C.x alpha.1) word =
        (S.positiveRelativeRootList.map fun alpha =>
          S.C.x alpha.1 (params alpha)).prod := by
  letI := Fintype.ofFinite S.ι
  apply FilteredCollection.filteredCollection_exists_params
    (fun alpha : S.PositiveRelativeRoot => S.relativeDegree alpha.1)
      (fun alpha : S.PositiveRelativeRoot => S.C.x alpha.1)
      S.positiveRelativeRootList
      S.positiveRelativeRootList_nodup (S.maxRelativeHeight + 1)
  · intro alpha halpha
    have hle := S.relativeHeight_le alpha.1
    change S.relativeHeight alpha.1 ≤ S.maxRelativeHeight at hle
    change (S.relativeHeight alpha.1).toNat < S.maxRelativeHeight + 1
    omega
  · intro alpha a b
    exact standardParabolic_positiveRelativeRoot_add S alpha a b
  · intro alpha beta a b halpha hbeta hne
    exact standardParabolic_positiveRelativeRoot_exchange S alpha beta a b hne
  · exact hword

@[expose] public def StandardParabolicRelativeRootSetup.RelativeRootAtLeast
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (n : Nat) :=
  {alpha : S.D.Root // (n : Int) ≤ S.relativeHeight alpha}

@[expose] public noncomputable def
    StandardParabolicRelativeRootSetup.relativeRootAtLeastList
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (n : Nat) :
    List (S.RelativeRootAtLeast n) := by
  letI : Finite (S.RelativeRootAtLeast n) := by
    unfold StandardParabolicRelativeRootSetup.RelativeRootAtLeast
    infer_instance
  letI := Fintype.ofFinite (S.RelativeRootAtLeast n)
  classical
  exact Finset.univ.toList

omit [IsAlgClosed k] in
public theorem StandardParabolicRelativeRootSetup.mem_relativeRootAtLeastList
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (n : Nat)
    (alpha : S.RelativeRootAtLeast n) :
    alpha ∈ S.relativeRootAtLeastList n := by
  letI : Finite (S.RelativeRootAtLeast n) := by
    unfold StandardParabolicRelativeRootSetup.RelativeRootAtLeast
    infer_instance
  letI := Fintype.ofFinite (S.RelativeRootAtLeast n)
  classical
  simp [StandardParabolicRelativeRootSetup.relativeRootAtLeastList]

omit [IsAlgClosed k] in
public theorem StandardParabolicRelativeRootSetup.relativeRootAtLeastList_nodup
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (n : Nat) :
    (S.relativeRootAtLeastList n).Nodup := by
  letI : Finite (S.RelativeRootAtLeast n) := by
    unfold StandardParabolicRelativeRootSetup.RelativeRootAtLeast
    infer_instance
  letI := Fintype.ofFinite (S.RelativeRootAtLeast n)
  classical
  exact Finset.nodup_toList _

omit [IsAlgClosed k] in
private theorem standardParabolic_relativeRootAtLeast_exchange
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (n : Nat) (hn : 0 < n)
    (alpha beta : S.RelativeRootAtLeast n)
    (a b : k) (hne : alpha ≠ beta) :
    ∃ correction : List (S.RelativeRootAtLeast n × k),
      (∀ z ∈ correction,
        z.1 ∈ S.relativeRootAtLeastList n ∧
          max (S.relativeDegree alpha.1) (S.relativeDegree beta.1) <
            S.relativeDegree z.1.1) ∧
      S.C.x alpha.1 a * S.C.x beta.1 b =
        S.C.x beta.1 b * S.C.x alpha.1 a *
          FilteredCollection.wordProduct (fun gamma => S.C.x gamma.1)
            correction := by
  letI := Fintype.ofFinite S.ι
  have halpha : 0 < S.relativeHeight alpha.1 := by
    have : (0 : Int) < n := by exact_mod_cast hn
    exact lt_of_lt_of_le this alpha.2
  have hbeta : 0 < S.relativeHeight beta.1 := by
    have : (0 : Int) < n := by exact_mod_cast hn
    exact lt_of_lt_of_le this beta.2
  have hrootne : alpha.1 ≠ beta.1 := fun heq => hne (Subtype.ext heq)
  have hLI := positiveRelativeRoots_linearlyIndependent S halpha hbeta hrootne
  obtain ⟨order, coeff, hnodup, hpairwise, hvalid, hcoeff, hformula⟩ :=
    S.chevalleySystem.2.2.2.2.1 alpha.1 beta.1 hLI
  have hterm (q : ChevalleyCommutatorTerm S.D.Root) (hq : q ∈ order) :
      (n : Int) ≤ S.relativeHeight q.root ∧
        max (S.relativeDegree alpha.1) (S.relativeDegree beta.1) <
          S.relativeDegree q.root := by
    have hqdata := validTerm_positive_and_degree_gt S halpha hbeta q
      ((hvalid q).mp hq)
    have halphaDegree : S.relativeDegree alpha.1 ≤ S.relativeDegree q.root :=
      le_of_lt (lt_of_le_of_lt (le_max_left _ _) hqdata.2.1)
    have hnDegree : n ≤ S.relativeDegree alpha.1 := by
      rw [StandardParabolicRelativeRootSetup.relativeDegree]
      exact (Int.le_toNat (le_trans (Int.natCast_nonneg n) alpha.2)).mpr alpha.2
    have hnqDegree : n ≤ S.relativeDegree q.root :=
      le_trans hnDegree halphaDegree
    have hqnonneg : 0 ≤ S.relativeHeight q.root := le_of_lt hqdata.1
    exact ⟨(Int.le_toNat hqnonneg).mp hnqDegree, hqdata.2.1⟩
  let correction : List (S.RelativeRootAtLeast n × k) :=
    order.attach.map fun q =>
      (⟨q.1.root, (hterm q.1 q.2).1⟩,
        coeff q.1 * a ^ q.1.i * b ^ q.1.j)
  refine ⟨correction, ?_, ?_⟩
  · intro z hz
    rw [List.mem_map] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    exact ⟨S.mem_relativeRootAtLeastList n _, (hterm q.1 q.2).2⟩
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
public theorem standardParabolic_relativeRootAtLeast_collection
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (n : Nat) (hn : 0 < n)
    (word : List (S.RelativeRootAtLeast n × k))
    (hword : ∀ z ∈ word, z.1 ∈ S.relativeRootAtLeastList n) :
    ∃ params : S.RelativeRootAtLeast n → k,
      FilteredCollection.wordProduct (fun alpha => S.C.x alpha.1) word =
        ((S.relativeRootAtLeastList n).map fun alpha =>
          S.C.x alpha.1 (params alpha)).prod := by
  letI := Fintype.ofFinite S.ι
  apply FilteredCollection.filteredCollection_exists_params
    (fun alpha : S.RelativeRootAtLeast n => S.relativeDegree alpha.1)
      (fun alpha : S.RelativeRootAtLeast n => S.C.x alpha.1)
      (S.relativeRootAtLeastList n)
      (S.relativeRootAtLeastList_nodup n) (S.maxRelativeHeight + 1)
  · intro alpha halpha
    have hle := S.relativeHeight_le alpha.1
    change S.relativeHeight alpha.1 ≤ S.maxRelativeHeight at hle
    change (S.relativeHeight alpha.1).toNat < S.maxRelativeHeight + 1
    omega
  · intro alpha a b
    exact S.chevalleySystem.2.2.2.1 alpha.1 a b
  · intro alpha beta a b halpha hbeta hne
    exact standardParabolic_relativeRootAtLeast_exchange S n hn alpha beta a b hne
  · exact hword

omit [IsAlgClosed k] in
private lemma chevalleyRoot_zero
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (alpha : S.D.Root) :
    S.C.x alpha 0 = 1 := by
  simpa using S.chevalleySystem.2.2.2.1 alpha 0 0

omit [IsAlgClosed k] in
private lemma chevalleyRoot_neg
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (alpha : S.D.Root) (a : k) :
    S.C.x alpha (-a) = (S.C.x alpha a)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [S.chevalleySystem.2.2.2.1]
  simpa using chevalleyRoot_zero S alpha

omit [IsAlgClosed k] in
public theorem standardParabolic_layer_exists_word
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (n : Nat) (_hn : 0 < n)
    (z : Variety.Point K) (hz : z ∈ S.layer n) :
    ∃ word : List (S.RelativeRootAtLeast n × k),
      (∀ q ∈ word, q.1 ∈ S.relativeRootAtLeastList n) ∧
      z = FilteredCollection.wordProduct (fun alpha => S.C.x alpha.1) word := by
  classical
  have hwordInv : ∀ word : List (S.RelativeRootAtLeast n × k),
      (FilteredCollection.wordProduct (fun alpha => S.C.x alpha.1) word)⁻¹ =
        FilteredCollection.wordProduct (fun alpha => S.C.x alpha.1)
          (word.reverse.map fun q => (q.1, -q.2)) := by
    intro word
    let f : S.RelativeRootAtLeast n × k → Variety.Point K :=
      fun q => S.C.x q.1.1 q.2
    let negParam : S.RelativeRootAtLeast n × k →
        S.RelativeRootAtLeast n × k := fun q => (q.1, -q.2)
    have hneg (q : S.RelativeRootAtLeast n × k) :
        f (negParam q) = (f q)⁻¹ := by
      exact chevalleyRoot_neg S q.1.1 q.2
    change (word.map f).prod⁻¹ =
      ((word.reverse.map negParam).map f).prod
    induction word with
    | nil => simp
    | cons q tail ih =>
        simp only [List.map_cons, List.prod_cons, List.reverse_cons,
          List.map_append, List.map_map, List.prod_append, mul_inv_rev]
        rw [ih, hneg]
        simp [Function.comp_def]
  rw [StandardParabolicRelativeRootSetup.layer, RelativeRootSeries,
    RootSubgroupGenerated] at hz
  refine Subgroup.closure_induction
    (p := fun z _ => ∃ word : List (S.RelativeRootAtLeast n × k),
      (∀ q ∈ word, q.1 ∈ S.relativeRootAtLeastList n) ∧
      z = FilteredCollection.wordProduct (fun alpha => S.C.x alpha.1) word)
    (k := ⋃ alpha ∈ {alpha | (n : Int) ≤ S.relativeHeight alpha},
      (S.D.rootSubgroup alpha : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hz
  · intro x hx
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hx
    obtain ⟨alpha, halpha, hxalpha⟩ := hx
    have hxRange : x ∈ Set.range (S.C.x alpha) := by
      rw [(S.chevalleySystem.1 alpha).2]
      exact hxalpha
    obtain ⟨t, rfl⟩ := hxRange
    let alpha' : S.RelativeRootAtLeast n := ⟨alpha, halpha⟩
    refine ⟨[(alpha', t)], ?_, ?_⟩
    · simp [S.mem_relativeRootAtLeastList n alpha']
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
public theorem standardParabolic_layer_exists_collected
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (n : Nat) (hn : 0 < n)
    (z : Variety.Point K) (hz : z ∈ S.layer n) :
    ∃ params : S.RelativeRootAtLeast n → k,
      z = ((S.relativeRootAtLeastList n).map fun alpha =>
        S.C.x alpha.1 (params alpha)).prod := by
  obtain ⟨word, hword, rfl⟩ := standardParabolic_layer_exists_word S n hn z hz
  obtain ⟨params, hparams⟩ :=
    standardParabolic_relativeRootAtLeast_collection S n hn word hword
  exact ⟨params, hparams⟩

public theorem standardParabolic_positiveRoots_exists_pairingSeparator
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
    (alpha beta : S.D.Root)
    (halpha : 0 < S.relativeHeight alpha)
    (hbeta : 0 < S.relativeHeight beta)
    (hne : alpha ≠ beta) :
    ∃ u v : kˣ,
      u ^ S.D.pairing alpha beta * v ^ S.D.pairing alpha alpha = 1 ∧
      u ^ S.D.pairing beta beta * v ^ S.D.pairing beta alpha ≠ 1 := by
  letI := Fintype.ofFinite S.ι
  let P := S.rationalPairing
  let _ := P.indexNeg
  have halphaPos : S.rationalBase.IsPos (S.rootEquiv alpha) :=
    base_isPos_of_relativeRootHeight_pos P S.rationalBase
      (S.rootEquiv '' S.J) S.coeff S.rationalSimpleRootExpansion halpha
  have hbetaPos : S.rationalBase.IsPos (S.rootEquiv beta) :=
    base_isPos_of_relativeRootHeight_pos P S.rationalBase
      (S.rootEquiv '' S.J) S.coeff S.rationalSimpleRootExpansion hbeta
  have hnotopp :
      P.root (S.rootEquiv alpha) ≠ -P.root (S.rootEquiv beta) := by
    intro hneg
    have hidx : S.rootEquiv alpha =
        P.reflectionPerm (S.rootEquiv beta) (S.rootEquiv beta) :=
      P.root_eq_neg_iff.mp hneg
    have halphaNeg : S.rationalBase.IsPos (-S.rootEquiv beta) := by
      simpa [hidx] using halphaPos
    exact ((RootPairing.Base.IsPos.neg_iff_not
      (P := P) (b := S.rationalBase) (i := S.rootEquiv beta)).mp
        halphaNeg) hbetaPos
  have hweightNe : S.D.rootWeight alpha ≠ S.D.rootWeight beta := fun hw =>
    hne (S.standardParabolic.1.2.1.1 hw)
  have hrootNe : S.rootEquiv alpha ≠ S.rootEquiv beta := by
    intro heq
    apply hweightNe
    rw [← S.actualRootDatum.2.1 alpha, ← S.actualRootDatum.2.1 beta, heq]
  have hlin : LinearIndependent ℚ
      ![P.root (S.rootEquiv alpha), P.root (S.rootEquiv beta)] :=
    RootPairing.IsReduced.linearIndependent (P := P) hrootNe hnotopp
  have hcox : P.coxeterWeight (S.rootEquiv alpha) (S.rootEquiv beta) ≠ 4 :=
    (P.linearIndependent_iff_coxeterWeight_ne_four).mp hlin
  let z : Int := 4 - S.D.pairing alpha beta * S.D.pairing beta alpha
  have hz : z ≠ 0 := by
    intro hz0
    apply hcox
    rw [RootPairing.coxeterWeight, ← S.rationalRootRealization.1 alpha beta,
      ← S.rationalRootRealization.1 beta alpha]
    have hzprod : S.D.pairing alpha beta * S.D.pairing beta alpha = 4 := by
      dsimp [z] at hz0
      omega
    exact_mod_cast hzprod
  obtain ⟨c, hc⟩ := exists_unit_zpow_ne_one (k := k) hz
  let a := S.D.pairing alpha beta
  let b := S.D.pairing beta alpha
  refine ⟨c ^ (2 : Int), c ^ (-a), ?_, ?_⟩
  · rw [S.standardParabolic.1.2.1.2.2.2.2.2.2.1 alpha]
    dsimp [a]
    rw [← zpow_mul, ← zpow_mul, ← zpow_add]
    convert zpow_zero c using 1
    all_goals ring_nf
  · rw [S.standardParabolic.1.2.1.2.2.2.2.2.2.1 beta]
    dsimp [a, b, z] at hc ⊢
    rw [← zpow_mul, ← zpow_mul, ← zpow_add]
    convert hc using 1
    all_goals ring_nf

@[expose] public def standardParabolic_corootPairScale
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
    (alpha beta gamma : S.D.Root) (u v : kˣ) : k :=
  (u : k) ^ S.D.pairing gamma beta *
    (v : k) ^ S.D.pairing gamma alpha

omit [IsAlgClosed k] in
public theorem standardParabolic_corootPair_conjugates_root
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
    (alpha beta gamma : S.D.Root) (u v : kˣ) (t : k) :
    (S.C.h beta u * S.C.h alpha v)⁻¹ * S.C.x gamma t *
        (S.C.h beta u * S.C.h alpha v) =
      S.C.x gamma (standardParabolic_corootPairScale S alpha beta gamma u v * t) := by
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
      simp only [standardParabolic_corootPairScale]
      ring

omit [IsAlgClosed k] in
private theorem standardParabolic_corootPair_conjugates_word
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
    (alpha beta : S.D.Root) (u v : kˣ)
    (word : List (S.D.Root × k)) :
    (S.C.h beta u * S.C.h alpha v)⁻¹ *
        FilteredCollection.wordProduct S.C.x word *
          (S.C.h beta u * S.C.h alpha v) =
      FilteredCollection.wordProduct S.C.x
        (word.map fun q =>
          (q.1, standardParabolic_corootPairScale S alpha beta q.1 u v * q.2)) := by
  induction word with
  | nil => simp [FilteredCollection.wordProduct]
  | cons q tail ih =>
      rw [show FilteredCollection.wordProduct S.C.x (q :: tail) =
          S.C.x q.1 q.2 * FilteredCollection.wordProduct S.C.x tail by rfl]
      rw [show FilteredCollection.wordProduct S.C.x
          ((q :: tail).map fun r =>
            (r.1, standardParabolic_corootPairScale S alpha beta r.1 u v * r.2)) =
          S.C.x q.1 (standardParabolic_corootPairScale S alpha beta q.1 u v * q.2) *
            FilteredCollection.wordProduct S.C.x
              (tail.map fun r =>
                (r.1, standardParabolic_corootPairScale S alpha beta r.1 u v * r.2)) by rfl]
      calc
        (S.C.h beta u * S.C.h alpha v)⁻¹ *
            (S.C.x q.1 q.2 * FilteredCollection.wordProduct S.C.x tail) *
              (S.C.h beta u * S.C.h alpha v) =
            ((S.C.h beta u * S.C.h alpha v)⁻¹ * S.C.x q.1 q.2 *
              (S.C.h beta u * S.C.h alpha v)) *
            ((S.C.h beta u * S.C.h alpha v)⁻¹ *
              FilteredCollection.wordProduct S.C.x tail *
                (S.C.h beta u * S.C.h alpha v)) := by group
        _ = _ := by
          rw [standardParabolic_corootPair_conjugates_root, ih]

omit [IsAlgClosed k] in
private theorem chevalleyRoot_mem_layer
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (n : Nat)
    (alpha : S.D.Root) (t : k)
    (halpha : (n : Int) ≤ S.relativeHeight alpha) :
    S.C.x alpha t ∈ S.layer n := by
  rw [StandardParabolicRelativeRootSetup.layer, RelativeRootSeries,
    RootSubgroupGenerated]
  apply Subgroup.subset_closure
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨alpha, halpha, ?_⟩
  rw [← (S.chevalleySystem.1 alpha).2]
  exact ⟨t, rfl⟩

omit [IsAlgClosed k] in
private theorem standardParabolic_corootPair_conjugates_layer
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (n : Nat) (hn : 0 < n)
    (alpha beta : S.D.Root) (u v : kˣ)
    (z : Variety.Point K) (hz : z ∈ S.layer n) :
    (S.C.h beta u * S.C.h alpha v)⁻¹ * z *
      (S.C.h beta u * S.C.h alpha v) ∈ S.layer n := by
  obtain ⟨word, hword, rfl⟩ := standardParabolic_layer_exists_word S n hn z hz
  let rawWord : List (S.D.Root × k) := word.map fun q => (q.1.1, q.2)
  have hraw : FilteredCollection.wordProduct
      (fun gamma : S.RelativeRootAtLeast n => S.C.x gamma.1) word =
      FilteredCollection.wordProduct S.C.x rawWord := by
    simp [rawWord, FilteredCollection.wordProduct, List.map_map,
      Function.comp_def]
  rw [hraw, standardParabolic_corootPair_conjugates_word]
  apply Subgroup.list_prod_mem
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  rw [List.mem_map] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  rw [List.mem_map] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  exact chevalleyRoot_mem_layer S n s.1.1 _ s.1.2

omit [IsAlgClosed k] in
private theorem standardParabolic_exactWord_difference_mem_next
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : Nat) (hi : 0 < i)
    (word : List (S.D.Root × k))
    (hexact : ∀ q ∈ word, S.relativeHeight q.1 = i)
    (alpha beta : S.D.Root) (u v : kˣ)
    (hrelation :
      FilteredCollection.wordProduct S.C.x
          (word.map fun q =>
            (q.1, standardParabolic_corootPairScale S alpha beta q.1 u v * q.2)) *
        (FilteredCollection.wordProduct S.C.x word)⁻¹ ∈ S.layer (i + 1)) :
    FilteredCollection.wordProduct S.C.x
      (word.map fun q =>
        (q.1,
          (standardParabolic_corootPairScale S alpha beta q.1 u v - 1) * q.2)) ∈
        S.layer (i + 1) := by
  classical
  let hN := standardParabolicRelativeRootLayer_next_normal S i hi
  letI := hN
  let hcomm := standardParabolicRelativeRootLayer_quotient_commutative S i hi
  letI := hcomm
  let N := (S.layer (i + 1)).subgroupOf (S.layer i)
  let Q := S.layer i ⧸ N
  have horigLayer : FilteredCollection.wordProduct S.C.x word ∈ S.layer i := by
    apply Subgroup.list_prod_mem
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact chevalleyRoot_mem_layer S i q.1 q.2 (by rw [hexact q hq])
  have hscaledLayer : FilteredCollection.wordProduct S.C.x
      (word.map fun q =>
        (q.1, standardParabolic_corootPairScale S alpha beta q.1 u v * q.2)) ∈
      S.layer i := by
    apply Subgroup.list_prod_mem
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    rw [List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    exact chevalleyRoot_mem_layer S i r.1 _ (by rw [hexact r hr])
  let original (q : {q // q ∈ word}) : Q :=
    QuotientGroup.mk' N
      ⟨S.C.x q.1.1 q.1.2, chevalleyRoot_mem_layer S i q.1.1 q.1.2 (by
        rw [hexact q.1 q.2])⟩
  let scaled (q : {q // q ∈ word}) : Q :=
    QuotientGroup.mk' N
      ⟨S.C.x q.1.1
          (standardParabolic_corootPairScale S alpha beta q.1.1 u v * q.1.2),
        chevalleyRoot_mem_layer S i q.1.1 _ (by rw [hexact q.1 q.2])⟩
  let difference (q : {q // q ∈ word}) : Q :=
    QuotientGroup.mk' N
      ⟨S.C.x q.1.1
          ((standardParabolic_corootPairScale S alpha beta q.1.1 u v - 1) *
            q.1.2),
        chevalleyRoot_mem_layer S i q.1.1 _ (by rw [hexact q.1 q.2])⟩
  have hfactor (q : {q // q ∈ word}) :
      difference q = scaled q * (original q)⁻¹ := by
    have hparam :
        (standardParabolic_corootPairScale S alpha beta q.1.1 u v - 1) * q.1.2 =
          standardParabolic_corootPairScale S alpha beta q.1.1 u v * q.1.2 +
            (-q.1.2) := by ring
    have hx : S.C.x q.1.1
        ((standardParabolic_corootPairScale S alpha beta q.1.1 u v - 1) * q.1.2) =
        S.C.x q.1.1
          (standardParabolic_corootPairScale S alpha beta q.1.1 u v * q.1.2) *
            (S.C.x q.1.1 q.1.2)⁻¹ := by
      rw [hparam, ← S.chevalleySystem.2.2.2.1, chevalleyRoot_neg S]
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
              chevalleyRoot_mem_layer S i q.1.1 q.1.2 (by
                rw [hexact q.1 q.2])⟩ : S.layer i)).map
              (QuotientGroup.mk' N)).prod := by
            simp only [List.map_map]
            rfl
      _ = QuotientGroup.mk' N
          (word.attach.map fun q =>
            (⟨S.C.x q.1.1 q.1.2,
              chevalleyRoot_mem_layer S i q.1.1 q.1.2 (by
                rw [hexact q.1 q.2])⟩ : S.layer i)).prod :=
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
              (q.1, standardParabolic_corootPairScale S alpha beta q.1 u v * q.2)),
            hscaledLayer⟩ := by
    calc
      (word.attach.map scaled).prod =
          ((word.attach.map fun q =>
            (⟨S.C.x q.1.1
                (standardParabolic_corootPairScale S alpha beta q.1.1 u v * q.1.2),
              chevalleyRoot_mem_layer S i q.1.1 _ (by
                rw [hexact q.1 q.2])⟩ : S.layer i)).map
              (QuotientGroup.mk' N)).prod := by
            simp only [List.map_map]
            rfl
      _ = QuotientGroup.mk' N
          (word.attach.map fun q =>
            (⟨S.C.x q.1.1
                (standardParabolic_corootPairScale S alpha beta q.1.1 u v * q.1.2),
              chevalleyRoot_mem_layer S i q.1.1 _ (by
                rw [hexact q.1 q.2])⟩ : S.layer i)).prod :=
            (map_list_prod (QuotientGroup.mk' N) _).symm
      _ = QuotientGroup.mk' N
          ⟨FilteredCollection.wordProduct S.C.x
            (word.map fun q =>
              (q.1, standardParabolic_corootPairScale S alpha beta q.1 u v * q.2)),
            hscaledLayer⟩ := by
            apply congrArg (QuotientGroup.mk' N)
            apply Subtype.ext
            rw [SubmonoidClass.coe_list_prod]
            simp only [List.map_map]
            rw [FilteredCollection.wordProduct]
            simp only [List.map_map]
            change (word.attach.map fun q => S.C.x q.1.1
              (standardParabolic_corootPairScale S alpha beta q.1.1 u v *
                q.1.2)).prod = _
            exact congrArg List.prod (List.attach_map_val
              (l := word)
              (f := fun q => S.C.x q.1
                (standardParabolic_corootPairScale S alpha beta q.1 u v * q.2)))
  have hrelationOne :
      (word.attach.map scaled).prod * (word.attach.map original).prod⁻¹ = 1 := by
    rw [hscaled', horiginal, ← map_inv, ← map_mul]
    exact (QuotientGroup.eq_one_iff (N := N)
      (⟨FilteredCollection.wordProduct S.C.x
          (word.map fun q : S.D.Root × k =>
            (q.1, standardParabolic_corootPairScale S alpha beta q.1 u v * q.2)) *
        (FilteredCollection.wordProduct S.C.x word)⁻¹, by
          exact S.layer i |>.mul_mem hscaledLayer (S.layer i |>.inv_mem horigLayer)⟩ :
        S.layer i)).2 hrelation
  have hdifferenceOne : (word.attach.map difference).prod = 1 := by
    rw [hprod, hrelationOne]
  let differencePoint : S.layer i :=
    ⟨FilteredCollection.wordProduct S.C.x
      (word.map fun q =>
        (q.1,
          (standardParabolic_corootPairScale S alpha beta q.1 u v - 1) * q.2)), by
      apply Subgroup.list_prod_mem
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      rw [List.mem_map] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      exact chevalleyRoot_mem_layer S i r.1 _ (by rw [hexact r hr])⟩
  have hdifference :
      (word.attach.map difference).prod = QuotientGroup.mk' N differencePoint := by
    calc
      (word.attach.map difference).prod =
          ((word.attach.map fun q =>
            (⟨S.C.x q.1.1
                ((standardParabolic_corootPairScale S alpha beta q.1.1 u v - 1) *
                  q.1.2),
              chevalleyRoot_mem_layer S i q.1.1 _ (by
                rw [hexact q.1 q.2])⟩ : S.layer i)).map
              (QuotientGroup.mk' N)).prod := by
            simp only [List.map_map]
            rfl
      _ = QuotientGroup.mk' N
          (word.attach.map fun q =>
            (⟨S.C.x q.1.1
                ((standardParabolic_corootPairScale S alpha beta q.1.1 u v - 1) *
                  q.1.2),
              chevalleyRoot_mem_layer S i q.1.1 _ (by
                rw [hexact q.1 q.2])⟩ : S.layer i)).prod :=
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
              ((standardParabolic_corootPairScale S alpha beta q.1.1 u v - 1) *
                q.1.2)).prod = _
            exact congrArg List.prod (List.attach_map_val
              (l := word)
              (f := fun q => S.C.x q.1
                ((standardParabolic_corootPairScale S alpha beta q.1 u v - 1) * q.2)))
  rw [hdifference] at hdifferenceOne
  exact (QuotientGroup.eq_one_iff (N := N) differencePoint).1 hdifferenceOne

omit [IsAlgClosed k] in
private theorem standardParabolic_word_mul_exactHeightPart_inv_mem_next
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (e : Nat) (he : 0 < e)
    (word : List (S.D.Root × k))
    (hzeroBelow : ∀ q ∈ word, S.relativeHeight q.1 < e → q.2 = 0) :
    FilteredCollection.wordProduct S.C.x word *
        (FilteredCollection.wordProduct S.C.x
          (word.filter fun q => S.relativeHeight q.1 = e))⁻¹ ∈
      S.layer (e + 1) := by
  classical
  let hN := standardParabolicRelativeRootLayer_next_normal S e he
  induction word with
  | nil => simp [FilteredCollection.wordProduct]
  | cons q tail ih =>
      have hzeroTail : ∀ r ∈ tail, S.relativeHeight r.1 < e → r.2 = 0 := by
        intro r hr
        exact hzeroBelow r (by simp [hr])
      have ih' := ih hzeroTail
      have hqLayer : S.C.x q.1 q.2 ∈ S.layer e := by
        by_cases hle : (e : Int) ≤ S.relativeHeight q.1
        · exact chevalleyRoot_mem_layer S e q.1 q.2 hle
        · have hqzero := hzeroBelow q (by simp) (by omega)
          rw [hqzero, chevalleyRoot_zero S]
          exact Subgroup.one_mem _
      by_cases hqExact : S.relativeHeight q.1 = e
      · have hconj := hN.conj_mem
          (⟨FilteredCollection.wordProduct S.C.x tail *
              (FilteredCollection.wordProduct S.C.x
                (tail.filter fun r => S.relativeHeight r.1 = e))⁻¹,
            standardParabolicRelativeRootLayer_succ_le S e ih'⟩ : S.layer e)
          ih' (⟨S.C.x q.1 q.2, hqLayer⟩ : S.layer e)
        change S.C.x q.1 q.2 *
            (FilteredCollection.wordProduct S.C.x tail *
              (FilteredCollection.wordProduct S.C.x
                (tail.filter fun r => S.relativeHeight r.1 = e))⁻¹) *
              (S.C.x q.1 q.2)⁻¹ ∈ S.layer (e + 1) at hconj
        simpa [FilteredCollection.wordProduct, hqExact, mul_inv_rev, mul_assoc]
          using hconj
      · have hqNotBelowOrAbove :
            S.relativeHeight q.1 < e ∨ (e + 1 : Int) ≤ S.relativeHeight q.1 := by
          omega
        rcases hqNotBelowOrAbove with hqBelow | hqAbove
        · have hqzero := hzeroBelow q (by simp) hqBelow
          simpa [FilteredCollection.wordProduct, hqExact, hqzero,
            chevalleyRoot_zero S] using ih'
        · have hqNext : S.C.x q.1 q.2 ∈ S.layer (e + 1) :=
            chevalleyRoot_mem_layer S (e + 1) q.1 q.2 hqAbove
          have hmul := (S.layer (e + 1)).mul_mem hqNext ih'
          simpa [FilteredCollection.wordProduct, hqExact, mul_assoc] using hmul

omit [IsAlgClosed k] in
private theorem standardParabolic_minimalHeight_difference_mem_next
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (e : Nat) (he : 0 < e)
    (word : List (S.D.Root × k))
    (hzeroBelow : ∀ q ∈ word, S.relativeHeight q.1 < e → q.2 = 0)
    (alpha beta : S.D.Root) (u v : kˣ)
    (heq : FilteredCollection.wordProduct S.C.x
      (word.map fun q =>
        (q.1, standardParabolic_corootPairScale S alpha beta q.1 u v * q.2)) =
      FilteredCollection.wordProduct S.C.x word) :
    FilteredCollection.wordProduct S.C.x
      ((word.filter fun q => S.relativeHeight q.1 = e).map fun q =>
        (q.1,
          (standardParabolic_corootPairScale S alpha beta q.1 u v - 1) * q.2)) ∈
      S.layer (e + 1) := by
  classical
  let scaledWord := word.map fun q =>
    (q.1, standardParabolic_corootPairScale S alpha beta q.1 u v * q.2)
  let exactWord := word.filter fun q => S.relativeHeight q.1 = e
  have hscaledZeroBelow : ∀ q ∈ scaledWord,
      S.relativeHeight q.1 < e → q.2 = 0 := by
    intro q hq hqBelow
    rw [List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    rw [hzeroBelow r hr hqBelow, mul_zero]
  have horigApprox :=
    standardParabolic_word_mul_exactHeightPart_inv_mem_next S e he word hzeroBelow
  have hscaledApprox :=
    standardParabolic_word_mul_exactHeightPart_inv_mem_next S e he scaledWord
      hscaledZeroBelow
  have hfilter :
      scaledWord.filter (fun q => S.relativeHeight q.1 = e) =
        exactWord.map fun q =>
          (q.1, standardParabolic_corootPairScale S alpha beta q.1 u v * q.2) := by
    dsimp [scaledWord, exactWord]
    rw [List.filter_map]
    rfl
  have hrelation :
      FilteredCollection.wordProduct S.C.x
          (exactWord.map fun q =>
            (q.1, standardParabolic_corootPairScale S alpha beta q.1 u v * q.2)) *
        (FilteredCollection.wordProduct S.C.x exactWord)⁻¹ ∈ S.layer (e + 1) := by
    have hmul := (S.layer (e + 1)).mul_mem
      ((S.layer (e + 1)).inv_mem hscaledApprox) horigApprox
    rw [hfilter] at hmul
    dsimp [exactWord] at hmul ⊢
    convert hmul using 1
    all_goals
      rw [heq]
      group
  apply standardParabolic_exactWord_difference_mem_next S e he exactWord
  · intro q hq
    dsimp [exactWord] at hq
    exact of_decide_eq_true (List.mem_filter.mp hq |>.2)
  · exact hrelation

omit [IsAlgClosed k] in
private theorem chevalleyWord_eq_one_of_params_eq_zero
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
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
      rw [hq, chevalleyRoot_zero S, ih htail, one_mul]

omit [IsAlgClosed k] in
private theorem chevalleyWord_eq_single_of_other_params_eq_zero
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
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
        rw [hrzero, chevalleyRoot_zero S, one_mul, ih hqtail hnodup'.2 htail]

private noncomputable def nonzeroRootSupport
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
    (word : List (S.D.Root × k)) : Finset S.D.Root := by
  classical
  exact (word.toFinset.filter fun q => q.2 ≠ 0).image Prod.fst

omit [IsAlgClosed k] in
private theorem mem_nonzeroRootSupport_iff
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
    (word : List (S.D.Root × k)) (alpha : S.D.Root) :
    alpha ∈ nonzeroRootSupport S word ↔
      ∃ q ∈ word, q.1 = alpha ∧ q.2 ≠ 0 := by
  classical
  simp [nonzeroRootSupport]

omit [IsAlgClosed k] in
private theorem pair_eq_of_mem_of_root_eq
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K)
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

private theorem standardParabolic_exactWord_parameters_eq_zero_of_singleRoot
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : Nat) (hi : 0 < i)
    (hsingle : ∀ alpha t,
      S.relativeHeight alpha = i → S.C.x alpha t ∈ S.layer (i + 1) → t = 0)
    (word : List (S.D.Root × k))
    (hnodup : (word.map Prod.fst).Nodup)
    (hexact : ∀ q ∈ word, S.relativeHeight q.1 = i)
    (hmem : FilteredCollection.wordProduct S.C.x word ∈ S.layer (i + 1)) :
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
      have hqaMem : S.C.x qa.1 qa.2 ∈ S.layer (i + 1) := by
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
      have halphaPos : 0 < S.relativeHeight qa.1 := by
        rw [hexact qa hqa]
        exact_mod_cast hi
      have hbetaPos : 0 < S.relativeHeight qb.1 := by
        rw [hexact qb hqb]
        exact_mod_cast hi
      have hrootNe : qa.1 ≠ qb.1 := by
        rw [hqaRoot, hqbRoot]
        exact hbetaNe.symm
      obtain ⟨u, v, hfix, hmove⟩ :=
        standardParabolic_positiveRoots_exists_pairingSeparator S qa.1 qb.1
          halphaPos hbetaPos hrootNe
      let differenceWord := word.map fun q =>
        (q.1,
          (standardParabolic_corootPairScale S qa.1 qb.1 q.1 u v - 1) * q.2)
      have hscaledMem :
          FilteredCollection.wordProduct S.C.x
              (word.map fun q =>
                (q.1, standardParabolic_corootPairScale S qa.1 qb.1 q.1 u v * q.2)) ∈
            S.layer (i + 1) := by
        have hconj := standardParabolic_corootPair_conjugates_layer S (i + 1)
          (by omega) qa.1 qb.1 u v
            (FilteredCollection.wordProduct S.C.x word) hmem
        rw [standardParabolic_corootPair_conjugates_word] at hconj
        exact hconj
      have hrelation :
          FilteredCollection.wordProduct S.C.x
              (word.map fun q =>
                (q.1, standardParabolic_corootPairScale S qa.1 qb.1 q.1 u v * q.2)) *
            (FilteredCollection.wordProduct S.C.x word)⁻¹ ∈ S.layer (i + 1) :=
        (S.layer (i + 1)).mul_mem hscaledMem ((S.layer (i + 1)).inv_mem hmem)
      have hdifferenceMem :
          FilteredCollection.wordProduct S.C.x differenceWord ∈ S.layer (i + 1) := by
        exact standardParabolic_exactWord_difference_mem_next S i hi word hexact
          qa.1 qb.1 u v hrelation
      have hdifferenceNodup : (differenceWord.map Prod.fst).Nodup := by
        simpa [differenceWord, List.map_map, Function.comp_def] using hnodup
      have hdifferenceExact : ∀ q ∈ differenceWord,
          S.relativeHeight q.1 = i := by
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
        rw [standardParabolic_corootPairScale, hfixField, sub_self, zero_mul]
      have hqaOriginal : qa.1 ∈ nonzeroRootSupport S word :=
        (mem_nonzeroRootSupport_iff S word qa.1).2
          ⟨qa, hqa, rfl, hqaNonzero⟩
      have hproper : nonzeroRootSupport S differenceWord ⊂
          nonzeroRootSupport S word :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hsupportSubset, fun heq =>
          hqaNotDifference (heq.symm ▸ hqaOriginal)⟩
      have hrec := standardParabolic_exactWord_parameters_eq_zero_of_singleRoot
        S i hi hsingle differenceWord hdifferenceNodup hdifferenceExact hdifferenceMem
      have hqbDifference :
          (qb.1,
            (standardParabolic_corootPairScale S qa.1 qb.1 qb.1 u v - 1) * qb.2) ∈
            differenceWord := by
        exact List.mem_map.mpr ⟨qb, hqb, rfl⟩
      have hbetaDifferenceZero := hrec _ hqbDifference
      have hmoveField :
          standardParabolic_corootPairScale S qa.1 qb.1 qb.1 u v ≠ 1 := by
        intro heq
        apply hmove
        apply Units.ext
        simpa [standardParabolic_corootPairScale] using heq
      exact False.elim ((mul_ne_zero (sub_ne_zero.mpr hmoveField) hqbNonzero)
        hbetaDifferenceZero)
termination_by (nonzeroRootSupport S word).card
decreasing_by exact Finset.card_lt_card hproper

/-- A collected word with one factor for each root of exact positive relative
height has no nonzero parameter when its product lies in the next layer. -/
public theorem standardParabolic_exactHeight_parameters_eq_zero_of_wordProduct_mem_next
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : Nat) (hi : 0 < i)
    (word : List (S.D.Root × k))
    (hnodup : (word.map Prod.fst).Nodup)
    (hexact : ∀ q ∈ word, S.relativeHeight q.1 = i)
    (hmem : FilteredCollection.wordProduct S.C.x word ∈ S.layer (i + 1)) :
    ∀ q ∈ word, q.2 = 0 := by
  classical
  have hsingle : ∀ alpha t,
      S.relativeHeight alpha = i →
        S.C.x alpha t ∈ S.layer (i + 1) → t = 0 := by
    intro alpha t halpha hrootMem
    obtain ⟨params, hparams⟩ :=
      standardParabolic_layer_exists_collected S (i + 1) (by omega)
        (S.C.x alpha t) hrootMem
    let highWord : List (S.D.Root × k) :=
      (S.relativeRootAtLeastList (i + 1)).map fun gamma =>
        (gamma.1, params gamma)
    have hhighProduct :
        FilteredCollection.wordProduct S.C.x highWord = S.C.x alpha t := by
      calc
        FilteredCollection.wordProduct S.C.x highWord =
            ((S.relativeRootAtLeastList (i + 1)).map fun gamma =>
              S.C.x gamma.1 (params gamma)).prod := by
                simp [highWord, FilteredCollection.wordProduct, List.map_map,
                  Function.comp_def]
        _ = S.C.x alpha t := hparams.symm
    have hhighNodup : (highWord.map Prod.fst).Nodup := by
      have hsubtypeNodup := S.relativeRootAtLeastList_nodup (i + 1)
      have hrootListNodup := hsubtypeNodup.map
        (fun _ _ h => Subtype.ext h)
      dsimp [highWord]
      rw [List.map_map]
      change (List.map (fun gamma : S.RelativeRootAtLeast (i + 1) => gamma.1)
        (S.relativeRootAtLeastList (i + 1))).Nodup
      exact hrootListNodup
    have hparamsZero : ∀ gamma : S.RelativeRootAtLeast (i + 1),
        params gamma = 0 := by
      letI : Finite (S.RelativeRootAtLeast (i + 1)) := by
        unfold StandardParabolicRelativeRootSetup.RelativeRootAtLeast
        infer_instance
      letI := Fintype.ofFinite (S.RelativeRootAtLeast (i + 1))
      by_contra hnotAllZero
      push Not at hnotAllZero
      let support : Finset (S.RelativeRootAtLeast (i + 1)) :=
        Finset.univ.filter fun gamma => params gamma ≠ 0
      have hsupportNonempty : support.Nonempty := by
        obtain ⟨gamma, hgamma⟩ := hnotAllZero
        exact ⟨gamma, by simp [support, hgamma]⟩
      let heights : Finset Nat := support.image fun gamma => S.relativeDegree gamma.1
      have hheightsNonempty : heights.Nonempty := hsupportNonempty.image _
      let e : Nat := heights.min' hheightsNonempty
      have heMem : e ∈ heights := Finset.min'_mem heights hheightsNonempty
      obtain ⟨beta, hbetaSupport, hbetaDegree⟩ :=
        Finset.mem_image.mp heMem
      have hbetaParam : params beta ≠ 0 := by
        simpa [support] using hbetaSupport
      have hbetaPos : 0 < S.relativeHeight beta.1 := by
        have hiCast : (0 : Int) < i + 1 := by omega
        exact lt_of_lt_of_le hiCast beta.2
      have hbetaHeight : S.relativeHeight beta.1 = e := by
        calc
          S.relativeHeight beta.1 = ((S.relativeHeight beta.1).toNat : Int) :=
            (Int.toNat_of_nonneg (le_of_lt hbetaPos)).symm
          _ = (S.relativeDegree beta.1 : Int) := by
            rfl
          _ = (e : Int) := by exact_mod_cast hbetaDegree
      have hie : i < e := by
        have := beta.2
        rw [hbetaHeight] at this
        omega
      have he : 0 < e := lt_trans hi hie
      have heMax : e ≤ S.maxRelativeHeight := by
        have hle := S.relativeHeight_le beta.1
        change S.relativeHeight beta.1 ≤ S.maxRelativeHeight at hle
        rw [hbetaHeight] at hle
        exact_mod_cast hle
      have hzeroBelow : ∀ q ∈ highWord,
          S.relativeHeight q.1 < e → q.2 = 0 := by
        intro q hq hqBelow
        rw [List.mem_map] at hq
        obtain ⟨gamma, hgammaList, rfl⟩ := hq
        by_contra hgammaParam
        have hgammaSupport : gamma ∈ support := by
          simp [support, hgammaParam]
        have hgammaHeightPos : 0 < S.relativeHeight gamma.1 := by
          have hiCast : (0 : Int) < i + 1 := by omega
          exact lt_of_lt_of_le hiCast gamma.2
        have hmin : e ≤ S.relativeDegree gamma.1 := by
          apply Finset.min'_le heights (S.relativeDegree gamma.1)
          exact Finset.mem_image_of_mem _ hgammaSupport
        have hcast : ((S.relativeHeight gamma.1).toNat : Int) =
            S.relativeHeight gamma.1 :=
          Int.toNat_of_nonneg (le_of_lt hgammaHeightPos)
        change e ≤ (S.relativeHeight gamma.1).toNat at hmin
        have hminCast : (e : Int) ≤ ((S.relativeHeight gamma.1).toNat : Int) := by
          exact_mod_cast hmin
        rw [hcast] at hminCast
        change S.relativeHeight gamma.1 < (e : Int) at hqBelow
        exact (not_lt_of_ge hminCast hqBelow).elim
      have hrootNe : alpha ≠ beta.1 := by
        intro heq
        have := hbetaHeight
        rw [← heq, halpha] at this
        omega
      have halphaPos : 0 < S.relativeHeight alpha := by
        rw [halpha]
        exact_mod_cast hi
      obtain ⟨u, v, hfix, hmove⟩ :=
        standardParabolic_positiveRoots_exists_pairingSeparator S alpha beta.1
          halphaPos hbetaPos hrootNe
      have hfixField :
          standardParabolic_corootPairScale S alpha beta.1 alpha u v = 1 := by
        have hfixVal :
            (u : k) ^ S.D.pairing alpha beta.1 *
              (v : k) ^ S.D.pairing alpha alpha = 1 := by
          simpa using congrArg Units.val hfix
        simpa [standardParabolic_corootPairScale] using hfixVal
      have hscaledProduct :
          FilteredCollection.wordProduct S.C.x
              (highWord.map fun q =>
                (q.1, standardParabolic_corootPairScale S alpha beta.1 q.1 u v * q.2)) =
            FilteredCollection.wordProduct S.C.x highWord := by
        calc
          FilteredCollection.wordProduct S.C.x
              (highWord.map fun q =>
                (q.1, standardParabolic_corootPairScale S alpha beta.1 q.1 u v * q.2)) =
              (S.C.h beta.1 u * S.C.h alpha v)⁻¹ *
                FilteredCollection.wordProduct S.C.x highWord *
                  (S.C.h beta.1 u * S.C.h alpha v) :=
            (standardParabolic_corootPair_conjugates_word S alpha beta.1 u v
              highWord).symm
          _ = (S.C.h beta.1 u * S.C.h alpha v)⁻¹ *
                S.C.x alpha t * (S.C.h beta.1 u * S.C.h alpha v) := by
            rw [hhighProduct]
          _ = S.C.x alpha
              (standardParabolic_corootPairScale S alpha beta.1 alpha u v * t) :=
            standardParabolic_corootPair_conjugates_root S alpha beta.1 alpha u v t
          _ = S.C.x alpha t := by rw [hfixField, one_mul]
          _ = FilteredCollection.wordProduct S.C.x highWord := hhighProduct.symm
      let exactDifferenceWord : List (S.D.Root × k) :=
        ((highWord.filter fun q => S.relativeHeight q.1 = e).map fun q =>
          (q.1,
            (standardParabolic_corootPairScale S alpha beta.1 q.1 u v - 1) * q.2))
      have hexactDifferenceMem :
          FilteredCollection.wordProduct S.C.x exactDifferenceWord ∈
            S.layer (e + 1) := by
        exact standardParabolic_minimalHeight_difference_mem_next S e he highWord
          hzeroBelow alpha beta.1 u v hscaledProduct
      have hfilteredNodup :
          ((highWord.filter fun q => S.relativeHeight q.1 = e).map Prod.fst).Nodup := by
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
          S.relativeHeight q.1 = e := by
        intro q hq
        rw [List.mem_map] at hq
        obtain ⟨r, hr, rfl⟩ := hq
        exact of_decide_eq_true (List.mem_filter.mp hr).2
      have hrecursive :=
        standardParabolic_exactHeight_parameters_eq_zero_of_wordProduct_mem_next
          S e he exactDifferenceWord hexactDifferenceNodup
            hexactDifferenceHeight hexactDifferenceMem
      have hbetaList : beta ∈ S.relativeRootAtLeastList (i + 1) :=
        S.mem_relativeRootAtLeastList (i + 1) beta
      have hbetaHigh : (beta.1, params beta) ∈ highWord :=
        List.mem_map.mpr ⟨beta, hbetaList, rfl⟩
      have hbetaFiltered : (beta.1, params beta) ∈
          highWord.filter fun q => S.relativeHeight q.1 = e := by
        exact List.mem_filter.mpr ⟨hbetaHigh, by simp [hbetaHeight]⟩
      have hbetaDifference :
          (beta.1,
            (standardParabolic_corootPairScale S alpha beta.1 beta.1 u v - 1) *
              params beta) ∈ exactDifferenceWord :=
        List.mem_map.mpr ⟨(beta.1, params beta), hbetaFiltered, rfl⟩
      have hbetaDifferenceZero := hrecursive _ hbetaDifference
      have hmoveField :
          standardParabolic_corootPairScale S alpha beta.1 beta.1 u v ≠ 1 := by
        intro hscale
        apply hmove
        apply Units.ext
        simpa [standardParabolic_corootPairScale] using hscale
      exact (mul_ne_zero (sub_ne_zero.mpr hmoveField) hbetaParam)
        hbetaDifferenceZero
    have hhighOne := chevalleyWord_eq_one_of_params_eq_zero S highWord (by
      intro q hq
      rw [List.mem_map] at hq
      obtain ⟨gamma, hgamma, rfl⟩ := hq
      exact hparamsZero gamma)
    have hxOne : S.C.x alpha t = 1 := by rw [← hhighProduct, hhighOne]
    have hxZero : S.C.x alpha 0 = 1 := chevalleyRoot_zero S alpha
    exact (S.chevalleySystem.1 alpha).1 (hxOne.trans hxZero.symm)
  exact standardParabolic_exactWord_parameters_eq_zero_of_singleRoot
    S i hi hsingle word hnodup hexact hmem
termination_by S.maxRelativeHeight + 1 - i
decreasing_by
  exact Nat.sub_lt_sub_left (by omega) hie

/-- Exact-height subtype form of lowest-layer extraction, intended for the
coordinate-homomorphism construction. -/
public theorem standardParabolic_exactHeight_collected_parameters_eq_zero
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : Nat) (hi : 0 < i)
    (roots : List (S.ExactHeightRoot i)) (hnodup : roots.Nodup)
    (params : S.ExactHeightRoot i → k)
    (hmem : (roots.map fun alpha => S.C.x alpha.root (params alpha)).prod ∈
      S.layer (i + 1)) :
    ∀ alpha ∈ roots, params alpha = 0 := by
  classical
  let word : List (S.D.Root × k) := roots.map fun alpha =>
    (alpha.root, params alpha)
  have hwordNodup : (word.map Prod.fst).Nodup := by
    have hrootNodup := hnodup.map
      StandardParabolicRelativeRootSetup.ExactHeightRoot.root_injective
    dsimp [word]
    rw [List.map_map]
    change (roots.map fun alpha => alpha.root).Nodup
    exact hrootNodup
  have hwordExact : ∀ q ∈ word, S.relativeHeight q.1 = i := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨alpha, halpha, rfl⟩ := hq
    exact alpha.height_eq
  have hwordProduct : FilteredCollection.wordProduct S.C.x word =
      (roots.map fun alpha => S.C.x alpha.root (params alpha)).prod := by
    simp [word, FilteredCollection.wordProduct, List.map_map, Function.comp_def]
  have hwordMem : FilteredCollection.wordProduct S.C.x word ∈ S.layer (i + 1) := by
    rw [hwordProduct]
    exact hmem
  have hzero :=
    standardParabolic_exactHeight_parameters_eq_zero_of_wordProduct_mem_next
      S i hi word hwordNodup hwordExact hwordMem
  intro alpha halpha
  exact hzero (alpha.root, params alpha)
    (List.mem_map.mpr ⟨alpha, halpha, rfl⟩)

end Theory.AlgebraicGroup
