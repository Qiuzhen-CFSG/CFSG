module

public import Theory.AlgebraicGroup.Borel.RootStructure.PositiveRootOrderedFactorization
public import Theory.AlgebraicGroup.Borel.RootStructure.FundamentalRootGeneration
public import Theory.AlgebraicGroup.Borel.RootStructure.UnipotentProductDefs
public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteGeneration
public import Theory.AlgebraicGroup.RootData.ChevalleyCommutator

/-!
The unipotent root-product package of GLS3 Theorem 1.12.7(a)-(d).

An aligned abstract base turns the selected positive system into a strictly
positive height filtration.  The arbitrary-order Chevalley collector then
writes every generated root-subgroup word in any duplicate-free root order;
the positive-coordinate separation theorem supplies uniqueness for the full
positive system.  For a closed subset, finite connected generation makes the
abstractly generated subgroup Zariski closed and the same collector identifies
all of its ordered products.

For a positive-root ideal, a root-string induction shows that every valid
positive combination containing an ideal root remains in the ideal.  The
Chevalley commutator formula consequently shows that each positive root factor
normalizes the ideal-generated subgroup.  Closure under the positive-root
generators gives normality inside the unipotent radical.  Finally, the
characteristic-free rank-two isolation theorem reduces positive-root
generation to the fundamental roots.
-/

universe u v w x y

namespace Theory.AlgebraicGroup

open scoped commutatorElement

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma chevalleyRoot_zero
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} {C : ChevalleyData K D}
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y}
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {systemBase : P.Base}
    (hC : IsChevalleySystem D C P e systemBase) (alpha : D.Root) :
    C.x alpha 0 = 1 := by
  simpa using hC.2.2.2.1 alpha 0 0

omit [IsAlgClosed k] in
private lemma chevalleyRoot_neg
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} {C : ChevalleyData K D}
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y}
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {systemBase : P.Base}
    (hC : IsChevalleySystem D C P e systemBase) (alpha : D.Root) (a : k) :
    C.x alpha (-a) = (C.x alpha a)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [hC.2.2.2.1]
  simpa using chevalleyRoot_zero hC alpha

omit [IsAlgClosed k] in
private lemma rootGenerated_exists_word
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} {C : ChevalleyData K D}
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y}
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {systemBase : P.Base}
    (hC : IsChevalleySystem D C P e systemBase)
    (roots : Set D.Root) (z : Variety.Point K)
    (hz : z ∈ RootSubgroupGenerated D roots) :
    ∃ word : List (D.Root × k),
      (∀ q ∈ word, q.1 ∈ roots) ∧
      z = FilteredCollection.wordProduct C.x word := by
  classical
  have hwordInv : ∀ word : List (D.Root × k),
      (FilteredCollection.wordProduct C.x word)⁻¹ =
        FilteredCollection.wordProduct C.x
          (word.reverse.map fun q => (q.1, -q.2)) := by
    intro word
    change (word.map fun q => C.x q.1 q.2).prod⁻¹ =
      (((word.reverse.map fun q => (q.1, -q.2)).map
        fun q => C.x q.1 q.2).prod)
    induction word with
    | nil => simp
    | cons q tail ih =>
        simp only [List.map_cons, List.prod_cons, List.reverse_cons,
          List.map_append, List.map_map, List.prod_append, mul_inv_rev]
        rw [ih, chevalleyRoot_neg hC]
        simp [Function.comp_def]
  rw [RootSubgroupGenerated] at hz
  refine Subgroup.closure_induction
    (p := fun z _ => ∃ word : List (D.Root × k),
      (∀ q ∈ word, q.1 ∈ roots) ∧
      z = FilteredCollection.wordProduct C.x word)
    (k := ⋃ alpha ∈ roots,
      (D.rootSubgroup alpha : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hz
  · intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨alpha, halpha, hz⟩ := hz
    have hzRange : z ∈ Set.range (C.x alpha) := by
      simpa [(hC.1 alpha).2] using hz
    obtain ⟨t, rfl⟩ := hzRange
    exact ⟨[(alpha, t)], by simp [halpha], by simp [FilteredCollection.wordProduct]⟩
  · exact ⟨[], by simp, by simp [FilteredCollection.wordProduct]⟩
  · intro z z' _ _
    rintro ⟨word, hword, rfl⟩ ⟨word', hword', rfl⟩
    refine ⟨word ++ word', ?_, by simp [FilteredCollection.wordProduct]⟩
    intro q hq
    exact (List.mem_append.mp hq).elim (hword q) (hword' q)
  · intro z _
    rintro ⟨word, hword, rfl⟩
    refine ⟨word.reverse.map fun q => (q.1, -q.2), ?_, hwordInv word⟩
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    exact hword r (List.mem_reverse.mp hr)

omit [IsAlgClosed k] in
private lemma positiveRoots_linearlyIndependent
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y}
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (positiveBase : P.Base)
    {alpha beta : D.Root}
    (halpha : positiveBase.IsPos (e alpha))
    (hbeta : positiveBase.IsPos (e beta)) (hne : alpha ≠ beta) :
    AreLinearlyIndependentRoots D P e alpha beta := by
  let _ := P.indexNeg
  have hnotopp : P.root (e alpha) ≠ -P.root (e beta) := by
    intro hneg
    have hidx : e alpha = P.reflectionPerm (e beta) (e beta) :=
      P.root_eq_neg_iff.mp hneg
    have halphaNeg : positiveBase.IsPos (-e beta) := by simpa [hidx] using halpha
    exact ((RootPairing.Base.IsPos.neg_iff_not
      (P := P) (b := positiveBase) (i := e beta)).mp halphaNeg) hbeta
  have hrootne : e alpha ≠ e beta := fun heq => hne (e.injective heq)
  have hlin : LinearIndependent R ![P.root (e alpha), P.root (e beta)] :=
    RootPairing.IsReduced.linearIndependent (P := P) hrootne hnotopp
  rw [LinearIndependent.pair_iff] at hlin
  simpa [AreLinearlyIndependentRoots] using hlin

omit [IsAlgClosed k] in
private lemma combination_ne_left
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y}
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) {alpha beta gamma : D.Root} {i j : ℕ}
    (_hi : 0 < i) (hj : 0 < j)
    (hroot : P.root (e gamma) =
      (i : R) • P.root (e alpha) + (j : R) • P.root (e beta))
    (hLI : AreLinearlyIndependentRoots D P e alpha beta) : gamma ≠ alpha := by
  intro h
  subst gamma
  have hz : (1 - (i : R)) • P.root (e alpha) +
      (-(j : R)) • P.root (e beta) = 0 := by
    calc
      _ = P.root (e alpha) -
          ((i : R) • P.root (e alpha) + (j : R) • P.root (e beta)) := by module
      _ = 0 := by rw [← hroot]; module
  have hz' := hLI (1 - (i : R)) (-(j : R)) hz
  have hjR : (j : R) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  exact hjR (neg_eq_zero.mp hz'.2)

omit [IsAlgClosed k] in
private lemma combination_ne_right
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y}
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) {alpha beta gamma : D.Root} {i j : ℕ}
    (hi : 0 < i) (_hj : 0 < j)
    (hroot : P.root (e gamma) =
      (i : R) • P.root (e alpha) + (j : R) • P.root (e beta))
    (hLI : AreLinearlyIndependentRoots D P e alpha beta) : gamma ≠ beta := by
  intro h
  subst gamma
  have hz : (-(i : R)) • P.root (e alpha) +
      (1 - (j : R)) • P.root (e beta) = 0 := by
    calc
      _ = P.root (e beta) -
          ((i : R) • P.root (e alpha) + (j : R) • P.root (e beta)) := by module
      _ = 0 := by rw [← hroot]; module
  have hz' := hLI (-(i : R)) (1 - (j : R)) hz
  have hiR : (i : R) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hi)
  exact hiR (neg_eq_zero.mp hz'.1)

omit [IsAlgClosed k] in
private lemma positiveCombination_mem_rootIdeal
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y}
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (positiveRoots roots : Set D.Root)
    (hIdeal : IsRootIdealIn D positiveRoots roots)
    {alpha beta : D.Root} (halpha : alpha ∈ positiveRoots)
    (hbeta : beta ∈ roots)
    (hLI : AreLinearlyIndependentRoots D P e alpha beta)
    (hAdd : IsRootAdditionRealization D P e) :
    ∀ i j : ℕ, 0 < i → 0 < j → ∀ gamma : D.Root,
      P.root (e gamma) =
        (i : R) • P.root (e alpha) + (j : R) • P.root (e beta) →
      gamma ∈ roots := by
  intro i j hi hj gamma hroot
  let _ := Fintype.ofFinite ι
  generalize hn : i + j = n
  induction n using Nat.strong_induction_on generalizing i j gamma with
  | h n ih =>
      have hpair : (2 : ℤ) =
          (i : ℤ) * P.pairingIn ℤ (e alpha) (e gamma) +
            (j : ℤ) * P.pairingIn ℤ (e beta) (e gamma) := by
        have hrootZ : P.root (e gamma) =
            (i : ℤ) • P.root (e alpha) + (j : ℤ) • P.root (e beta) := by
          simpa only [natCast_zsmul, Nat.cast_smul_eq_nsmul R] using hroot
        have h := P.pairingIn_eq_add_of_root_eq_smul_add_smul
          (S := ℤ) (j := e gamma) hrootZ
        rw [P.pairingIn_same] at h
        simpa [smul_eq_mul] using h
      have hiZ : (0 : ℤ) < i := by exact_mod_cast hi
      have hjZ : (0 : ℤ) < j := by exact_mod_cast hj
      have hpairing : 0 < P.pairingIn ℤ (e alpha) (e gamma) ∨
          0 < P.pairingIn ℤ (e beta) (e gamma) := by
        by_contra! hnonpos
        nlinarith
      by_cases hbase : i = 1 ∧ j = 1
      · rcases hbase with ⟨rfl, rfl⟩
        exact hIdeal.2 beta hbeta alpha halpha gamma
          (hAdd.add_of_root_eq_add (by simpa [add_comm] using hroot))
      rcases hpairing with hpaForward | hpbForward
      · have hpa : 0 < P.pairingIn ℤ (e gamma) (e alpha) :=
          (P.zero_lt_pairingIn_iff (P.posRootForm ℤ) (e alpha) (e gamma)).mp hpaForward
        have hne : e gamma ≠ e alpha := fun h =>
          combination_ne_left D P e hi hj hroot hLI (e.injective h)
        obtain ⟨deltaIndex, hdeltaIndex⟩ :=
          P.root_sub_root_mem_of_pairingIn_pos hpa hne
        have hi_gt : 1 < i := by
          by_contra hi_not
          have hi1 : i = 1 := by omega
          subst i
          let _ : IsAddTorsionFree M := IsAddTorsionFree.of_isTorsionFree R M
          let _ : j.AtLeastTwo := ⟨by omega⟩
          exact (P.nsmul_notMem_range_root (n := j) (i := e beta)) ⟨deltaIndex, by
            rw [hdeltaIndex, hroot]
            simp only [Nat.cast_one, one_smul, Nat.cast_smul_eq_nsmul R]
            module⟩
        let delta : D.Root := e.symm deltaIndex
        have hdeltaRoot : P.root (e delta) =
            P.root (e gamma) - P.root (e alpha) := by
          simpa [delta] using hdeltaIndex
        have hcomb : P.root (e delta) =
            ((i - 1 : ℕ) : R) • P.root (e alpha) +
              (j : R) • P.root (e beta) := by
          rw [hdeltaRoot, hroot, Nat.cast_sub (Nat.le_of_lt hi_gt)]
          module
        have hsmaller : i - 1 + j < n := by omega
        have hdeltaMem : delta ∈ roots := ih (i - 1 + j) hsmaller
          (i - 1) j (by omega) (by omega) delta hcomb (by omega)
        exact hIdeal.2 delta hdeltaMem alpha halpha gamma
          (hAdd.add_of_root_eq_add (by rw [hdeltaRoot]; module))
      · have hpb : 0 < P.pairingIn ℤ (e gamma) (e beta) :=
          (P.zero_lt_pairingIn_iff (P.posRootForm ℤ) (e beta) (e gamma)).mp hpbForward
        have hne : e gamma ≠ e beta := fun h =>
          combination_ne_right D P e hi hj hroot hLI (e.injective h)
        obtain ⟨deltaIndex, hdeltaIndex⟩ :=
          P.root_sub_root_mem_of_pairingIn_pos hpb hne
        have hj_gt : 1 < j := by
          by_contra hj_not
          have hj1 : j = 1 := by omega
          subst j
          let _ : IsAddTorsionFree M := IsAddTorsionFree.of_isTorsionFree R M
          let _ : i.AtLeastTwo := ⟨by omega⟩
          exact (P.nsmul_notMem_range_root (n := i) (i := e alpha)) ⟨deltaIndex, by
            rw [hdeltaIndex, hroot]
            simp only [Nat.cast_one, one_smul, Nat.cast_smul_eq_nsmul R]
            module⟩
        let delta : D.Root := e.symm deltaIndex
        have hdeltaRoot : P.root (e delta) =
            P.root (e gamma) - P.root (e beta) := by
          simpa [delta] using hdeltaIndex
        have hcomb : P.root (e delta) =
            (i : R) • P.root (e alpha) +
              ((j - 1 : ℕ) : R) • P.root (e beta) := by
          rw [hdeltaRoot, hroot, Nat.cast_sub (Nat.le_of_lt hj_gt)]
          module
        have hsmaller : i + (j - 1) < n := by omega
        have hdeltaMem : delta ∈ roots := ih (i + (j - 1)) hsmaller
          i (j - 1) hi (by omega) delta hcomb (by omega)
        exact hIdeal.2 delta hdeltaMem beta (hIdeal.1 hbeta) gamma
          (hAdd.add_of_root_eq_add (by rw [hdeltaRoot]; module))

omit [IsAlgClosed k] in
private theorem rootGenerated_eq_orderedRootSubgroupProductFin
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y}
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (systemBase positiveBase : P.Base)
    (hC : IsChevalleySystem D C P e systemBase)
    (hAdd : IsRootAdditionRealization D P e)
    (positiveRoots roots : Set D.Root)
    (hpositive : ∀ alpha, alpha ∈ positiveRoots ↔ positiveBase.IsPos (e alpha))
    (hroots : roots ⊆ positiveRoots)
    (hclosed : ∀ alpha beta gamma, alpha ∈ roots → beta ∈ roots →
      D.add alpha beta = some gamma → gamma ∈ roots)
    (order : List D.Root) (horder : EnumeratesRootSet roots order) :
    (RootSubgroupGenerated D roots : Set (Variety.Point K)) =
      OrderedRootSubgroupProductFin D order := by
  classical
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨word, hword, hzWord⟩ := rootGenerated_exists_word hC roots z hz
    obtain ⟨params, hparams⟩ :=
      positiveRootChevalleyCollection_exists_params_of_separateBase
        P e systemBase positiveBase C hC hAdd hpositive hroots hclosed
          order horder.1 horder.2 word hword
    let factors : Fin order.length → Variety.Point K :=
      fun i => C.x (order.get i) (params (order.get i))
    refine ⟨factors, ?_, ?_⟩
    · intro i
      change C.x (order.get i) (params (order.get i)) ∈
        (D.rootSubgroup (order.get i) : Set (Variety.Point K))
      rw [← (hC.1 (order.get i)).2]
      exact Set.mem_range_self _
    · calc
        z = FilteredCollection.wordProduct C.x word := hzWord
        _ = (order.map fun alpha => C.x alpha (params alpha)).prod := hparams
        _ = (List.ofFn factors).prod := by
          change _ = (List.ofFn
            ((fun alpha => C.x alpha (params alpha)) ∘ order.get)).prod
          rw [← List.map_ofFn, List.ofFn_get]
  · rintro z ⟨factors, hfactors, rfl⟩
    apply Subgroup.list_prod_mem
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact rootSubgroup_le_RootSubgroupGenerated D
      ((horder.2 (order.get i)).mp (List.get_mem order i)) (hfactors i)

private lemma rootGenerated_isZariskiClosed
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization)
    (roots : Set D.Root) [Finite roots] :
    IsZariskiClosed K
      (RootSubgroupGenerated D roots : Set (Variety.Point K)) := by
  let rootFamily : roots → ClosedSubgroup K :=
    fun alpha => D.rootSubgroup alpha.1
  have hconnected : ∀ alpha,
      _root_.IsConnected (rootFamily alpha : Set (Variety.Point K)) := by
    intro alpha
    have hconn : Variety.IsConnected
        (D.rootSubgroup alpha.1).carrierVariety :=
      (hD.2.2.1 alpha.1).1.2.isConnected
    let : ConnectedSpace
        (Variety.Point (D.rootSubgroup alpha.1).carrierVariety) :=
      connectedSpace_iff_univ.mpr hconn
    change _root_.IsConnected
      ((D.rootSubgroup alpha.1).toSubgroup : Set (Variety.Point K))
    rw [← (D.rootSubgroup alpha.1).range_inclusion]
    exact isConnected_range
      (D.rootSubgroup alpha.1).inclusion.toVariety.continuous
  have hclosed :=
    closure_iUnion_connected_closedSubgroup_isZariskiClosed rootFamily hconnected
  rw [RootSubgroupGenerated]
  change IsZariskiClosed K
    (Subgroup.closure (⋃ alpha ∈ roots,
      (D.rootSubgroup alpha : Set (Variety.Point K))) : Set (Variety.Point K))
  rw [← Set.iUnion_subtype (fun alpha : D.Root => alpha ∈ roots)
    (fun alpha => (D.rootSubgroup alpha.1 : Set (Variety.Point K)))]
  exact hclosed

omit [IsAlgClosed k] in
private lemma rootSubgroup_commutatorElement_eq_one
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} {C : ChevalleyData K D}
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y}
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {systemBase : P.Base}
    (hC : IsChevalleySystem D C P e systemBase)
    (alpha : D.Root) {z z' : Variety.Point K}
    (hz : z ∈ D.rootSubgroup alpha) (hz' : z' ∈ D.rootSubgroup alpha) :
    ⁅z, z'⁆ = 1 := by
  apply commutatorElement_eq_one_iff_commute.mpr
  have hzRange : z ∈ Set.range (C.x alpha) := by
    simpa [(hC.1 alpha).2] using hz
  have hz'Range : z' ∈ Set.range (C.x alpha) := by
    simpa [(hC.1 alpha).2] using hz'
  obtain ⟨t, rfl⟩ := hzRange
  obtain ⟨s, rfl⟩ := hz'Range
  show C.x alpha t * C.x alpha s = C.x alpha s * C.x alpha t
  rw [hC.2.2.2.1, hC.2.2.2.1, add_comm]

omit [IsAlgClosed k] in
private lemma rootFactor_commutator_mem_rootIdeal
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y}
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (systemBase positiveBase : P.Base)
    (hC : IsChevalleySystem D C P e systemBase)
    (hAdd : IsRootAdditionRealization D P e)
    (positiveRoots roots : Set D.Root)
    (hpositive : ∀ alpha, alpha ∈ positiveRoots ↔ positiveBase.IsPos (e alpha))
    (hIdeal : IsRootIdealIn D positiveRoots roots)
    {alpha beta : D.Root} (halpha : alpha ∈ positiveRoots) (hbeta : beta ∈ roots)
    {z z' : Variety.Point K} (hz : z ∈ D.rootSubgroup alpha)
    (hz' : z' ∈ D.rootSubgroup beta) :
    ⁅z, z'⁆ ∈ RootSubgroupGenerated D roots := by
  by_cases heq : alpha = beta
  · subst beta
    rw [rootSubgroup_commutatorElement_eq_one hC alpha hz hz']
    exact (RootSubgroupGenerated D roots).one_mem
  · have hLI : AreLinearlyIndependentRoots D P e alpha beta :=
      positiveRoots_linearlyIndependent D P e positiveBase
        ((hpositive alpha).1 halpha) ((hpositive beta).1 (hIdeal.1 hbeta)) heq
    have hcomm := rootSubgroup_commutatorElement_mem_chevalleyCommutatorRoots
      D C P e systemBase hC hLI hz hz'
    apply RootSubgroupGenerated_mono D ?_ hcomm
    intro gamma hgamma
    obtain ⟨i, j, hi, hj, hroot⟩ :=
      (mem_chevalleyCommutatorRoots_iff D P e alpha beta gamma).1 hgamma
    exact positiveCombination_mem_rootIdeal D P e positiveRoots roots hIdeal
      halpha hbeta hLI hAdd i j hi hj gamma hroot

omit [IsAlgClosed k] in
private lemma rootSubgroup_le_normalizer_rootIdeal
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y}
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (systemBase positiveBase : P.Base)
    (hC : IsChevalleySystem D C P e systemBase)
    (hAdd : IsRootAdditionRealization D P e)
    (positiveRoots roots : Set D.Root)
    (hpositive : ∀ alpha, alpha ∈ positiveRoots ↔ positiveBase.IsPos (e alpha))
    (hIdeal : IsRootIdealIn D positiveRoots roots)
    {alpha : D.Root} (halpha : alpha ∈ positiveRoots) :
    (D.rootSubgroup alpha).toSubgroup ≤
      Subgroup.normalizer
        (RootSubgroupGenerated D roots : Set (Variety.Point K)) := by
  intro z hz
  have hconj (z0 : Variety.Point K) (hz0 : z0 ∈ D.rootSubgroup alpha) :
      ∀ q, q ∈ RootSubgroupGenerated D roots →
        z0 * q * z0⁻¹ ∈ RootSubgroupGenerated D roots := by
    intro q hq
    rw [RootSubgroupGenerated] at hq
    refine Subgroup.closure_induction
      (p := fun q _ => z0 * q * z0⁻¹ ∈ RootSubgroupGenerated D roots)
      (k := ⋃ beta ∈ roots,
        (D.rootSubgroup beta : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hq
    · intro q hq
      simp only [Set.mem_iUnion] at hq
      obtain ⟨beta, hbeta, hq⟩ := hq
      have hcomm := rootFactor_commutator_mem_rootIdeal
        D C P e systemBase positiveBase hC hAdd positiveRoots roots hpositive hIdeal
          halpha hbeta hz0 hq
      have hmul := (RootSubgroupGenerated D roots).mul_mem hcomm
        (rootSubgroup_le_RootSubgroupGenerated D hbeta hq)
      simpa [commutatorElement_def, mul_assoc] using hmul
    · simp
    · intro q r _ _ hq' hr'
      have hmul := (RootSubgroupGenerated D roots).mul_mem hq' hr'
      simpa [mul_assoc] using hmul
    · intro q _ hq'
      have hinv := (RootSubgroupGenerated D roots).inv_mem hq'
      simpa [mul_assoc] using hinv
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · exact hconj z hz q
  · intro hq
    have hzInv : z⁻¹ ∈ D.rootSubgroup alpha :=
      (D.rootSubgroup alpha).inv_mem hz
    simpa [mul_assoc] using hconj z⁻¹ hzInv (z * q * z⁻¹) hq

omit [IsAlgClosed k] in
private lemma positiveRootGenerated_le_normalizer_rootIdeal
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y}
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (systemBase positiveBase : P.Base)
    (hC : IsChevalleySystem D C P e systemBase)
    (hAdd : IsRootAdditionRealization D P e)
    (positiveRoots roots : Set D.Root)
    (hpositive : ∀ alpha, alpha ∈ positiveRoots ↔ positiveBase.IsPos (e alpha))
    (hIdeal : IsRootIdealIn D positiveRoots roots) :
    RootSubgroupGenerated D positiveRoots ≤
      Subgroup.normalizer
        (RootSubgroupGenerated D roots : Set (Variety.Point K)) := by
  apply RootSubgroupGenerated_le_of_rootSubgroup_le
  intro alpha halpha
  exact rootSubgroup_le_normalizer_rootIdeal D C P e systemBase positiveBase
    hC hAdd positiveRoots roots hpositive hIdeal halpha

public structure UnipotentRootProductPackage
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (positiveRoots : Set D.Root) (B U : ClosedSubgroup K)
    (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) where
  ordered_factorization : ∀ order, EnumeratesRootSet positiveRoots order →
    ∀ z, z ∈ U ↔
      ∃! parameters : Fin order.length → k,
        orderedChevalleyProduct C order parameters = z
  commutator_formula : ∀ alpha beta, alpha ∈ positiveRoots → beta ∈ positiveRoots →
    ∀ order,
      EnumeratesRootSet (PositiveRootCombinations (D := D) P e alpha beta) order →
        ∀ z,
          z ∈ ⁅(D.rootSubgroup alpha).toSubgroup,
            (D.rootSubgroup beta).toSubgroup⁆ →
          z ∈ OrderedRootSubgroupProductFin D order
  closed_subset : ∀ roots, roots ⊆ positiveRoots → IsClosedRootSubset D roots →
    Nonempty (ClosedRootProduct (U := U) D roots)
  ideal_subset : ∀ roots, IsRootIdealIn D positiveRoots roots →
    Nonempty (NormalRootProduct (U := U) D roots)
  fundamental_generation :
    U.toSubgroup = RootSubgroupGenerated D (FundamentalRootsFor D positiveRoots)

/-- The unipotent root-product package in GLS3 Theorem 1.12.7(a)-(d). -/
public theorem unipotentRootProductPackage
    {K : Variety k} [AlgebraicGroup K]
    (T B U : ClosedSubgroup K) (D : RootGroupData K T)
    (C : ChevalleyData K D) (positiveRoots : Set D.Root)
    [Fintype D.Root]
    (hSetup : IsStandardBorelSetup T B D positiveRoots)
    (hGen : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y}
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hActual : IsRootSystemRealization D P e base)
    (hAdd : IsRootAdditionRealization D P e)
    (hC : IsChevalleySystem D C P e base) :
    Nonempty (UnipotentRootProductPackage T D positiveRoots B U C P e base) := by
  classical
  obtain ⟨positiveBase, hpositive⟩ :=
    exists_base_isPos_iff_of_positiveSystem D P e base hSetup.2.2.1 hActual hAdd
  refine ⟨{
    ordered_factorization := ?_
    commutator_formula := ?_
    closed_subset := ?_
    ideal_subset := ?_
    fundamental_generation := ?_ }⟩
  · intro order horder z
    change z ∈ U.toSubgroup ↔ _
    rw [hGen]
    exact positiveRootOrderedFactorization D C positiveRoots P e base positiveBase
      hSetup.2.2.1 hpositive hAdd hActual hC order horder z
  · intro alpha beta halpha hbeta order horder z hz
    by_cases heq : alpha = beta
    · subst beta
      have hcommLe : ⁅(D.rootSubgroup alpha).toSubgroup,
          (D.rootSubgroup alpha).toSubgroup⁆ ≤
          (⊥ : Subgroup (Variety.Point K)) := by
        rw [Subgroup.commutator_le]
        intro q hq r hr
        rw [rootSubgroup_commutatorElement_eq_one hC alpha hq hr]
        exact Subgroup.one_mem _
      have hbot : z ∈ (⊥ : Subgroup (Variety.Point K)) := hcommLe hz
      have hzOne : z = 1 := Subgroup.mem_bot.mp hbot
      subst z
      refine ⟨fun _ => 1, fun i => (D.rootSubgroup (order.get i)).one_mem, by simp⟩
    · have hLI : AreLinearlyIndependentRoots D P e alpha beta :=
        positiveRoots_linearlyIndependent D P e positiveBase
          ((hpositive alpha).1 halpha) ((hpositive beta).1 hbeta) heq
      have hsets : ChevalleyCommutatorRoots D P e alpha beta =
          PositiveRootCombinations (D := D) P e alpha beta := by
        ext gamma
        rw [mem_chevalleyCommutatorRoots_iff]
        rfl
      have hzGenerated : z ∈ RootSubgroupGenerated D
          (PositiveRootCombinations (D := D) P e alpha beta) := by
        rw [← hsets]
        exact rootSubgroup_commutator_le_chevalleyCommutatorRoots
          D C P e base hC hLI hz
      have hPositiveIdeal : IsRootIdealIn D positiveRoots positiveRoots :=
        ⟨fun _ h => h, fun a ha b hb gamma hadd =>
          hSetup.2.2.1.2.2 a ha b hb gamma hadd⟩
      have hcombinationsPositive :
          PositiveRootCombinations (D := D) P e alpha beta ⊆ positiveRoots := by
        intro gamma hgamma
        obtain ⟨i, j, hi, hj, hroot⟩ := hgamma
        exact positiveCombination_mem_rootIdeal D P e positiveRoots positiveRoots
          hPositiveIdeal halpha hbeta hLI hAdd i j hi hj gamma hroot
      have hcombinationsClosed : ∀ gamma delta epsilon,
          gamma ∈ PositiveRootCombinations (D := D) P e alpha beta →
          delta ∈ PositiveRootCombinations (D := D) P e alpha beta →
          D.add gamma delta = some epsilon →
          epsilon ∈ PositiveRootCombinations (D := D) P e alpha beta := by
        rintro gamma delta epsilon ⟨i, j, hi, hj, hgamma⟩
          ⟨i', j', hi', hj', hdelta⟩ hadd
        refine ⟨i + i', j + j', by omega, by omega, ?_⟩
        rw [(hAdd gamma delta epsilon).1 hadd, hgamma, hdelta]
        push_cast
        module
      rw [← rootGenerated_eq_orderedRootSubgroupProductFin
        D C P e base positiveBase hC hAdd positiveRoots
          (PositiveRootCombinations (D := D) P e alpha beta)
          hpositive hcombinationsPositive hcombinationsClosed order horder]
      exact hzGenerated
  · intro roots hroots hClosed
    let carrier : ClosedSubgroup K := ClosedSubgroup.ofSubgroup
      (RootSubgroupGenerated D roots)
      (rootGenerated_isZariskiClosed hSetup.2.1 roots)
    refine ⟨{
      carrier := carrier
      le_unipotent := ?_
      generated := rfl
      every_order := ?_ }⟩
    · change RootSubgroupGenerated D roots ≤ U.toSubgroup
      rw [hGen]
      exact RootSubgroupGenerated_mono D hroots
    · intro order horder
      change (RootSubgroupGenerated D roots : Set (Variety.Point K)) = _
      exact rootGenerated_eq_orderedRootSubgroupProductFin
        D C P e base positiveBase hC hAdd positiveRoots roots hpositive hroots
          (fun alpha beta gamma halpha hbeta hadd =>
            hClosed alpha halpha beta hbeta gamma hadd) order horder
  · intro roots hIdeal
    have hClosed : IsClosedRootSubset D roots := by
      intro alpha halpha beta hbeta gamma hadd
      exact hIdeal.2 alpha halpha beta (hIdeal.1 hbeta) gamma hadd
    let carrier : ClosedSubgroup K := ClosedSubgroup.ofSubgroup
      (RootSubgroupGenerated D roots)
      (rootGenerated_isZariskiClosed hSetup.2.1 roots)
    refine ⟨{
      carrier := carrier
      le_unipotent := ?_
      generated := rfl
      every_order := ?_
      normal_in_unipotent := ?_ }⟩
    · change RootSubgroupGenerated D roots ≤ U.toSubgroup
      rw [hGen]
      exact RootSubgroupGenerated_mono D hIdeal.1
    · intro order horder
      change (RootSubgroupGenerated D roots : Set (Variety.Point K)) = _
      exact rootGenerated_eq_orderedRootSubgroupProductFin
        D C P e base positiveBase hC hAdd positiveRoots roots hpositive hIdeal.1
          (fun alpha beta gamma halpha hbeta hadd =>
            hClosed alpha halpha beta hbeta gamma hadd) order horder
    · apply Subgroup.normal_subgroupOf_of_le_normalizer
      rw [hGen]
      exact positiveRootGenerated_le_normalizer_rootIdeal
        D C P e base positiveBase hC hAdd positiveRoots roots hpositive hIdeal
  · rw [hGen]
    exact rootSubgroupGenerated_positiveRoots_eq_fundamentalRootsFor
      D C positiveRoots hSetup P e base hActual hAdd hC

end Theory.AlgebraicGroup
