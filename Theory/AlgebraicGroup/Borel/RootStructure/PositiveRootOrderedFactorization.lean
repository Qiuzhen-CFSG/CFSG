module

public import Theory.AlgebraicGroup.RootData.PositiveRootCoordinateUniqueness
public import Theory.AlgebraicGroup.RootData.PositiveRootCollection
public import Theory.AlgebraicGroup.Borel.RootStructure.FundamentalCorootData
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup

/-!
This module identifies the positive-root generated subgroup with the ordered
Chevalley coordinate space.  A finite subgroup word is collected into the
chosen positive-root order using the exact root-addition relation.  The
coordinate-injectivity theorem supplies uniqueness even when the Chevalley
system base and the positive-system base are different; finite root-subgroup
words give the converse membership implication.

This is the ordered-factorization argument used for the unipotent-root
product package in GLS3, Theorem 1.12.7.
-/

universe u v w x y

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma chevalleyRoot_zero
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} {C : ChevalleyData K D}
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y} [Finite ι] [Field R] [CharZero R]
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
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y} [Finite ι] [Field R] [CharZero R]
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
private theorem positiveRootGenerated_exists_word
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} {C : ChevalleyData K D}
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {systemBase : P.Base}
    (hC : IsChevalleySystem D C P e systemBase)
    (positiveRoots : Set D.Root) (z : Variety.Point K)
    (hz : z ∈ RootSubgroupGenerated D positiveRoots) :
    ∃ word : List (D.Root × k),
      (∀ q ∈ word, q.1 ∈ positiveRoots) ∧
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
      (∀ q ∈ word, q.1 ∈ positiveRoots) ∧
      z = FilteredCollection.wordProduct C.x word)
    (k := ⋃ alpha ∈ positiveRoots,
      (D.rootSubgroup alpha : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hz
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨alpha, halpha, hxalpha⟩ := hx
    have hxRange : x ∈ Set.range (C.x alpha) := by
      simpa [(hC.1 alpha).2] using hxalpha
    obtain ⟨t, rfl⟩ := hxRange
    exact ⟨[(alpha, t)], by simp [halpha], by simp [FilteredCollection.wordProduct]⟩
  · exact ⟨[], by simp, by simp [FilteredCollection.wordProduct]⟩
  · intro x y _ _
    rintro ⟨wordX, hwordX, rfl⟩ ⟨wordY, hwordY, rfl⟩
    refine ⟨wordX ++ wordY, ?_, by simp [FilteredCollection.wordProduct]⟩
    intro q hq
    exact (List.mem_append.mp hq).elim (hwordX q) (hwordY q)
  · intro x _
    rintro ⟨word, hword, rfl⟩
    refine ⟨word.reverse.map fun q => (q.1, -q.2), ?_, hwordInv word⟩
    · intro q hq
      rw [List.mem_map] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      exact hword r (List.mem_reverse.mp hr)

public theorem positiveRootOrderedFactorization
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (positiveRoots : Set D.Root) [Fintype D.Root]
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (systemBase positiveBase : P.Base)
    (hPositive : IsPositiveSystem D positiveRoots)
    (hpositive : ∀ alpha, alpha ∈ positiveRoots ↔ positiveBase.IsPos (e alpha))
    (hAdd : IsRootAdditionRealization D P e)
    (hActual : IsRootSystemRealization D P e systemBase)
    (hC : IsChevalleySystem D C P e systemBase)
    (order : List D.Root) (horder : EnumeratesRootSet positiveRoots order)
    (u : Variety.Point K) :
    u ∈ RootSubgroupGenerated D positiveRoots ↔
      ∃! parameters : Fin order.length → k,
        orderedChevalleyProduct C order parameters = u := by
  constructor
  · intro hu
    obtain ⟨word, hword, rfl⟩ :=
      positiveRootGenerated_exists_word hC positiveRoots u hu
    have hclosed : ∀ alpha beta gamma, alpha ∈ positiveRoots →
        beta ∈ positiveRoots → D.add alpha beta = some gamma →
        gamma ∈ positiveRoots := by
      intro alpha beta gamma halpha hbeta hadd
      exact hPositive.2.2 alpha halpha beta hbeta gamma hadd
    obtain ⟨params, hparams⟩ :=
      positiveRootChevalleyCollection_exists_params_of_separateBase
        P e systemBase positiveBase C hC hAdd hpositive
          (fun _ h => h) hclosed order horder.1 horder.2 word hword
    let parameters : Fin order.length → k := fun i => params (order.get i)
    have hparameters : orderedChevalleyProduct C order parameters =
        FilteredCollection.wordProduct C.x word := by
      change (List.ofFn fun i => C.x (order.get i) (parameters i)).prod =
        FilteredCollection.wordProduct C.x word
      dsimp [parameters]
      calc
        (List.ofFn fun i => C.x (order.get i) (params (order.get i))).prod =
            (order.map fun alpha => C.x alpha (params alpha)).prod := by
          change (List.ofFn ((fun alpha => C.x alpha (params alpha)) ∘ order.get)).prod = _
          rw [← List.map_ofFn, List.ofFn_get]
        _ = FilteredCollection.wordProduct C.x word := hparams.symm
    refine ⟨parameters, hparameters, ?_⟩
    · intro params' hparams'
      apply positiveRootOrderedProduct_injective_of_separateBase
        P e systemBase positiveBase C hPositive hpositive hAdd hActual hC order horder
      exact hparams'.trans hparameters.symm
  · rintro ⟨parameters, hparameters, _⟩
    rw [← hparameters]
    change (List.ofFn fun i => C.x (order.get i) (parameters i)).prod ∈
      RootSubgroupGenerated D positiveRoots
    apply Subgroup.list_prod_mem
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    apply rootSubgroup_le_RootSubgroupGenerated D
    · exact (horder.2 (order.get i)).mp (List.get_mem order i)
    · change C.x (order.get i) (parameters i) ∈
        (D.rootSubgroup (order.get i) : Set (Variety.Point K))
      rw [← (hC.1 (order.get i)).2]
      exact Set.mem_range_self _

end Theory.AlgebraicGroup
