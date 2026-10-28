module

public import Theory.GroupTheory.FilteredCollection
public import Theory.AlgebraicGroup.Borel.RootStructure.GeneralChevalleyRelatorAPI

/-!
# Collection of positive roots in a presented Chevalley group

This module proves that any finite word of positive-root formal `x` generators in
the quotient by the general Chevalley relators can be collected into any fixed
noduplicated ordering of the positive roots, with one field parameter for each root.
It is the presented-group normal form needed by the later Chevalley/Bruhat kernel
induction.

Root addition supplies the additive, zero, and inverse quotient equalities. For two
distinct positive roots, reducedness makes the roots linearly independent, so the
root-commutator relator exchanges their factors. The validity characterization for
the configured commutator order writes every correction root as a positive integral
combination. Base height therefore keeps the correction positive and raises its
degree strictly above both exchanged roots. The abstract finite filtered collector
then terminates at a height bound supplied by the chosen root order.

The relation data and relators are the source-faithful formal Chevalley presentation
from `theorem_1_12_1`; no geometric presentation theorem or Bruhat normal form is
used here.
-/

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem presentedChevalley_root_addition
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    (α : D.Root) (t s : k) :
    (PresentedGroup.of (.x α t) :
        PresentedGroup (generalChevalleyRelators data weights)) *
      PresentedGroup.of (.x α s) =
        PresentedGroup.of (.x α (t + s)) := by
  have hmem : formalRelation
      (formalChevalleyX α t * formalChevalleyX α s)
      (formalChevalleyX α (t + s)) ∈
        generalChevalleyRelators data weights := by
    rw [mem_generalChevalleyRelators (e := e) (base := base)]
    apply Or.inl
    rw [mem_universalChevalleyRelators]
    exact IsCommonChevalleyRelator.rootAddition α t s
  have hmem' :
      (formalChevalleyX α t * formalChevalleyX α s) *
          (formalChevalleyX α (t + s))⁻¹ ∈
        generalChevalleyRelators data weights := by
    simpa only [formalRelation_eq] using hmem
  simpa only [formalChevalleyX_eq, PresentedGroup.of, map_mul] using
    (PresentedGroup.mk_eq_mk_of_mul_inv_mem hmem')

public theorem presentedChevalley_root_zero
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T) (α : D.Root) :
    (PresentedGroup.of (.x α 0) :
      PresentedGroup (generalChevalleyRelators data weights)) = 1 := by
  have hadd := presentedChevalley_root_addition data weights α 0 0
  have hcancel :
      (PresentedGroup.of (.x α 0) :
          PresentedGroup (generalChevalleyRelators data weights)) *
          PresentedGroup.of (.x α 0) =
        PresentedGroup.of (.x α 0) * 1 := by
    simpa using hadd
  exact mul_left_cancel hcancel

public theorem presentedChevalley_root_inv
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T) (α : D.Root) (t : k) :
    (PresentedGroup.of (.x α (-t)) :
        PresentedGroup (generalChevalleyRelators data weights)) =
      (PresentedGroup.of (.x α t) :
        PresentedGroup (generalChevalleyRelators data weights))⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [presentedChevalley_root_addition data weights]
  simpa using presentedChevalley_root_zero data weights α

public theorem presentedChevalley_root_commutator
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    {α β : D.Root} (hLI : AreLinearlyIndependentRoots D P e α β)
    (t s : k) :
    (PresentedGroup.of (.x α t) :
        PresentedGroup (generalChevalleyRelators data weights))⁻¹ *
        (PresentedGroup.of (.x β s))⁻¹ *
        PresentedGroup.of (.x α t) * PresentedGroup.of (.x β s) =
      ((data.commutatorOrder α β).map fun q =>
        (PresentedGroup.of
          (.x q.root (data.commutatorCoefficient α β q * t ^ q.i * s ^ q.j)) :
          PresentedGroup (generalChevalleyRelators data weights))).prod := by
  have hmem : formalRelation
      ((formalChevalleyX α t)⁻¹ * (formalChevalleyX β s)⁻¹ *
        formalChevalleyX α t * formalChevalleyX β s)
      ((data.commutatorOrder α β).map fun q =>
        formalChevalleyX q.root
          (data.commutatorCoefficient α β q * t ^ q.i * s ^ q.j)).prod ∈
        generalChevalleyRelators data weights := by
    rw [mem_generalChevalleyRelators (e := e) (base := base)]
    apply Or.inl
    rw [mem_universalChevalleyRelators]
    exact IsCommonChevalleyRelator.rootCommutator α β hLI t s
  have hmem' :
      ((formalChevalleyX α t)⁻¹ * (formalChevalleyX β s)⁻¹ *
          formalChevalleyX α t * formalChevalleyX β s) *
        ((data.commutatorOrder α β).map fun q =>
          formalChevalleyX q.root
            (data.commutatorCoefficient α β q * t ^ q.i * s ^ q.j)).prod⁻¹ ∈
      generalChevalleyRelators data weights := by
    simpa only [formalRelation_eq] using hmem
  simpa only [formalChevalleyX_eq, PresentedGroup.of, map_mul, map_inv,
    map_list_prod, List.map_map, Function.comp_def] using
      (PresentedGroup.mk_eq_mk_of_mul_inv_mem hmem')

omit [IsAlgClosed k] in
private lemma positiveRoots_linearlyIndependent
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    {α β : D.Root} (hα : base.IsPos (e α)) (hβ : base.IsPos (e β))
    (hne : α ≠ β) :
    AreLinearlyIndependentRoots D P e α β := by
  let _ := P.indexNeg
  have hnotopp : P.root (e α) ≠ -P.root (e β) := by
    intro hneg
    have hidx : e α = P.reflectionPerm (e β) (e β) :=
      P.root_eq_neg_iff.mp hneg
    have hαneg : base.IsPos (-e β) := by simpa [hidx] using hα
    exact ((RootPairing.Base.IsPos.neg_iff_not
      (P := P) (b := base) (i := e β)).mp hαneg) hβ
  have hrootne : e α ≠ e β := fun heq => hne (e.injective heq)
  have hlin : LinearIndependent R ![P.root (e α), P.root (e β)] :=
    RootPairing.IsReduced.linearIndependent (P := P) hrootne hnotopp
  rw [LinearIndependent.pair_iff] at hlin
  simpa [AreLinearlyIndependentRoots] using hlin

omit [IsAlgClosed k] in
private lemma height_of_validChevalleyCommutatorTerm
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) {α β : D.Root}
    (q : ChevalleyCommutatorTerm D.Root)
    (hq : IsValidChevalleyCommutatorTerm D P e α β q) :
    base.height (e q.root) =
      (q.i : ℤ) * base.height (e α) +
        (q.j : ℤ) * base.height (e β) := by
  classical
  obtain ⟨f, -, -, hf⟩ := base.exists_root_eq_sum_int (e α)
  obtain ⟨g, -, -, hg⟩ := base.exists_root_eq_sum_int (e β)
  have hf : P.root (e α) = ∑ l ∈ base.support, f l • P.root l := by
    exact hf
  have hg : P.root (e β) = ∑ l ∈ base.support, g l • P.root l := by
    exact hg
  have hqexp : P.root (e q.root) =
      ∑ l ∈ base.support,
        ((q.i : ℤ) * f l + (q.j : ℤ) * g l) • P.root l := by
    have hq' : P.root (e q.root) =
        (q.i : ℤ) • P.root (e α) + (q.j : ℤ) • P.root (e β) := by
      have hqNat : P.root (e q.root) =
          q.i • P.root (e α) + q.j • P.root (e β) := by
        simpa only [Nat.cast_smul_eq_nsmul R] using hq.2.2
      rw [← natCast_zsmul (P.root (e α)) q.i,
        ← natCast_zsmul (P.root (e β)) q.j] at hqNat
      exact hqNat
    rw [hq', hf, hg]
    simp_rw [Finset.smul_sum, smul_smul, add_zsmul,
      Finset.sum_add_distrib]
  rw [base.height_eq_sum hqexp, base.height_eq_sum hf,
    base.height_eq_sum hg]
  simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

omit [IsAlgClosed k] in
private lemma validTerm_positive_and_degree_gt
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) {α β : D.Root}
    (hα : base.IsPos (e α)) (hβ : base.IsPos (e β))
    (q : ChevalleyCommutatorTerm D.Root)
    (hq : IsValidChevalleyCommutatorTerm D P e α β q) :
    base.IsPos (e q.root) ∧
      max (Int.toNat (base.height (e α)))
          (Int.toNat (base.height (e β))) <
        Int.toNat (base.height (e q.root)) := by
  rw [RootPairing.Base.isPos_iff] at hα hβ ⊢
  rw [height_of_validChevalleyCommutatorTerm D P e base q hq]
  have hi : (1 : ℤ) ≤ q.i := by exact_mod_cast hq.1
  have hj : (1 : ℤ) ≤ q.j := by exact_mod_cast hq.2.1
  constructor
  · nlinarith
  · apply max_lt
    · exact (Int.toNat_lt_toNat (by nlinarith)).mpr (by nlinarith)
    · exact (Int.toNat_lt_toNat (by nlinarith)).mpr (by nlinarith)

public theorem presentedChevalley_positiveRootWord_collect
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    (order : List D.Root) (horderNodup : order.Nodup)
    (horder : ∀ α, α ∈ order ↔ base.IsPos (e α))
    (word : List (D.Root × k))
    (hword : ∀ z ∈ word, base.IsPos (e z.1)) :
    ∃ params : D.Root → k,
      (word.map fun z =>
        (PresentedGroup.of (.x z.1 z.2) :
          PresentedGroup (generalChevalleyRelators data weights))).prod =
      (order.map fun α =>
        (PresentedGroup.of (.x α (params α)) :
          PresentedGroup (generalChevalleyRelators data weights))).prod := by
  classical
  let PositiveRoot := {α : D.Root // base.IsPos (e α)}
  let toPositiveRoot : {α : D.Root // α ∈ order} → PositiveRoot :=
    fun α => ⟨α.1, (horder α.1).mp α.2⟩
  let posOrder : List PositiveRoot :=
    order.attach.map toPositiveRoot
  have hposOrderVal : posOrder.map Subtype.val = order := by
    simp [posOrder, toPositiveRoot]
  have hposOrderNodup : posOrder.Nodup := by
    apply List.Nodup.of_map Subtype.val
    rw [hposOrderVal]
    exact horderNodup
  have hposOrderMem (α : PositiveRoot) : α ∈ posOrder := by
    have hval : α.1 ∈ posOrder.map Subtype.val := by
      rw [hposOrderVal]
      exact (horder α.1).mpr α.2
    obtain ⟨β, hβ, hβα⟩ := List.mem_map.mp hval
    have hEq : β = α := Subtype.ext hβα
    simpa [hEq] using hβ
  let posWord : List (PositiveRoot × k) :=
    word.attach.map fun z =>
      (⟨z.1.1, hword z.1 z.2⟩, z.1.2)
  let degree : PositiveRoot → ℕ :=
    fun α => Int.toNat (base.height (e α.1))
  let factor : PositiveRoot → k →
      PresentedGroup (generalChevalleyRelators data weights) :=
    fun α t => PresentedGroup.of (.x α.1 t)
  let degreeBound := (posOrder.map degree).sum + 1
  have hdegreeBound : ∀ α ∈ posOrder, degree α < degreeBound := by
    intro α hα
    have hmem : degree α ∈ posOrder.map degree := List.mem_map_of_mem hα
    exact (List.le_sum_of_mem hmem).trans_lt (Nat.lt_succ_self _)
  have hadd : ∀ α t s, factor α t * factor α s = factor α (t + s) := by
    intro α t s
    exact presentedChevalley_root_addition data weights α.1 t s
  have hswap : ∀ α β t s, α ≠ β →
      ∃ correction : List (PositiveRoot × k),
        (∀ z ∈ correction,
          z.1 ∈ posOrder ∧ max (degree α) (degree β) < degree z.1) ∧
        factor α t * factor β s =
          factor β s * factor α t *
            FilteredCollection.wordProduct factor correction := by
    intro α β t s hne
    have hLI : AreLinearlyIndependentRoots D P e α.1 β.1 :=
      positiveRoots_linearlyIndependent D P e base α.2 β.2
        (fun h => hne (Subtype.ext h))
    let correction : List (PositiveRoot × k) :=
      (data.commutatorOrder α.1 β.1).attach.map fun q =>
        let hqValid :=
          (data.commutatorOrderMem α.1 β.1 hLI q.1).mp q.2
        (⟨q.1.root,
            (validTerm_positive_and_degree_gt D P e base α.2 β.2 q.1 hqValid).1⟩,
          data.commutatorCoefficient α.1 β.1 q.1 * t ^ q.1.i * s ^ q.1.j)
    refine ⟨correction, ?_, ?_⟩
    · intro z hz
      simp only [correction, List.mem_map] at hz
      obtain ⟨q, -, rfl⟩ := hz
      dsimp only
      let hqValid :=
        (data.commutatorOrderMem α.1 β.1 hLI q.1).mp q.2
      exact ⟨hposOrderMem _,
        (validTerm_positive_and_degree_gt D P e base α.2 β.2 q.1 hqValid).2⟩
    · have hcorrection :
          FilteredCollection.wordProduct factor correction =
            ((data.commutatorOrder α.1 β.1).map fun q =>
              (PresentedGroup.of
                (.x q.root (data.commutatorCoefficient α.1 β.1 q *
                  t ^ q.i * s ^ q.j)) :
                PresentedGroup
                  (generalChevalleyRelators data weights))).prod := by
        simp [FilteredCollection.wordProduct, correction, factor]
      rw [hcorrection,
        ← presentedChevalley_root_commutator data weights hLI t s]
      dsimp only [factor]
      group
  have hposWord : ∀ z ∈ posWord, z.1 ∈ posOrder := by
    intro z hz
    exact hposOrderMem z.1
  obtain ⟨paramsPos, hcollect⟩ :=
    FilteredCollection.filteredCollection_exists_params degree factor posOrder
      hposOrderNodup degreeBound hdegreeBound hadd
      (fun α β t s _ _ hne => hswap α β t s hne) posWord hposWord
  let params : D.Root → k :=
    Function.extend Subtype.val paramsPos (fun _ => 0)
  have hparams (α : {α : D.Root // α ∈ order}) :
      params α.1 = paramsPos (toPositiveRoot α) := by
    simpa only [params] using
      (Subtype.val_injective.extend_apply paramsPos (fun _ => 0)
        (toPositiveRoot α))
  refine ⟨params, ?_⟩
  have hleft : FilteredCollection.wordProduct factor posWord =
      (word.map fun z =>
        (PresentedGroup.of (.x z.1 z.2) :
          PresentedGroup (generalChevalleyRelators data weights))).prod := by
    simp only [FilteredCollection.wordProduct, posWord, factor, List.map_map,
      Function.comp_def]
    exact congrArg List.prod (List.attach_map_val (l := word)
      (f := fun z =>
        (PresentedGroup.of (.x z.1 z.2) :
          PresentedGroup (generalChevalleyRelators data weights))))
  have hright :
      (posOrder.map fun α => factor α (paramsPos α)).prod =
        (order.map fun α =>
          (PresentedGroup.of (.x α (params α)) :
            PresentedGroup (generalChevalleyRelators data weights))).prod := by
    simp only [posOrder, factor, List.map_map, Function.comp_def]
    apply congrArg List.prod
    refine (List.map_congr_left (l := order.attach) ?_).trans
      (List.attach_map_val (l := order)
        (f := fun α =>
          (PresentedGroup.of (.x α (params α)) :
            PresentedGroup (generalChevalleyRelators data weights))))
    intro α hα
    rw [← hparams α]
  exact hleft.symm.trans (hcollect.trans hright)

end Theory.AlgebraicGroup
