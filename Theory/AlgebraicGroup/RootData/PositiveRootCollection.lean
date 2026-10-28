module

public import Theory.AlgebraicGroup.RootData.FilteredCollection
public import Theory.AlgebraicGroup.RootData.Chevalley
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
public import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear

/-!
# Arbitrary-order collection for positive Chevalley roots

This module specializes the filtered collector to a finite, binary-closed
support of positive roots.  The exchange word is obtained directly from the
Chevalley commutator formula.  The only non-formal point is that every root
`i α + j β` occurring in that formula remains in the chosen support: a
root-string descent subtracts one of the two input roots, using the positive
pairing identity and the exact root-addition realization.  A base aligned with
the positive system then gives positivity and strict growth of the filtration
degree; it need not be the base used to package the Chevalley system.

The group-theoretic input is the Chevalley commutator relation packaged by
`IsChevalleySystem`; the support argument uses Mathlib's finite
crystallographic root-string and reduced-root lemmas.  Mathematically this is
the standard collection argument following the Chevalley commutator relation
in GLS3, Section 1.12, with the abstract terminating collector supplied by
`FilteredCollection`.

The principal public theorem keeps the Chevalley-system base separate from the
positive-system base while exposing only the finite support, its exact binary
closure, an arbitrary duplicate-free enumeration, and a word supported there.
Correction support and height facts are derived internally.  The original
same-base statement remains as a compatibility wrapper.
-/

namespace Theory.AlgebraicGroup

universe u v w x y

open scoped BigOperators

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma positiveRoots_linearlyIndependent
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y} [Finite ι] [Field R] [CharZero R]
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
private lemma combination_ne_left
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) {α β γ : D.Root} {i j : ℕ}
    (_hi : 0 < i) (hj : 0 < j)
    (hroot : P.root (e γ) = (i : R) • P.root (e α) + (j : R) • P.root (e β))
    (hLI : AreLinearlyIndependentRoots D P e α β) : γ ≠ α := by
  intro h
  subst γ
  have hz : (1 - (i : R)) • P.root (e α) + (-(j : R)) • P.root (e β) = 0 := by
    calc
      (1 - (i : R)) • P.root (e α) + (-(j : R)) • P.root (e β) =
          P.root (e α) - ((i : R) • P.root (e α) + (j : R) • P.root (e β)) := by module
      _ = 0 := by rw [← hroot]; module
  have hz' := hLI (1 - (i : R)) (-(j : R)) hz
  have hjR : (j : R) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  exact hjR (neg_eq_zero.mp hz'.2)

omit [IsAlgClosed k] in
private lemma combination_ne_right
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) {α β γ : D.Root} {i j : ℕ}
    (hi : 0 < i) (_hj : 0 < j)
    (hroot : P.root (e γ) = (i : R) • P.root (e α) + (j : R) • P.root (e β))
    (hLI : AreLinearlyIndependentRoots D P e α β) : γ ≠ β := by
  intro h
  subst γ
  have hz : (-(i : R)) • P.root (e α) + (1 - (j : R)) • P.root (e β) = 0 := by
    calc
      (-(i : R)) • P.root (e α) + (1 - (j : R)) • P.root (e β) =
          P.root (e β) - ((i : R) • P.root (e α) + (j : R) • P.root (e β)) := by module
      _ = 0 := by rw [← hroot]; module
  have hz' := hLI (-(i : R)) (1 - (j : R)) hz
  have hiR : (i : R) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hi)
  exact hiR (neg_eq_zero.mp hz'.1)

omit [IsAlgClosed k] in
private lemma positive_combination_mem_support
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (support : Set D.Root)
    (hclosed : ∀ α β γ, α ∈ support → β ∈ support →
      D.add α β = some γ → γ ∈ support)
    {α β : D.Root} (hα : α ∈ support) (hβ : β ∈ support)
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hAdd : IsRootAdditionRealization D P e) :
    ∀ i j : ℕ, 0 < i → 0 < j → ∀ γ : D.Root,
      P.root (e γ) = (i : R) • P.root (e α) + (j : R) • P.root (e β) →
      γ ∈ support := by
  intro i j hi hj γ hroot
  let _ := Fintype.ofFinite ι
  generalize hn : i + j = n
  induction n using Nat.strong_induction_on generalizing i j γ with
  | h n ih =>
    have hpair : (2 : ℤ) = (i : ℤ) * P.pairingIn ℤ (e α) (e γ) +
        (j : ℤ) * P.pairingIn ℤ (e β) (e γ) := by
      have hrootZ : P.root (e γ) = (i : ℤ) • P.root (e α) +
          (j : ℤ) • P.root (e β) := by
        simpa only [natCast_zsmul, Nat.cast_smul_eq_nsmul R] using hroot
      have h := P.pairingIn_eq_add_of_root_eq_smul_add_smul
        (S := ℤ) (j := e γ) hrootZ
      rw [P.pairingIn_same] at h
      simpa [smul_eq_mul] using h
    have hiZ : (0 : ℤ) < i := by exact_mod_cast hi
    have hjZ : (0 : ℤ) < j := by exact_mod_cast hj
    have hpairing : 0 < P.pairingIn ℤ (e α) (e γ) ∨
        0 < P.pairingIn ℤ (e β) (e γ) := by
      by_contra! hn
      nlinarith
    by_cases hbase : i = 1 ∧ j = 1
    · rcases hbase with ⟨rfl, rfl⟩
      exact hclosed α β γ hα hβ (hAdd.add_of_root_eq_add (by simpa using hroot))
    rcases hpairing with hpaForward | hpbForward
    · have hpa : 0 < P.pairingIn ℤ (e γ) (e α) :=
        (P.zero_lt_pairingIn_iff (P.posRootForm ℤ) (e α) (e γ)).mp hpaForward
      have hne : e γ ≠ e α := fun h => combination_ne_left D P e hi hj hroot hLI
        (e.injective h)
      obtain ⟨δi, hδi⟩ := P.root_sub_root_mem_of_pairingIn_pos hpa hne
      have hi_gt : 1 < i := by
        by_contra hi_not
        have hi1 : i = 1 := by omega
        subst i
        let _ : IsAddTorsionFree M := IsAddTorsionFree.of_isTorsionFree R M
        let _ : j.AtLeastTwo := ⟨by omega⟩
        exact (P.nsmul_notMem_range_root (n := j) (i := e β)) ⟨δi, by
          rw [hδi, hroot]
          simp only [Nat.cast_one, one_smul, Nat.cast_smul_eq_nsmul R]
          module⟩
      let δ : D.Root := e.symm δi
      have hδroot : P.root (e δ) = P.root (e γ) - P.root (e α) := by
        simpa [δ] using hδi
      have hcomb : P.root (e δ) = ((i - 1 : ℕ) : R) • P.root (e α) +
          (j : R) • P.root (e β) := by
        rw [hδroot, hroot]
        rw [Nat.cast_sub (Nat.le_of_lt hi_gt)]
        module
      have hsmaller : i - 1 + j < n := by omega
      have hδmem : δ ∈ support := ih (i - 1 + j) hsmaller (i - 1) j
        (by omega) (by omega) δ hcomb (by omega)
      have hadd : D.add α δ = some γ := hAdd.add_of_root_eq_add (by
        rw [hδroot]
        module)
      exact hclosed α δ γ hα hδmem hadd
    · have hpb : 0 < P.pairingIn ℤ (e γ) (e β) :=
        (P.zero_lt_pairingIn_iff (P.posRootForm ℤ) (e β) (e γ)).mp hpbForward
      have hne : e γ ≠ e β := fun h => combination_ne_right D P e hi hj hroot hLI
        (e.injective h)
      obtain ⟨δi, hδi⟩ := P.root_sub_root_mem_of_pairingIn_pos hpb hne
      have hj_gt : 1 < j := by
        by_contra hj_not
        have hj1 : j = 1 := by omega
        subst j
        let _ : IsAddTorsionFree M := IsAddTorsionFree.of_isTorsionFree R M
        let _ : i.AtLeastTwo := ⟨by omega⟩
        exact (P.nsmul_notMem_range_root (n := i) (i := e α)) ⟨δi, by
          rw [hδi, hroot]
          simp only [Nat.cast_one, one_smul, Nat.cast_smul_eq_nsmul R]
          module⟩
      let δ : D.Root := e.symm δi
      have hδroot : P.root (e δ) = P.root (e γ) - P.root (e β) := by
        simpa [δ] using hδi
      have hcomb : P.root (e δ) = (i : R) • P.root (e α) +
          ((j - 1 : ℕ) : R) • P.root (e β) := by
        rw [hδroot, hroot]
        rw [Nat.cast_sub (Nat.le_of_lt hj_gt)]
        module
      have hsmaller : i + (j - 1) < n := by omega
      have hδmem : δ ∈ support := ih (i + (j - 1)) hsmaller i (j - 1) hi
        (by omega) δ hcomb (by omega)
      have hadd : D.add β δ = some γ := hAdd.add_of_root_eq_add (by
        rw [hδroot]
        module)
      exact hclosed β δ γ hβ hδmem hadd

omit [IsAlgClosed k] in
private lemma height_of_validChevalleyCommutatorTerm
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) {α β : D.Root}
    (q : ChevalleyCommutatorTerm D.Root)
    (hq : IsValidChevalleyCommutatorTerm D P e α β q) :
    base.height (e q.root) =
      (q.i : ℤ) * base.height (e α) + (q.j : ℤ) * base.height (e β) := by
  classical
  obtain ⟨f, -, -, hf⟩ := base.exists_root_eq_sum_int (e α)
  obtain ⟨g, -, -, hg⟩ := base.exists_root_eq_sum_int (e β)
  have hf : P.root (e α) = ∑ l ∈ base.support, f l • P.root l := hf
  have hg : P.root (e β) = ∑ l ∈ base.support, g l • P.root l := hg
  have hqexp : P.root (e q.root) =
      ∑ l ∈ base.support, ((q.i : ℤ) * f l + (q.j : ℤ) * g l) • P.root l := by
    have hq' : P.root (e q.root) = (q.i : ℤ) • P.root (e α) +
        (q.j : ℤ) • P.root (e β) := by
      simpa only [Nat.cast_smul_eq_nsmul R, ← natCast_zsmul] using hq.2.2
    rw [hq', hf, hg]
    simp_rw [Finset.smul_sum, smul_smul, add_zsmul, Finset.sum_add_distrib]
  rw [base.height_eq_sum hqexp, base.height_eq_sum hf, base.height_eq_sum hg]
  simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

omit [IsAlgClosed k] in
private lemma validTerm_positive_and_degree_gt
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) {α β : D.Root}
    (hα : base.IsPos (e α)) (hβ : base.IsPos (e β))
    (q : ChevalleyCommutatorTerm D.Root)
    (hq : IsValidChevalleyCommutatorTerm D P e α β q) :
    base.IsPos (e q.root) ∧
      max (Int.toNat (base.height (e α))) (Int.toNat (base.height (e β))) <
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

omit [IsAlgClosed k] in
/-- A finite word in a binary-closed set of positive Chevalley roots collects
to one parameter for each root, in any duplicate-free enumeration of that
support.  The base defining positivity and height may differ from the base in
the Chevalley-system data. -/
public theorem positiveRootChevalleyCollection_exists_params_of_separateBase
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (systemBase positiveBase : P.Base)
    (C : ChevalleyData K D)
    (hC : IsChevalleySystem D C P e systemBase)
    (hAdd : IsRootAdditionRealization D P e)
    {positiveRoots support : Set D.Root}
    (hpositive : ∀ α, α ∈ positiveRoots ↔ positiveBase.IsPos (e α))
    (hsupport_subset : ∀ α, α ∈ support → α ∈ positiveRoots)
    (hsupport_closed : ∀ α β γ, α ∈ support → β ∈ support →
      D.add α β = some γ → γ ∈ support)
    (order : List D.Root) (horderNodup : order.Nodup)
    (horder : ∀ α, α ∈ order ↔ α ∈ support)
    (word : List (D.Root × k))
    (hword : ∀ z ∈ word, z.1 ∈ support) :
    ∃ params : D.Root → k,
      FilteredCollection.wordProduct (fun α t => C.x α t) word =
        (order.map fun α => C.x α (params α)).prod := by
  classical
  let degree : D.Root → ℕ := fun α => Int.toNat (positiveBase.height (e α))
  let factor : D.Root → k → Variety.Point K := fun α t => C.x α t
  let degreeBound := (order.map degree).sum + 1
  have hdegreeBound : ∀ α ∈ order, degree α < degreeBound := by
    intro α hα
    have hmem : degree α ∈ order.map degree := List.mem_map_of_mem hα
    exact (List.le_sum_of_mem hmem).trans_lt (Nat.lt_succ_self _)
  have hadd : ∀ α t s, factor α t * factor α s = factor α (t + s) := by
    intro α t s
    exact hC.2.2.2.1 α t s
  have hswap : ∀ α β t s, α ∈ order → β ∈ order → α ≠ β →
      ∃ correction : List (D.Root × k),
        (∀ z ∈ correction, z.1 ∈ order ∧ max (degree α) (degree β) < degree z.1) ∧
        factor α t * factor β s = factor β s * factor α t *
          FilteredCollection.wordProduct factor correction := by
    intro α β t s hαorder hβorder hne
    have hαsupport := (horder α).mp hαorder
    have hβsupport := (horder β).mp hβorder
    have hαpos := (hpositive α).mp (hsupport_subset α hαsupport)
    have hβpos := (hpositive β).mp (hsupport_subset β hβsupport)
    have hLI : AreLinearlyIndependentRoots D P e α β :=
      positiveRoots_linearlyIndependent D P e positiveBase hαpos hβpos hne
    obtain ⟨commOrder, coefficient, _hnodup, _hpairwise, hvalid, _hcoeff, hformula⟩ :=
      hC.2.2.2.2.1 α β hLI
    let correction : List (D.Root × k) :=
      commOrder.attach.map fun q =>
        (q.1.root, coefficient q.1 * t ^ q.1.i * s ^ q.1.j)
    refine ⟨correction, ?_, ?_⟩
    · intro z hz
      simp only [correction, List.mem_map] at hz
      obtain ⟨q, -, rfl⟩ := hz
      let hqValid := (hvalid q.1).mp q.2
      have hqSupport : q.1.root ∈ support :=
        positive_combination_mem_support D P e support hsupport_closed
          hαsupport hβsupport hLI hAdd q.1.i q.1.j hqValid.1 hqValid.2.1 q.1.root hqValid.2.2
      have hqHeight := validTerm_positive_and_degree_gt
        D P e positiveBase hαpos hβpos q.1 hqValid
      exact ⟨(horder q.1.root).mpr hqSupport, hqHeight.2⟩
    · have hcorrection :
          FilteredCollection.wordProduct factor correction =
            (commOrder.map fun q => C.x q.root
              (coefficient q * t ^ q.i * s ^ q.j)).prod := by
        rw [FilteredCollection.wordProduct]
        dsimp [correction, factor]
        rw [List.map_map]
        change
          (commOrder.attach.map fun q =>
            C.x q.1.root (coefficient q.1 * t ^ q.1.i * s ^ q.1.j)).prod = _
        exact congrArg List.prod (List.attach_map_val
          (l := commOrder)
          (f := fun q => C.x q.root (coefficient q * t ^ q.i * s ^ q.j)))
      rw [hcorrection, ← hformula t s]
      dsimp only [factor]
      group
  have hword' : ∀ z ∈ word, z.1 ∈ order := by
    intro z hz
    exact (horder z.1).mpr (by exact hword z hz)
  obtain ⟨params, hcollect⟩ :=
    FilteredCollection.filteredCollection_exists_params degree factor order
      horderNodup degreeBound hdegreeBound hadd hswap word hword'
  exact ⟨params, hcollect⟩

omit [IsAlgClosed k] in
/-- Same-base compatibility wrapper for positive Chevalley collection. -/
public theorem positiveRootChevalleyCollection_exists_params
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι : Type v} {R : Type w} {M : Type x} {N : Type y} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (C : ChevalleyData K D)
    (hC : IsChevalleySystem D C P e base)
    (hAdd : IsRootAdditionRealization D P e)
    {positiveRoots support : Set D.Root}
    (hpositive : ∀ α, α ∈ positiveRoots ↔ base.IsPos (e α))
    (hsupport_subset : ∀ α, α ∈ support → α ∈ positiveRoots)
    (hsupport_closed : ∀ α β γ, α ∈ support → β ∈ support →
      D.add α β = some γ → γ ∈ support)
    (order : List D.Root) (horderNodup : order.Nodup)
    (horder : ∀ α, α ∈ order ↔ α ∈ support)
    (word : List (D.Root × k))
    (hword : ∀ z ∈ word, z.1 ∈ support) :
    ∃ params : D.Root → k,
      FilteredCollection.wordProduct (fun α t => C.x α t) word =
        (order.map fun α => C.x α (params α)).prod := by
  exact positiveRootChevalleyCollection_exists_params_of_separateBase
    P e base base C hC hAdd hpositive hsupport_subset hsupport_closed
      order horderNodup horder word hword

end Theory.AlgebraicGroup
