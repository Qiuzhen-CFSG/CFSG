module

public import Theory.AlgebraicGroup.Borel.AdjointCenter
public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.RootData.ChevalleyClassification
public import Theory.AlgebraicGroup.RootData.FilteredCollection
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.Commutator
public import Theory.AlgebraicGroup.RootSubgroups.Center
public import Theory.AlgebraicGroup.Unipotent.Radical

universe u

set_option linter.style.haveILetI false

/-! Exceptional Chevalley commutator collection and root-height filtrations. -/

/-! Collection infrastructure for products indexed by valid Chevalley commutator terms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-! The generic filtered collector is specialized below to Chevalley root words.
The adapter keeps the exchange law explicit: the Chevalley system supplies
same-root additivity, while a caller supplies the valid-term commutator word
and its strict degree increase.  No ordered-product membership is assumed. -/

public def ChevalleyCommutatorTerm.degree {Root : Type*}
    (q : ChevalleyCommutatorTerm Root) : ℕ :=
  q.i + q.j

public theorem chevalley_filteredCollection_exists_params
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base)
    (hC : IsChevalleySystem D C P e b)
    {α β : D.Root}
    (valid : ChevalleyCommutatorTerm D.Root → Prop)
    (_hvalid : ∀ q, valid q ↔ IsValidChevalleyCommutatorTerm D P e α β q)
    (order : List (ChevalleyCommutatorTerm D.Root))
    (horder : order.Nodup)
    (horderValid : ∀ q, q ∈ order ↔ valid q)
    (degreeBound : ℕ)
    (hbound : ∀ q ∈ order, q.degree < degreeBound)
    (hswap : ∀ p q a c, p ≠ q → valid p → valid q →
      ∃ correction : List
          (ChevalleyCommutatorTerm D.Root × k),
        (∀ z ∈ correction, valid z.1 ∧
          max p.degree q.degree < z.1.degree) ∧
        C.x p.root a * C.x q.root c =
          C.x q.root c * C.x p.root a *
            FilteredCollection.wordProduct
              (fun r t => C.x r.root t) correction)
    (word : List (ChevalleyCommutatorTerm D.Root × k))
    (hword : ∀ z ∈ word, valid z.1) :
    ∃ params : ChevalleyCommutatorTerm D.Root → k,
      ChevalleyCommutatorTermWordProduct C word =
        (order.map fun q => C.x q.root (params q)).prod := by
  let factor : ChevalleyCommutatorTerm D.Root → k → Variety.Point K :=
    fun q t => C.x q.root t
  have hadd : ∀ q a c, factor q a * factor q c = factor q (a + c) := by
    intro q a c
    exact hC.2.2.2.1 q.root a c
  obtain ⟨params, hparams⟩ :=
    FilteredCollection.filteredCollection_exists_params
      (degree := fun q => q.degree) factor order horder
      degreeBound hbound hadd
      (fun p q a c hpmem hqmem hpq => by
        obtain ⟨correction, hcorrection, hEq⟩ :=
          hswap p q a c hpq ((horderValid p).mp hpmem)
            ((horderValid q).mp hqmem)
        exact ⟨correction, by
          intro z hz
          exact ⟨(horderValid z.1).mpr (hcorrection z hz).1,
            (hcorrection z hz).2⟩, hEq⟩)
      word (by
        intro z hz
        exact (horderValid z.1).mpr (hword z hz))
  exact ⟨params, hparams⟩

private lemma validTerm_eq_of_root_eq
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    {q r : ChevalleyCommutatorTerm D.Root}
    (hq : IsValidChevalleyCommutatorTerm D P e α β q)
    (hr : IsValidChevalleyCommutatorTerm D P e α β r)
    (hroot : q.root = r.root) : q = r := by
  have heq :
      ((q.i : R) - (r.i : R)) • P.root (e α) +
        ((q.j : R) - (r.j : R)) • P.root (e β) = 0 := by
    calc
      _ = ((q.i : R) • P.root (e α) + (q.j : R) • P.root (e β)) -
          ((r.i : R) • P.root (e α) + (r.j : R) • P.root (e β)) := by module
      _ = P.root (e q.root) - P.root (e r.root) := by rw [← hq.2.2, ← hr.2.2]
      _ = 0 := by rw [hroot, sub_self]
  rcases hLI _ _ heq with ⟨hi, hj⟩
  have hi' : q.i = r.i := by exact_mod_cast (sub_eq_zero.mp hi)
  have hj' : q.j = r.j := by exact_mod_cast (sub_eq_zero.mp hj)
  cases q
  cases r
  simp_all

private def liftValidTerm
    {Root : Type*} (p q s : ChevalleyCommutatorTerm Root) :
    ChevalleyCommutatorTerm Root where
  i := s.i * p.i + s.j * q.i
  j := s.i * p.j + s.j * q.j
  root := s.root

private lemma liftValidTerm_valid
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) {α β : D.Root}
    {p q s : ChevalleyCommutatorTerm D.Root}
    (hp : IsValidChevalleyCommutatorTerm D P e α β p)
    (hq : IsValidChevalleyCommutatorTerm D P e α β q)
    (hs : IsValidChevalleyCommutatorTerm D P e p.root q.root s) :
    IsValidChevalleyCommutatorTerm D P e α β (liftValidTerm p q s) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [liftValidTerm]
    exact Nat.add_pos_left (Nat.mul_pos hs.1 hp.1) _
  · simp only [liftValidTerm]
    exact Nat.add_pos_left (Nat.mul_pos hs.1 hp.2.1) _
  simp only [liftValidTerm]
  rw [hs.2.2, hp.2.2, hq.2.2]
  push_cast
  module

private lemma liftValidTerm_ne_right
    {Root : Type*} {p q s : ChevalleyCommutatorTerm Root}
    (hp : 0 < p.i) (hs : 0 < s.i) (hsj : 0 < s.j) :
    liftValidTerm p q s ≠ q := by
  intro heq
  have hi := congrArg ChevalleyCommutatorTerm.i heq
  simp only [liftValidTerm] at hi
  have hleft : 0 < s.i * p.i := Nat.mul_pos hs hp
  have hright : q.i ≤ s.j * q.i := by
    calc
      q.i = 1 * q.i := by simp
      _ ≤ s.j * q.i := Nat.mul_le_mul_right q.i (Nat.succ_le_iff.mp hsj)
  omega

private lemma liftValidTerm_degree_gt
    {Root : Type*} {p q s : ChevalleyCommutatorTerm Root}
    (hp : 0 < p.i)
    (hs : 0 < s.i) (hsj : 0 < s.j) :
    q.degree < (liftValidTerm p q s).degree := by
  simp only [ChevalleyCommutatorTerm.degree, liftValidTerm]
  have hsp : 0 < s.i * (p.i + p.j) := Nat.mul_pos hs (Nat.add_pos_left hp _)
  have hq : q.i + q.j ≤ s.j * (q.i + q.j) := by
    calc
      q.i + q.j = 1 * (q.i + q.j) := by simp
      _ ≤ s.j * (q.i + q.j) := Nat.mul_le_mul_right _ (Nat.succ_le_iff.mp hsj)
  rw [show s.i * p.i + s.j * q.i + (s.i * p.j + s.j * q.j) =
    s.i * (p.i + p.j) + s.j * (q.i + q.j) by
      simp only [Nat.mul_add]
      omega]
  omega

private lemma exists_validChevalleyCommutatorTerm_of_valid_roots
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) {α β : D.Root}
    {p q s : ChevalleyCommutatorTerm D.Root}
    (hp : IsValidChevalleyCommutatorTerm D P e α β p)
    (hq : IsValidChevalleyCommutatorTerm D P e α β q)
    (hs : IsValidChevalleyCommutatorTerm D P e p.root q.root s) :
    ∃ r : ChevalleyCommutatorTerm D.Root,
      IsValidChevalleyCommutatorTerm D P e α β r ∧
        q.degree < r.degree ∧ r.root = s.root := by
  exact ⟨liftValidTerm p q s, liftValidTerm_valid D P e hp hq hs,
    liftValidTerm_degree_gt hp.1 hs.1 hs.2.1, rfl⟩

private lemma validTerm_roots_linearlyIndependent
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    {p q : ChevalleyCommutatorTerm D.Root}
    (hp : IsValidChevalleyCommutatorTerm D P e α β p)
    (hq : IsValidChevalleyCommutatorTerm D P e α β q)
    (hpq : p ≠ q) :
    AreLinearlyIndependentRoots D P e p.root q.root := by
  have hrootne : e p.root ≠ e q.root := by
    intro heq
    apply hpq
    apply validTerm_eq_of_root_eq D P e hLI hp hq
    exact e.injective heq
  have hnotopp : P.root (e p.root) ≠ -P.root (e q.root) := by
    intro hopp
    have heq :
        ((p.i : R) + (q.i : R)) • P.root (e α) +
          ((p.j : R) + (q.j : R)) • P.root (e β) = 0 := by
      calc
        _ = ((p.i : R) • P.root (e α) + (p.j : R) • P.root (e β)) +
            ((q.i : R) • P.root (e α) + (q.j : R) • P.root (e β)) := by module
        _ = P.root (e p.root) + P.root (e q.root) := by rw [← hp.2.2, ← hq.2.2]
        _ = 0 := by rw [hopp]; module
    have hi := (hLI _ _ heq).1
    have hiNat : p.i + q.i = 0 := by exact_mod_cast hi
    have hpi : 0 < p.i := hp.1
    omega
  have hlin : LinearIndependent R ![P.root (e p.root), P.root (e q.root)] :=
    RootPairing.IsReduced.linearIndependent (P := P) hrootne hnotopp
  rw [LinearIndependent.pair_iff] at hlin
  simpa [AreLinearlyIndependentRoots] using hlin

private lemma chevalleyCommutatorTermWordProduct_extract_avoiding
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hC : IsChevalleySystem D C P e b)
    (q : ChevalleyCommutatorTerm D.Root)
    (hq : IsValidChevalleyCommutatorTerm D P e α β q)
    (forbidden : List (ChevalleyCommutatorTerm D.Root))
    (hforbidden : ∀ r ∈ forbidden,
      IsValidChevalleyCommutatorTerm D P e α β r ∧ r.degree ≤ q.degree)
    (word : List (ChevalleyCommutatorTerm D.Root × k))
    (hword : ∀ z ∈ word,
      IsValidChevalleyCommutatorTerm D P e α β z.1 ∧ z.1 ∉ forbidden) :
    ∃ t : k, ∃ residual : List (ChevalleyCommutatorTerm D.Root × k),
      (∀ z ∈ residual,
        IsValidChevalleyCommutatorTerm D P e α β z.1 ∧ z.1 ∉ q :: forbidden) ∧
      ChevalleyCommutatorTermWordProduct C word =
        C.x q.root t * ChevalleyCommutatorTermWordProduct C residual := by
  induction word with
  | nil =>
      refine ⟨0, [], ?_, ?_⟩
      · simp
      · simp [ChevalleyCommutatorTermWordProduct]
        have hadd := hC.2.2.2.1 q.root 0 0
        have hcancel : C.x q.root 0 * C.x q.root 0 = C.x q.root 0 * 1 := by
          simpa using hadd
        rw [mul_left_cancel hcancel]
  | cons z word ih =>
      have hz := hword z (by simp)
      have htail : ∀ y ∈ word,
          IsValidChevalleyCommutatorTerm D P e α β y.1 ∧ y.1 ∉ forbidden := by
        intro y hy
        exact hword y (by simp [hy])
      rcases ih htail with ⟨t, residual, hresidual, hprod⟩
      rcases z with ⟨p, a⟩
      by_cases hpq : p = q
      · subst p
        refine ⟨a + t, residual, hresidual, ?_⟩
        change C.x q.root a * ChevalleyCommutatorTermWordProduct C word =
          C.x q.root (a + t) * ChevalleyCommutatorTermWordProduct C residual
        rw [hprod, ← mul_assoc, hC.2.2.2.1]
      · have hLIpq := validTerm_roots_linearlyIndependent D P e hLI hz.1 hq hpq
        rcases hC.2.2.2.2.1 p.root q.root hLIpq with
          ⟨correctionOrder, c, hnodup, hpairwise, hvalid, hcoeff, hformula⟩
        let correctionWord : List (ChevalleyCommutatorTerm D.Root × k) :=
          correctionOrder.map fun s =>
            (liftValidTerm p q s, c s * a ^ s.i * t ^ s.j)
        refine ⟨t, (p, a) :: correctionWord ++ residual, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨hz.1, by simp [hpq, hz.2]⟩
          · rcases List.mem_append.mp hy with hy | hy
            · rw [List.mem_map] at hy
              rcases hy with ⟨s, hs, rfl⟩
              have hsvalid := (hvalid s).mp hs
              refine ⟨liftValidTerm_valid D P e hz.1 hq hsvalid, ?_⟩
              simp only [List.mem_cons, not_or]
              refine ⟨liftValidTerm_ne_right hz.1.1 hsvalid.1 hsvalid.2.1, ?_⟩
              intro hmem
              obtain ⟨_, hrdeg⟩ := hforbidden _ hmem
              have hgt : q.degree < (liftValidTerm p q s).degree :=
                liftValidTerm_degree_gt (q := q)
                  (show 0 < p.i from hz.1.1) hsvalid.1 hsvalid.2.1
              exact (Nat.not_lt_of_ge hrdeg) hgt
            · exact hresidual y hy
        · change C.x p.root a * ChevalleyCommutatorTermWordProduct C word =
            C.x q.root t * ChevalleyCommutatorTermWordProduct C
              ((p, a) :: correctionWord ++ residual)
          rw [hprod]
          have hcomm := hformula a t
          have hswap : C.x p.root a * C.x q.root t =
              C.x q.root t * C.x p.root a *
                (correctionOrder.map fun s =>
                  C.x s.root (c s * a ^ s.i * t ^ s.j)).prod := by
            rw [← hcomm]
            group
          rw [← mul_assoc, hswap]
          dsimp [correctionWord, ChevalleyCommutatorTermWordProduct]
          simp [liftValidTerm, Function.comp_def, mul_assoc]

private lemma chevalleyCommutatorTermWordProduct_extract
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hC : IsChevalleySystem D C P e b)
    (q : ChevalleyCommutatorTerm D.Root)
    (hq : IsValidChevalleyCommutatorTerm D P e α β q)
    (word : List (ChevalleyCommutatorTerm D.Root × k))
    (hword : ∀ z ∈ word,
      IsValidChevalleyCommutatorTerm D P e α β z.1) :
    ∃ t : k, ∃ residual : List (ChevalleyCommutatorTerm D.Root × k),
      (∀ z ∈ residual,
        IsValidChevalleyCommutatorTerm D P e α β z.1 ∧ z.1 ≠ q) ∧
      ChevalleyCommutatorTermWordProduct C word =
        C.x q.root t * ChevalleyCommutatorTermWordProduct C residual := by
  induction word with
  | nil =>
      refine ⟨0, [], ?_, ?_⟩
      · simp
      · simp [ChevalleyCommutatorTermWordProduct]
        have hx0 : C.x q.root 0 = 1 := by
          have hadd := hC.2.2.2.1 q.root 0 0
          have hcancel : C.x q.root 0 * C.x q.root 0 = C.x q.root 0 * 1 := by
            simpa using hadd
          exact mul_left_cancel hcancel
        rw [hx0]
  | cons z word ih =>
      have hzvalid := hword z (by simp)
      have htail : ∀ y ∈ word,
          IsValidChevalleyCommutatorTerm D P e α β y.1 := by
        intro y hy
        exact hword y (by simp [hy])
      rcases ih htail with ⟨t, residual, hresidual, hprod⟩
      rcases z with ⟨p, a⟩
      by_cases hpq : p = q
      · subst p
        refine ⟨a + t, residual, hresidual, ?_⟩
        change C.x q.root a * ChevalleyCommutatorTermWordProduct C word =
          C.x q.root (a + t) * ChevalleyCommutatorTermWordProduct C residual
        rw [hprod, ← mul_assoc, hC.2.2.2.1]
      · have hLIpq := validTerm_roots_linearlyIndependent D P e hLI hzvalid hq hpq
        rcases hC.2.2.2.2.1 p.root q.root hLIpq with
          ⟨correctionOrder, c, hnodup, hpairwise, hvalid, hcoeff, hformula⟩
        let correctionWord : List (ChevalleyCommutatorTerm D.Root × k) :=
          correctionOrder.map fun s =>
            (liftValidTerm p q s, c s * a ^ s.i * t ^ s.j)
        refine ⟨t, (p, a) :: correctionWord ++ residual, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨hzvalid, hpq⟩
          · rcases List.mem_append.mp hy with hy | hy
            · rw [List.mem_map] at hy
              rcases hy with ⟨s, hs, rfl⟩
              have hsvalid := (hvalid s).mp hs
              exact ⟨liftValidTerm_valid D P e hzvalid hq hsvalid,
                liftValidTerm_ne_right hzvalid.1 hsvalid.1 hsvalid.2.1⟩
            · exact hresidual y hy
        · change C.x p.root a * ChevalleyCommutatorTermWordProduct C word =
            C.x q.root t * ChevalleyCommutatorTermWordProduct C ((p, a) :: correctionWord ++ residual)
          rw [hprod]
          have hcomm := hformula a t
          have hswap : C.x p.root a * C.x q.root t =
              C.x q.root t * C.x p.root a *
                (correctionOrder.map fun s =>
                  C.x s.root (c s * a ^ s.i * t ^ s.j)).prod := by
            rw [← hcomm]
            group
          rw [← mul_assoc, hswap]
          dsimp [correctionWord, ChevalleyCommutatorTermWordProduct]
          simp [liftValidTerm, Function.comp_def, mul_assoc]

variable {k : Type u} [Field k]

/-- The explicit parameter-combination law for two factors with the same
Chevalley commutator root.  This is the local merge step used when a higher
correction word contains repeated roots. -/
private lemma chevalleyCommutatorTerm_sameRoot_parameter_combine
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base)
    (hC : IsChevalleySystem D C P e b)
    (q : ChevalleyCommutatorTerm D.Root) (a t : k) :
    C.x q.root a * C.x q.root t = C.x q.root (a + t) := by
  exact hC.2.2.2.1 q.root a t

variable {k : Type u} [Field k]

/-! Degree-filtered collection for products indexed by Chevalley commutator terms. -/

private lemma chevalleyCommutatorTermWordProduct_collect
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hC : IsChevalleySystem D C P e b)
    (processed order : List (ChevalleyCommutatorTerm D.Root))
    (hprocessed : ∀ r ∈ processed,
      IsValidChevalleyCommutatorTerm D P e α β r)
    (hprocessedDegree : ∀ r ∈ processed, ∀ q ∈ order,
      r.degree ≤ q.degree)
    (horderNodup : order.Nodup)
    (horderDegree : order.Pairwise fun q r => q.degree ≤ r.degree)
    (horder : ∀ q, q ∈ order ↔
      IsValidChevalleyCommutatorTerm D P e α β q ∧ q ∉ processed)
    (word : List (ChevalleyCommutatorTerm D.Root × k))
    (hword : ∀ z ∈ word,
      IsValidChevalleyCommutatorTerm D P e α β z.1 ∧ z.1 ∉ processed) :
    ∃ params : ChevalleyCommutatorTerm D.Root → k,
      ChevalleyCommutatorTermWordProduct C word =
        (order.map fun q => C.x q.root (params q)).prod := by
  classical
  induction order generalizing processed word with
  | nil =>
      have hwordNil : word = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro z hz
        obtain ⟨hzvalid, hznot⟩ := hword z hz
        have := (horder z.1).mpr ⟨hzvalid, hznot⟩
        simp at this
      subst word
      exact ⟨fun _ => 0, by simp [ChevalleyCommutatorTermWordProduct]⟩
  | cons q tail ih =>
      have hqtail := List.pairwise_cons.mp horderDegree
      have hqdata := (horder q).mp (by simp)
      have hqnotTail : q ∉ tail := (List.nodup_cons.mp horderNodup).1
      have hforbidden : ∀ r ∈ processed,
          IsValidChevalleyCommutatorTerm D P e α β r ∧ r.degree ≤ q.degree := by
        intro r hr
        exact ⟨hprocessed r hr, hprocessedDegree r hr q (by simp)⟩
      rcases chevalleyCommutatorTermWordProduct_extract_avoiding
          D C P e b hLI hC q hqdata.1 processed hforbidden word hword with
        ⟨t, residual, hresidual, hproduct⟩
      have hprocessed' : ∀ r ∈ q :: processed,
          IsValidChevalleyCommutatorTerm D P e α β r := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hqdata.1
        · exact hprocessed r hr
      have hprocessedDegree' : ∀ r ∈ q :: processed, ∀ s ∈ tail,
          r.degree ≤ s.degree := by
        intro r hr s hs
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hqtail.1 s hs
        · exact hprocessedDegree r hr s (by simp [hs])
      have horderTail : ∀ r, r ∈ tail ↔
          IsValidChevalleyCommutatorTerm D P e α β r ∧ r ∉ q :: processed := by
        intro r
        constructor
        · intro hr
          have hrdata := (horder r).mp (by simp [hr])
          exact ⟨hrdata.1, by simp [hrdata.2, ne_of_mem_of_not_mem hr hqnotTail]⟩
        · rintro ⟨hrvalid, hrnot⟩
          have hrnotProcessed : r ∉ processed := by
            intro hr
            exact hrnot (by simp [hr])
          have hrOrder := (horder r).mpr ⟨hrvalid, hrnotProcessed⟩
          rcases List.mem_cons.mp hrOrder with rfl | hr
          · exact False.elim (hrnot (by simp))
          · exact hr
      rcases ih (processed := q :: processed) hprocessed' hprocessedDegree'
          (List.nodup_cons.mp horderNodup).2 hqtail.2 horderTail residual hresidual with
        ⟨params, hresidualProduct⟩
      refine ⟨fun r => if r = q then t else params r, ?_⟩
      rw [hproduct, hresidualProduct]
      simp only [List.map_cons, List.prod_cons, if_pos]
      congr 1
      apply congrArg List.prod
      apply List.map_congr_left
      intro r hr
      have hrne : r ≠ q := by
        intro hrq
        subst r
        exact hqnotTail hr
      simp [hrne]

/-! An explicit adjacent-exchange interface for order changes.

The premise only supplies a two-factor parameter exchange.  The theorem then
propagates that exchange through `List.Perm` and returns a target word with the
requested term order.  In the actual Chevalley commutator problem, swapping
non-maximal terms also emits higher-degree correction factors, so this is the
small pure-exchange layer; the higher-degree splice remains a separate route.
-/

private lemma chevalleyCommutatorTermWordProduct_targetWord_of_adjacent_exchange
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (_b : P.Base) {α β : D.Root}
    (word : List (ChevalleyCommutatorTerm D.Root × k))
    (order : List (ChevalleyCommutatorTerm D.Root))
    (hperm : List.Perm (word.map Prod.fst) order)
    (hvalid : ∀ q, q ∈ order →
      IsValidChevalleyCommutatorTerm D P e α β q)
    (hSwap : ∀ p q : ChevalleyCommutatorTerm D.Root, ∀ a c : k,
      IsValidChevalleyCommutatorTerm D P e α β p →
      IsValidChevalleyCommutatorTerm D P e α β q →
      ∃ a' c' : k,
        C.x p.root a * C.x q.root c =
          C.x q.root c' * C.x p.root a') :
    ∃ targetWord : List (ChevalleyCommutatorTerm D.Root × k),
      targetWord.map Prod.fst = order ∧
      (word.map (fun z => C.x z.1.root z.2)).prod =
        (targetWord.map (fun z => C.x z.1.root z.2)).prod := by
  let aux : ∀ (terms : List (ChevalleyCommutatorTerm D.Root)),
      ∀ (w : List (ChevalleyCommutatorTerm D.Root × k)),
      w.map Prod.fst = terms →
      ∀ (ord : List (ChevalleyCommutatorTerm D.Root)),
      List.Perm terms ord →
      (∀ q, q ∈ ord →
        IsValidChevalleyCommutatorTerm D P e α β q) →
      ∃ targetWord : List (ChevalleyCommutatorTerm D.Root × k),
        targetWord.map Prod.fst = ord ∧
        (w.map (fun z => C.x z.1.root z.2)).prod =
          (targetWord.map (fun z => C.x z.1.root z.2)).prod := by
    intro terms w hmap ord hperm hord
    induction hperm generalizing w with
    | nil =>
      cases w with
      | nil => exact ⟨[], by simp, by simp⟩
      | cons z rest => cases hmap
    | @cons x l₁ l₂ hperm ih =>
      cases w with
      | nil => cases hmap
      | cons z rest =>
          have hmap' : z.1 :: rest.map Prod.fst = x :: l₁ := by
            simpa using hmap
          have hz : z.1 = x := (List.cons.inj hmap').1
          subst x
          have hrest : rest.map Prod.fst = l₁ :=
            (List.cons.inj hmap').2
          have hvalidTail : ∀ q, q ∈ l₂ →
              IsValidChevalleyCommutatorTerm D P e α β q := by
            intro q hq
            exact hord q (by simp [hq])
          obtain ⟨tw, htw, hprod⟩ := ih (w := rest) hrest hvalidTail
          refine ⟨(z.1, z.2) :: tw, ?_, ?_⟩
          · simp [htw]
          · simp only [List.map_cons, List.prod_cons]
            rw [hprod]
    | @swap x y l =>
      cases w with
      | nil => cases hmap
      | cons z rest =>
          cases rest with
          | nil => cases hmap
          | cons z' rest =>
              have hmap' : z.1 :: z'.1 :: rest.map Prod.fst = y :: x :: l := by
                simpa using hmap
              have hz : z.1 = y := (List.cons.inj hmap').1
              have htail : z'.1 :: rest.map Prod.fst = x :: l :=
                (List.cons.inj hmap').2
              have hz' : z'.1 = x := (List.cons.inj htail).1
              have hrest : rest.map Prod.fst = l :=
                (List.cons.inj htail).2
              subst y
              subst x
              have hvalidY := hord z.1 (by simp)
              have hvalidX := hord z'.1 (by simp)
              obtain ⟨a', c', hswap⟩ :=
                hSwap z.1 z'.1 z.2 z'.2 hvalidY hvalidX
              refine ⟨(z'.1, c') :: (z.1, a') :: rest, ?_, ?_⟩
              · simp [hrest]
              · simp only [List.map_cons, List.prod_cons]
                calc
                  C.x z.1.root z.2 *
                        (C.x z'.1.root z'.2 *
                          (rest.map (fun z => C.x z.1.root z.2)).prod) =
                      (C.x z.1.root z.2 * C.x z'.1.root z'.2) *
                        (rest.map (fun z => C.x z.1.root z.2)).prod := by
                          rw [mul_assoc]
                  _ = (C.x z'.1.root c' * C.x z.1.root a') *
                        (rest.map (fun z => C.x z.1.root z.2)).prod := by
                          rw [hswap]
                  _ = C.x z'.1.root c' *
                        (C.x z.1.root a' *
                          (rest.map (fun z => C.x z.1.root z.2)).prod) := by
                          rw [mul_assoc]
    | @trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ =>
      have hvalidMid : ∀ q, q ∈ l₂ →
          IsValidChevalleyCommutatorTerm D P e α β q := by
        intro q hq
        exact hord q ((List.Perm.mem_iff h₂).mp hq)
      obtain ⟨tw₁, htw₁, hprod₁⟩ :=
        ih₁ (w := w) hmap hvalidMid
      obtain ⟨tw₂, htw₂, hprod₂⟩ :=
        ih₂ (w := tw₁) (by simp [htw₁]) hord
      exact ⟨tw₂, htw₂, hprod₁.trans hprod₂⟩

  exact aux (word.map Prod.fst) word rfl order hperm hvalid

/-! The subgroup generated by strictly higher commutator terms is normalized by lower terms. -/

open scoped commutatorElement

variable {k : Type u} [Field k]

private def ChevalleyCommutatorTermAboveDegreeRoots
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (α β : D.Root) (d : ℕ) : Set D.Root :=
  {γ | ∃ q : ChevalleyCommutatorTerm D.Root,
    IsValidChevalleyCommutatorTerm D P e α β q ∧ d < q.degree ∧ q.root = γ}

private def ChevalleyCommutatorTermAboveDegreeSubgroup
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (α β : D.Root) (d : ℕ) :
    Subgroup (Variety.Point K) :=
  RootSubgroupGenerated D (ChevalleyCommutatorTermAboveDegreeRoots D P e α β d)

private lemma chevalleyCommutatorTermAboveDegreeSubgroup_mem_normalizer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hC : IsChevalleySystem D C P e b)
    (p : ChevalleyCommutatorTerm D.Root)
    (hp : IsValidChevalleyCommutatorTerm D P e α β p)
    (d : ℕ) (hpd : p.degree ≤ d) (t : k) :
    C.x p.root t ∈ Subgroup.normalizer
      (ChevalleyCommutatorTermAboveDegreeSubgroup D P e α β d : Set (Variety.Point K)) := by
  classical
  let H := ChevalleyCommutatorTermAboveDegreeSubgroup D P e α β d
  have hrootNeg (γ : D.Root) (a : k) :
      C.x γ (-a) = (C.x γ a)⁻¹ := by
    have hzero : C.x γ 0 = 1 := by
      simpa using hC.2.2.2.1 γ 0 0
    have hmul : C.x γ a * C.x γ (-a) = 1 := by
      rw [hC.2.2.2.1]
      simpa using hzero
    exact eq_inv_of_mul_eq_one_right hmul
  have hconjGenerator (a : k) :
      ∀ z ∈ ⋃ γ ∈ ChevalleyCommutatorTermAboveDegreeRoots D P e α β d,
        (D.rootSubgroup γ : Set (Variety.Point K)),
        C.x p.root a * z * (C.x p.root a)⁻¹ ∈ H := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    rcases hz with ⟨γ, hγhigh, hzγ⟩
    rcases hγhigh with ⟨q, hq, hdq, hqroot⟩
    subst γ
    have hpq : p ≠ q := by
      intro heq
      subst q
      omega
    have hLIpq := validTerm_roots_linearlyIndependent D P e hLI hp hq hpq
    have hzRange : z ∈ Set.range (C.x q.root) := by
      rw [(hC.1 q.root).2]
      exact hzγ
    rcases hzRange with ⟨u, rfl⟩
    rcases hC.2.2.2.2.1 p.root q.root hLIpq with
      ⟨order, coeff, hnodup, hdegree, hvalid, hcoeff, hformula⟩
    have hterm : ∀ s ∈ order,
        C.x s.root (coeff s * (-a) ^ s.i * (-u) ^ s.j) ∈ H := by
      intro s hs
      have hsvalid := (hvalid s).mp hs
      rcases exists_validChevalleyCommutatorTerm_of_valid_roots D P e hp hq hsvalid with
        ⟨r, hrvalid, hqr, hrroot⟩
      apply rootSubgroup_le_RootSubgroupGenerated D
        (show s.root ∈ ChevalleyCommutatorTermAboveDegreeRoots D P e α β d from
          ⟨r, hrvalid, lt_trans hdq hqr, hrroot⟩)
      have hxmem : C.x s.root (coeff s * (-a) ^ s.i * (-u) ^ s.j) ∈
          Set.range (C.x s.root) := Set.mem_range_self _
      rw [(hC.1 s.root).2] at hxmem
      exact hxmem
    have hproduct :
        (order.map fun s => C.x s.root
          (coeff s * (-a) ^ s.i * (-u) ^ s.j)).prod ∈ H := by
      exact Subgroup.list_prod_mem H (by
        intro x hx
        rw [List.mem_map] at hx
        rcases hx with ⟨s, hs, rfl⟩
        exact hterm s hs)
    have hcommutator : ⁅C.x p.root a, C.x q.root u⁆ ∈ H := by
      have hf := hformula (-a) (-u)
      rw [hrootNeg p.root a, hrootNeg q.root u] at hf
      simp only [inv_inv] at hf
      rw [commutatorElement_def, hf]
      exact hproduct
    have hyH : C.x q.root u ∈ H := by
      apply rootSubgroup_le_RootSubgroupGenerated D
        (show q.root ∈ ChevalleyCommutatorTermAboveDegreeRoots D P e α β d from
          ⟨q, hq, hdq, rfl⟩)
      have hxmem : C.x q.root u ∈ Set.range (C.x q.root) := Set.mem_range_self _
      rw [(hC.1 q.root).2] at hxmem
      exact hxmem
    simpa [commutatorElement_def, mul_assoc] using H.mul_mem hcommutator hyH
  have hconj (a : k) : ∀ z ∈ H, C.x p.root a * z * (C.x p.root a)⁻¹ ∈ H := by
    intro z hz
    change z ∈ RootSubgroupGenerated D
      (ChevalleyCommutatorTermAboveDegreeRoots D P e α β d) at hz
    rw [RootSubgroupGenerated] at hz
    refine Subgroup.closure_induction
      (p := fun z _ => C.x p.root a * z * (C.x p.root a)⁻¹ ∈ H)
      (k := ⋃ γ ∈ ChevalleyCommutatorTermAboveDegreeRoots D P e α β d,
        (D.rootSubgroup γ : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hz
    · exact hconjGenerator a
    · simp only [mul_one, mul_inv_cancel]
      exact H.one_mem
    · intro x y hx hy ihx ihy
      simpa [mul_assoc] using H.mul_mem ihx ihy
    · intro x hx ihx
      simpa [_root_.mul_inv_rev, mul_assoc] using H.inv_mem ihx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact hconj t z
  · intro hz
    have hInv : C.x p.root (-t) * (C.x p.root t * z * (C.x p.root t)⁻¹) *
        (C.x p.root (-t))⁻¹ ∈ H :=
      hconj (-t) (C.x p.root t * z * (C.x p.root t)⁻¹) hz
    rw [hrootNeg p.root t] at hInv
    simpa [mul_assoc] using hInv

/-! Maximal-degree valid Chevalley terms commute with every valid term. -/

variable {k : Type u} [Field k]

private lemma chevalleyCommutatorTerm_maxDegree_commutes
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hC : IsChevalleySystem D C P e b)
    (q : ChevalleyCommutatorTerm D.Root)
    (hq : IsValidChevalleyCommutatorTerm D P e α β q)
    (hmax : ∀ r, IsValidChevalleyCommutatorTerm D P e α β r →
      r.degree ≤ q.degree)
    (p : ChevalleyCommutatorTerm D.Root)
    (hp : IsValidChevalleyCommutatorTerm D P e α β p)
    (a c : k) :
    Commute (C.x p.root a) (C.x q.root c) := by
  by_cases hpq : p = q
  · subst p
    rw [Commute]
    calc
      C.x q.root a * C.x q.root c = C.x q.root (a + c) := hC.2.2.2.1 q.root a c
      _ = C.x q.root (c + a) := by rw [add_comm]
      _ = C.x q.root c * C.x q.root a := (hC.2.2.2.1 q.root c a).symm
  have hLIpq := validTerm_roots_linearlyIndependent D P e hLI hp hq hpq
  rcases hC.2.2.2.2.1 p.root q.root hLIpq with
    ⟨correctionOrder, coeff, hnodup, hdegree, hvalid, hcoeff, hformula⟩
  have hcorrectionNil : correctionOrder = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro s hs
    have hsvalid := (hvalid s).mp hs
    rcases exists_validChevalleyCommutatorTerm_of_valid_roots D P e hp hq hsvalid with
      ⟨r, hrvalid, hqr, hroot⟩
    exact (Nat.not_lt_of_ge (hmax r hrvalid)) hqr
  have hone : (C.x p.root a)⁻¹ * (C.x q.root c)⁻¹ *
      C.x p.root a * C.x q.root c = 1 := by
    simpa [hcorrectionNil] using hformula a c
  have hleft := congrArg (fun z => C.x p.root a * z) hone
  have hright := congrArg (fun z => C.x q.root c * z) hleft
  have hcomm : C.x p.root a * C.x q.root c =
      C.x q.root c * C.x p.root a := by
    simpa [mul_assoc] using hright
  exact hcomm

private lemma chevalleyCommutatorTermWordProduct_commutes_maxDegree
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hC : IsChevalleySystem D C P e b)
    (q : ChevalleyCommutatorTerm D.Root)
    (hq : IsValidChevalleyCommutatorTerm D P e α β q)
    (hmax : ∀ r, IsValidChevalleyCommutatorTerm D P e α β r →
      r.degree ≤ q.degree)
    (word : List (ChevalleyCommutatorTerm D.Root × k))
    (hword : ∀ z ∈ word,
      IsValidChevalleyCommutatorTerm D P e α β z.1)
    (c : k) :
    Commute (ChevalleyCommutatorTermWordProduct C word) (C.x q.root c) := by
  apply Commute.list_prod_left
  intro x hx
  rw [List.mem_map] at hx
  rcases hx with ⟨z, hz, rfl⟩
  exact chevalleyCommutatorTerm_maxDegree_commutes D C P e b hLI hC q hq hmax
    z.1 (hword z hz) z.2 c

private lemma chevalleyCommutatorTermWordProduct_move_maxDegree_front
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hC : IsChevalleySystem D C P e b)
    (q : ChevalleyCommutatorTerm D.Root)
    (hq : IsValidChevalleyCommutatorTerm D P e α β q)
    (hmax : ∀ r, IsValidChevalleyCommutatorTerm D P e α β r →
      r.degree ≤ q.degree)
    (left right : List (ChevalleyCommutatorTerm D.Root × k))
    (hleft : ∀ z ∈ left,
      IsValidChevalleyCommutatorTerm D P e α β z.1)
    (c : k) :
    ChevalleyCommutatorTermWordProduct C (left ++ (q, c) :: right) =
      C.x q.root c *
        ChevalleyCommutatorTermWordProduct C (left ++ right) := by
  have hcomm := chevalleyCommutatorTermWordProduct_commutes_maxDegree
    D C P e b hLI hC q hq hmax left hleft c
  have hcommEq :
      (left.map fun z => C.x z.1.root z.2).prod * C.x q.root c =
        C.x q.root c * (left.map fun z => C.x z.1.root z.2).prod := by
    simpa [ChevalleyCommutatorTermWordProduct] using hcomm.eq
  simp only [ChevalleyCommutatorTermWordProduct, List.map_append,
    List.map_cons, List.prod_append, List.prod_cons]
  rw [← mul_assoc, hcommEq, mul_assoc]

/-! Moving a higher-degree accumulator across a lower Chevalley root factor. -/

variable {k : Type u} [Field k]

private lemma chevalleyCommutatorTermAboveDegreeSubgroup_mul_rootElement_exists
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hC : IsChevalleySystem D C P e b)
    (p : ChevalleyCommutatorTerm D.Root)
    (hp : IsValidChevalleyCommutatorTerm D P e α β p)
    (d : ℕ) (hpd : p.degree ≤ d) (t : k)
    (z : Variety.Point K)
    (hz : z ∈ ChevalleyCommutatorTermAboveDegreeSubgroup D P e α β d) :
    ∃ z' ∈ ChevalleyCommutatorTermAboveDegreeSubgroup D P e α β d,
      z * C.x p.root t = C.x p.root t * z' := by
  let H := ChevalleyCommutatorTermAboveDegreeSubgroup D P e α β d
  let x := C.x p.root t
  have hxnorm : x ∈ Subgroup.normalizer (H : Set (Variety.Point K)) :=
    chevalleyCommutatorTermAboveDegreeSubgroup_mem_normalizer D C P e b hLI hC p hp d hpd t
  have hxinvnorm : x⁻¹ ∈ Subgroup.normalizer (H : Set (Variety.Point K)) :=
    (Subgroup.normalizer (H : Set (Variety.Point K))).inv_mem hxnorm
  have hz' : x⁻¹ * z * x ∈ H := by
    rw [Subgroup.mem_normalizer_iff] at hxinvnorm
    have := (hxinvnorm z).mp hz
    simpa [mul_assoc] using this
  refine ⟨x⁻¹ * z * x, hz', ?_⟩
  simp [x, mul_assoc]

/-! Words supported in strictly higher commutator degrees lie in the high subgroup. -/

variable {k : Type u} [Field k]

private lemma chevalleyCommutatorTermWordProduct_mem_aboveDegreeSubgroup
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hC : IsChevalleySystem D C P e b) (d : ℕ)
    (word : List (ChevalleyCommutatorTerm D.Root × k))
    (hword : ∀ q ∈ word,
      IsValidChevalleyCommutatorTerm D P e α β q.1 ∧ d < q.1.degree) :
    ChevalleyCommutatorTermWordProduct C word ∈
      ChevalleyCommutatorTermAboveDegreeSubgroup D P e α β d := by
  apply Subgroup.list_prod_mem
  intro x hx
  rw [List.mem_map] at hx
  rcases hx with ⟨q, hq, rfl⟩
  have hqdata := hword q hq
  apply rootSubgroup_le_RootSubgroupGenerated D
    (show q.1.root ∈ ChevalleyCommutatorTermAboveDegreeRoots D P e α β d from
      ⟨q.1, hqdata.1, hqdata.2, rfl⟩)
  have hxmem : C.x q.1.root q.2 ∈ Set.range (C.x q.1.root) :=
    Set.mem_range_self _
  rw [(hC.1 q.1.root).2] at hxmem
  exact hxmem

/-! Moving a higher-degree accumulator across a word of lower-degree root factors. -/

variable {k : Type u} [Field k]

private lemma chevalleyCommutatorTermAboveDegreeSubgroup_mul_word_exists
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hC : IsChevalleySystem D C P e b)
    (d : ℕ)
    (word : List (ChevalleyCommutatorTerm D.Root × k))
    (hword : ∀ q ∈ word,
      IsValidChevalleyCommutatorTerm D P e α β q.1 ∧ q.1.degree ≤ d)
    (z : Variety.Point K)
    (hz : z ∈ ChevalleyCommutatorTermAboveDegreeSubgroup D P e α β d) :
    ∃ z' ∈ ChevalleyCommutatorTermAboveDegreeSubgroup D P e α β d,
      z * ChevalleyCommutatorTermWordProduct C word =
        ChevalleyCommutatorTermWordProduct C word * z' := by
  induction word generalizing z with
  | nil =>
      exact ⟨z, hz, by simp [ChevalleyCommutatorTermWordProduct]⟩
  | cons q tail ih =>
      have hq := hword q (by simp)
      have htail : ∀ r ∈ tail,
          IsValidChevalleyCommutatorTerm D P e α β r.1 ∧ r.1.degree ≤ d := by
        intro r hr
        exact hword r (by simp [hr])
      obtain ⟨z₁, hz₁, hmove₁⟩ :=
        chevalleyCommutatorTermAboveDegreeSubgroup_mul_rootElement_exists
          D C P e b hLI hC q.1 hq.1 d hq.2 q.2 z hz
      obtain ⟨z₂, hz₂, hmove₂⟩ := ih htail z₁ hz₁
      refine ⟨z₂, hz₂, ?_⟩
      simp only [ChevalleyCommutatorTermWordProduct, List.map_cons, List.prod_cons] at hmove₂ ⊢
      rw [← mul_assoc, hmove₁, mul_assoc, hmove₂, ← mul_assoc]

/-! Elements of the high subgroup have finite words in high valid root factors. -/

variable {k : Type u} [Field k]

private lemma chevalleyCommutatorTermAboveDegreeSubgroup_exists_word
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hC : IsChevalleySystem D C P e b) (d : ℕ)
    (z : Variety.Point K)
    (hz : z ∈ ChevalleyCommutatorTermAboveDegreeSubgroup D P e α β d) :
    ∃ word : List (ChevalleyCommutatorTerm D.Root × k),
      (∀ q ∈ word,
        IsValidChevalleyCommutatorTerm D P e α β q.1 ∧ d < q.1.degree) ∧
      z = ChevalleyCommutatorTermWordProduct C word := by
  classical
  have hrootNeg (γ : D.Root) (a : k) : C.x γ (-a) = (C.x γ a)⁻¹ := by
    have hzero : C.x γ 0 = 1 := by
      simpa using hC.2.2.2.1 γ 0 0
    have hmul : C.x γ a * C.x γ (-a) = 1 := by
      rw [hC.2.2.2.1]
      simpa using hzero
    exact eq_inv_of_mul_eq_one_right hmul
  have hwordInv : ∀ word : List (ChevalleyCommutatorTerm D.Root × k),
      (ChevalleyCommutatorTermWordProduct C word)⁻¹ =
        ChevalleyCommutatorTermWordProduct C
          (word.reverse.map fun q => (q.1, -q.2)) := by
    intro word
    induction word with
    | nil => simp [ChevalleyCommutatorTermWordProduct]
    | cons q tail ih =>
        have ih' := ih
        simp only [ChevalleyCommutatorTermWordProduct] at ih'
        simp only [ChevalleyCommutatorTermWordProduct, List.map_cons, List.prod_cons,
          List.reverse_cons, List.map_append, List.map_map, List.prod_append,
          mul_inv_rev]
        rw [ih', hrootNeg]
        simp [Function.comp_def]
  change z ∈ RootSubgroupGenerated D
    (ChevalleyCommutatorTermAboveDegreeRoots D P e α β d) at hz
  rw [RootSubgroupGenerated] at hz
  refine Subgroup.closure_induction
    (p := fun z _ => ∃ word : List (ChevalleyCommutatorTerm D.Root × k),
      (∀ q ∈ word,
        IsValidChevalleyCommutatorTerm D P e α β q.1 ∧ d < q.1.degree) ∧
      z = ChevalleyCommutatorTermWordProduct C word)
    (k := ⋃ γ ∈ ChevalleyCommutatorTermAboveDegreeRoots D P e α β d,
      (D.rootSubgroup γ : Set (Variety.Point K))) ?_ ?_ ?_ ?_ hz
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨γ, ⟨q, hqvalid, hqd, hqroot⟩, hxγ⟩
    subst γ
    have hxRange : x ∈ Set.range (C.x q.root) := by
      rw [(hC.1 q.root).2]
      exact hxγ
    rcases hxRange with ⟨t, rfl⟩
    exact ⟨[(q, t)], by simp [hqvalid, hqd], by
      simp [ChevalleyCommutatorTermWordProduct]⟩
  · exact ⟨[], by simp, by simp [ChevalleyCommutatorTermWordProduct]⟩
  · intro x y hx hy
    rintro ⟨wordX, hwordX, rfl⟩ ⟨wordY, hwordY, rfl⟩
    refine ⟨wordX ++ wordY, ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hwordX q hq
      · exact hwordY q hq
    · simp [ChevalleyCommutatorTermWordProduct]
  · intro x hx
    rintro ⟨word, hword, rfl⟩
    refine ⟨word.reverse.map fun q => (q.1, -q.2), ?_, hwordInv word⟩
    intro q hq
    rw [List.mem_map] at hq
    rcases hq with ⟨r, hr, rfl⟩
    exact hword r (List.mem_reverse.mp hr)

/-! A strictly higher correction word moves across a lower-degree target word. -/

variable {k : Type u} [Field k]

private lemma chevalleyCommutatorTermAboveDegreeWord_mul_lowWord_exists
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hC : IsChevalleySystem D C P e b)
    (d : ℕ)
    (highWord lowWord : List (ChevalleyCommutatorTerm D.Root × k))
    (hhigh : ∀ q ∈ highWord,
      IsValidChevalleyCommutatorTerm D P e α β q.1 ∧ d < q.1.degree)
    (hlow : ∀ q ∈ lowWord,
      IsValidChevalleyCommutatorTerm D P e α β q.1 ∧ q.1.degree ≤ d) :
    ∃ z ∈ ChevalleyCommutatorTermAboveDegreeSubgroup D P e α β d,
      ChevalleyCommutatorTermWordProduct C highWord *
          ChevalleyCommutatorTermWordProduct C lowWord =
        ChevalleyCommutatorTermWordProduct C lowWord * z := by
  have hmem := chevalleyCommutatorTermWordProduct_mem_aboveDegreeSubgroup
    D C P e b hC d highWord hhigh
  exact chevalleyCommutatorTermAboveDegreeSubgroup_mul_word_exists
    D C P e b hLI hC d lowWord hlow
      (ChevalleyCommutatorTermWordProduct C highWord) hmem

/-! Explicit higher-degree accumulator splicing.

The theorem combines the high-subgroup mover with its finite-word expansion.
It exposes the resulting correction word and its termwise degree bound, so a
later distributed collection induction can splice parameters without storing
the desired ordered-product conclusion in a setup structure.
-/

variable {k : Type u} [Field k]

private lemma chevalleyCommutatorTermAboveDegreeWord_splice_lowWord_exists
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hC : IsChevalleySystem D C P e b)
    (d : ℕ)
    (highWord lowWord : List (ChevalleyCommutatorTerm D.Root × k))
    (hhigh : ∀ q ∈ highWord,
      IsValidChevalleyCommutatorTerm D P e α β q.1 ∧ d < q.1.degree)
    (hlow : ∀ q ∈ lowWord,
      IsValidChevalleyCommutatorTerm D P e α β q.1 ∧ q.1.degree ≤ d) :
    ∃ highWord' : List (ChevalleyCommutatorTerm D.Root × k),
      (∀ q ∈ highWord',
        IsValidChevalleyCommutatorTerm D P e α β q.1 ∧ d < q.1.degree) ∧
      ChevalleyCommutatorTermWordProduct C highWord *
          ChevalleyCommutatorTermWordProduct C lowWord =
        ChevalleyCommutatorTermWordProduct C lowWord *
          ChevalleyCommutatorTermWordProduct C highWord' := by
  have hhighMem :
      ChevalleyCommutatorTermWordProduct C highWord ∈
        ChevalleyCommutatorTermAboveDegreeSubgroup D P e α β d :=
    chevalleyCommutatorTermWordProduct_mem_aboveDegreeSubgroup
      D C P e b hC d highWord hhigh
  obtain ⟨z', hz', hmove⟩ :=
    chevalleyCommutatorTermAboveDegreeSubgroup_mul_word_exists
      D C P e b hLI hC d lowWord hlow
        (ChevalleyCommutatorTermWordProduct C highWord) hhighMem
  obtain ⟨highWord', hhighWord', hzEq⟩ :=
    chevalleyCommutatorTermAboveDegreeSubgroup_exists_word
      D C P e b hC d z' hz'
  refine ⟨highWord', hhighWord', ?_⟩
  rw [hmove, hzEq]

variable {k : Type u} [Field k]

@[expose]
public def OrderedRootSubgroupProduct
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (order : List D.Root) : Set (Variety.Point K) :=
  {g | ∃ factor : D.Root → Variety.Point K,
    (∀ α ∈ order, factor α ∈ D.rootSubgroup α) ∧
      g = (order.map factor).prod}

@[expose]
public def IsClosedRootSubset
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (A : Set D.Root) : Prop :=
  ∀ α ∈ A, ∀ β ∈ A, ∀ γ, D.add α β = some γ → γ ∈ A

private lemma chevalleyCommutator_mem_orderedRootSubgroupProduct_self
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base)
    (hC : IsChevalleySystem D C P e b)
    (α : D.Root) (order : List (ChevalleyCommutatorTerm D.Root))
    (x y : Variety.Point K) (hx : x ∈ D.rootSubgroup α)
    (hy : y ∈ D.rootSubgroup α) :
    x⁻¹ * y⁻¹ * x * y ∈
      OrderedRootSubgroupProduct D (order.map (·.root)) := by
  have hxRange : x ∈ Set.range (C.x α) := by
    simpa [hC.1 α |>.2] using hx
  have hyRange : y ∈ Set.range (C.x α) := by
    simpa [hC.1 α |>.2] using hy
  rcases hxRange with ⟨t, rfl⟩
  rcases hyRange with ⟨u, rfl⟩
  have hcommute : Commute (C.x α t) (C.x α u) := by
    rw [Commute]
    calc
      C.x α t * C.x α u = C.x α (t + u) := hC.2.2.2.1 α t u
      _ = C.x α (u + t) := by rw [add_comm]
      _ = C.x α u * C.x α t := (hC.2.2.2.1 α u t).symm
  have hone : (C.x α t)⁻¹ * (C.x α u)⁻¹ * C.x α t * C.x α u = 1 := by
    calc
      _ = (C.x α u * C.x α t)⁻¹ * (C.x α t * C.x α u) := by
        rw [mul_inv_rev]
        simp only [mul_assoc]
      _ = (C.x α t * C.x α u)⁻¹ * (C.x α t * C.x α u) := by
        rw [hcommute.eq]
      _ = 1 := by simp
  rw [hone]
  refine ⟨fun _ => 1, ?_, by simp [Function.comp_def]⟩
  intro γ hγ
  exact (D.rootSubgroup γ).one_mem

private lemma positiveRoots_linearlyIndependent
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (positiveRoots : Set D.Root)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ base.IsPos (e α))
    {α β : D.Root} (hα : α ∈ positiveRoots) (hβ : β ∈ positiveRoots)
    (hne : α ≠ β) :
    AreLinearlyIndependentRoots D P e α β := by
  letI := P.indexNeg
  have hαPos : base.IsPos (e α) := (hPositiveRoots α).mp hα
  have hβPos : base.IsPos (e β) := (hPositiveRoots β).mp hβ
  have hnotopp : P.root (e α) ≠ -P.root (e β) := by
    intro hneg
    have hidx : e α = P.reflectionPerm (e β) (e β) := P.root_eq_neg_iff.mp hneg
    have hαPos' : base.IsPos (-e β) := by simpa [hidx] using hαPos
    have hβnot : ¬base.IsPos (e β) :=
      (RootPairing.Base.IsPos.neg_iff_not (P := P) (b := base) (i := e β)).mp hαPos'
    exact hβnot hβPos
  have hrootne : e α ≠ e β := fun heq => hne (e.injective heq)
  have hlin : LinearIndependent R ![P.root (e α), P.root (e β)] :=
    RootPairing.IsReduced.linearIndependent (P := P) hrootne hnotopp
  rw [LinearIndependent.pair_iff] at hlin
  simpa [AreLinearlyIndependentRoots] using hlin

private lemma chevalleyTermProduct_mem_orderedRootSubgroupProduct
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hC : IsChevalleySystem D C P e b)
    (order : List (ChevalleyCommutatorTerm D.Root))
    (horder : ∀ q ∈ order, IsValidChevalleyCommutatorTerm D P e α β q)
    (params : ChevalleyCommutatorTerm D.Root → k) :
    (order.map fun q => C.x q.root (params q)).prod ∈
      OrderedRootSubgroupProduct D (order.map (·.root)) := by
  classical
  let factor : D.Root → Variety.Point K := fun γ =>
    if h : ∃ q, q ∈ order ∧ q.root = γ then
      C.x γ (params (Classical.choose h))
    else 1
  have hfactor (q : ChevalleyCommutatorTerm D.Root) (hq : q ∈ order) :
      factor q.root = C.x q.root (params q) := by
    dsimp [factor]
    split
    next h =>
      let r := Classical.choose h
      have hr := Classical.choose_spec h
      have hre : r = q := by
        apply validTerm_eq_of_root_eq D P e hLI (horder r hr.1) (horder q hq)
        exact hr.2
      change C.x q.root (params r) = C.x q.root (params q)
      rw [hre]
    next h => exact False.elim (h ⟨q, hq, rfl⟩)
  refine ⟨factor, ?_, ?_⟩
  · intro γ hγ
    rcases List.mem_map.mp hγ with ⟨q, hq, rfl⟩
    rw [hfactor q hq]
    have hxmem : C.x q.root (params q) ∈ Set.range (C.x q.root) :=
      Set.mem_range_self (params q)
    rw [(hC.1 q.root).2] at hxmem
    exact hxmem
  · simp only [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro q hq
    exact (hfactor q hq).symm

public theorem chevalleySystem_commutator_mem_orderedRootSubgroupProduct_of_degreeOrder
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hC : IsChevalleySystem D C P e base)
    (positiveRoots : Set D.Root)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ base.IsPos (e α))
    (α : D.Root) (hα : α ∈ positiveRoots)
    (β : D.Root) (hβ : β ∈ positiveRoots)
    (order : List (ChevalleyCommutatorTerm D.Root))
    (horderNodup : order.Nodup)
    (horderDegree : order.Pairwise fun q r => q.degree ≤ r.degree)
    (horder : ∀ q, q ∈ order ↔
      IsValidChevalleyCommutatorTerm D P e α β q)
    (x : Variety.Point K) (hx : x ∈ D.rootSubgroup α)
    (y : Variety.Point K) (hy : y ∈ D.rootSubgroup β) :
    x⁻¹ * y⁻¹ * x * y ∈
      OrderedRootSubgroupProduct D (order.map (·.root)) := by
  by_cases hEq : α = β
  · subst β
    exact chevalleyCommutator_mem_orderedRootSubgroupProduct_self
      D C P e base hC α order x y hx hy
  have hLI := positiveRoots_linearlyIndependent D P e base positiveRoots
    hPositiveRoots hα hβ hEq
  have hxRange : x ∈ Set.range (C.x α) := by
    simpa [hC.1 α |>.2] using hx
  have hyRange : y ∈ Set.range (C.x β) := by
    simpa [hC.1 β |>.2] using hy
  rcases hxRange with ⟨t, rfl⟩
  rcases hyRange with ⟨u, rfl⟩
  rcases hC.2.2.2.2.1 α β hLI with
    ⟨canonicalOrder, c, hcanonicalNodup, hcanonicalDegree,
      hcanonical, hcoeff, hformula⟩
  let word : List (ChevalleyCommutatorTerm D.Root × k) :=
    canonicalOrder.map fun q => (q, c q * t ^ q.i * u ^ q.j)
  have hword : ∀ z ∈ word,
      IsValidChevalleyCommutatorTerm D P e α β z.1 := by
    intro z hz
    rw [List.mem_map] at hz
    rcases hz with ⟨q, hq, rfl⟩
    exact (hcanonical q).mp hq
  rcases chevalleyCommutatorTermWordProduct_collect D C P e base hLI hC
      [] order (by simp) (by simp) horderNodup horderDegree
      (by simpa using horder) word (by
        intro z hz
        exact ⟨hword z hz, by simp⟩) with ⟨params, hcollect⟩
  have hwordFormula : ChevalleyCommutatorTermWordProduct C word =
      (canonicalOrder.map fun q => C.x q.root
        (c q * t ^ q.i * u ^ q.j)).prod := by
    simp [word, ChevalleyCommutatorTermWordProduct, Function.comp_def]
  have hcommutator :
      (C.x α t)⁻¹ * (C.x β u)⁻¹ * C.x α t * C.x β u =
        (order.map fun q => C.x q.root (params q)).prod := by
    rw [hformula t u, ← hwordFormula, hcollect]
  rw [hcommutator]
  exact chevalleyTermProduct_mem_orderedRootSubgroupProduct D C P e base
    hLI hC order (fun q hq => (horder q).mp hq) params

@[expose]
public def IsRootIdealIn
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (P A : Set D.Root) : Prop :=
  A ⊆ P ∧ ∀ α ∈ A, ∀ β ∈ P, ∀ γ, D.add α β = some γ → γ ∈ A

open scoped commutatorElement
variable {k : Type u} [Field k]

public def IsLowestRoot
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots : Set D.Root)
    (lowestRoot : D.Root) : Prop :=
  lowestRoot ∉ positiveRoots ∧
    ∀ β, β ∉ positiveRoots → D.height lowestRoot ≤ D.height β

private lemma initialHeight_filtration
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (Uheight : ℕ → ClosedSubgroup K)
    (hDP : IsRootSystemRealization D P e b)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α}) :
    (Uheight 1).toSubgroup = U.toSubgroup ∧
      (∀ i, 0 < i → Uheight i ≤ U) ∧
      (∀ i, 0 < i →
        (Uheight (i + 1)).toSubgroup ≤ (Uheight i).toSubgroup) := by
  have hHeightPositive : positiveRoots = {α | (1 : ℤ) ≤ D.height α} := by
    ext α
    rw [hPositiveRoots]
    change b.IsPos (e α) ↔ (1 : ℤ) ≤ D.height α
    rw [RootPairing.Base.isPos_iff, ← hDP.2.2.2.2 α]
    omega
  constructor
  · calc
      (Uheight 1).toSubgroup =
          RootSubgroupGenerated D {α | (1 : ℤ) ≤ D.height α} := by
            simpa using hUheight 1 (by omega)
      _ = RootSubgroupGenerated D positiveRoots := by rw [hHeightPositive]
      _ = U.toSubgroup := hU.symm
  constructor
  · intro i hi
    change (Uheight i).toSubgroup ≤ U.toSubgroup
    rw [hUheight i hi, hU]
    apply RootSubgroupGenerated_mono D
    intro α hα
    rw [hHeightPositive]
    change (1 : ℤ) ≤ D.height α
    exact le_trans (by exact_mod_cast hi) hα
  · intro i hi
    rw [hUheight (i + 1) (by omega), hUheight i hi]
    apply RootSubgroupGenerated_mono D
    intro α hα
    change (i : ℤ) ≤ D.height α
    exact le_trans (by omega) hα

private lemma heightFiltration_commutator
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (Uheight : ℕ → ClosedSubgroup K)
    (hDP : IsRootSystemRealization D P e b)
    (hC : IsChevalleySystem D C P e b)
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α}) :
    ∀ i, 0 < i → ⁅(Uheight i).toSubgroup, U.toSubgroup⁆ ≤
      (Uheight (i + 1)).toSubgroup := by
  classical
  choose coeff hCoeffSupport hCoeffSign hCoeffRoot using
    fun β => b.exists_root_eq_sum_int β
  have hCoeff : HasSimpleRootExpansion P b coeff := by
    intro β
    constructor
    · simpa [Int.cast_smul_eq_zsmul] using hCoeffRoot β
    · intro γ hγ
      by_contra hne
      exact hγ (hCoeffSupport β hne)
  have hRelativeHeight (α : D.Root) :
      RelativeRootHeight coeff b.support (e '' (∅ : Set D.Root)) (e α) =
        D.height α := by
    rw [hDP.2.2.2.2 α]
    rw [b.height_eq_sum (by
      simpa [Int.cast_smul_eq_zsmul] using (hCoeff (e α)).1)]
    simp [RelativeRootHeight]
  have hSeries (n : ℕ) :
      RelativeRootSeries D e b.support coeff (∅ : Set D.Root) n =
        RootSubgroupGenerated D {α | (n : ℤ) ≤ D.height α} := by
    unfold RelativeRootSeries
    congr 1
    ext α
    simp only [Set.mem_ofPred_eq]
    rw [hRelativeHeight α]
  have hHeightPositive : positiveRoots = {α | (1 : ℤ) ≤ D.height α} := by
    ext α
    rw [hPositiveRoots]
    change b.IsPos (e α) ↔ (1 : ℤ) ≤ D.height α
    rw [RootPairing.Base.isPos_iff, ← hDP.2.2.2.2 α]
    omega
  intro i hi
  rw [hUheight i hi, ← hSeries i]
  have hUeq : U.toSubgroup =
      RelativeRootSeries D e b.support coeff (∅ : Set D.Root) 1 :=
    hU.trans ((congrArg (RootSubgroupGenerated D) hHeightPositive).trans
      (hSeries 1).symm)
  rw [hUeq]
  rw [hUheight (i + 1) (by omega), ← hSeries (i + 1)]
  exact relativeRootSeries_commutator_series_le
    D C P e b coeff hCoeff hC ∅ i hi

/-- Every positive height layer is normal in the unipotent group. -/
public theorem heightFiltration_normal
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (Uheight : ℕ → ClosedSubgroup K)
    (hDP : IsRootSystemRealization D P e b)
    (hC : IsChevalleySystem D C P e b)
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (i : ℕ) (hi : 0 < i) :
    ((Uheight i).toSubgroup.subgroupOf U.toSubgroup).Normal := by
  letI := Fintype.ofFinite ι
  rcases initialHeight_filtration T U D P e b positiveRoots Uheight
      hDP hPositiveRoots hU hUheight with ⟨_, hHeightLe, hDescending⟩
  have hComm := heightFiltration_commutator T U D C P e b positiveRoots
    Uheight hDP hC hU hPositiveRoots hUheight i hi
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    (show (Uheight i).toSubgroup ≤ U.toSubgroup from hHeightLe i hi)]
  rw [Subgroup.le_normalizer_iff_commutator_le_left]
  exact hComm.trans (hDescending i hi)

/-- The first height layer is the chosen positive-root subgroup. -/
public lemma heightFiltration_first_eq
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (Uheight : ℕ → ClosedSubgroup K)
    (hDP : IsRootSystemRealization D P e b)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α}) :
    (Uheight 1).toSubgroup = U.toSubgroup := by
  letI := Fintype.ofFinite ι
  exact (initialHeight_filtration T U D P e b positiveRoots Uheight
    hDP hPositiveRoots hU hUheight).1

/-- Every positive height layer is contained in the chosen unipotent group. -/
public lemma heightFiltration_le_unipotent
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (Uheight : ℕ → ClosedSubgroup K)
    (hDP : IsRootSystemRealization D P e b)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α}) :
    ∀ i, 0 < i → Uheight i ≤ U := by
  letI := Fintype.ofFinite ι
  exact (initialHeight_filtration T U D P e b positiveRoots Uheight
    hDP hPositiveRoots hU hUheight).2.1

/-- The height filtration is antitone from the first positive layer onward. -/
public lemma heightFiltration_antitone
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (Uheight : ℕ → ClosedSubgroup K)
    (hDP : IsRootSystemRealization D P e b)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α}) :
    ∀ i, 0 < i →
      (Uheight (i + 1)).toSubgroup ≤ (Uheight i).toSubgroup := by
  letI := Fintype.ofFinite ι
  exact (initialHeight_filtration T U D P e b positiveRoots Uheight
    hDP hPositiveRoots hU hUheight).2.2

private lemma terminalHeight_exists
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (lowestRoot : D.Root) (Uheight : ℕ → ClosedSubgroup K)
    (hD : D.IsRealization) (hDP : IsRootSystemRealization D P e b)
    (hPositive : IsPositiveSystem D positiveRoots)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hLowest : IsLowestRoot D positiveRoots lowestRoot)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (c : ℕ) (hc : (c : ℤ) = D.height (D.neg lowestRoot)) :
    (Uheight (c + 1)).toSubgroup = ⊥ ∧ 0 < c := by
  have hPosEq : positiveRoots = {α | 0 < D.height α} := by
    ext α
    rw [hPositiveRoots, RootPairing.Base.isPos_iff]
    rw [← hDP.2.2.2.2 α]
    simp
  have hc' : (c : ℤ) = -D.height lowestRoot := by
    calc
      (c : ℤ) = D.height (D.neg lowestRoot) := hc
      _ = -D.height lowestRoot := RootGroupData.IsRealization.neg_height hD lowestRoot
  have hlow_nonpos : D.height lowestRoot ≤ 0 := by
    have hnot : ¬ 0 < D.height lowestRoot := by
      intro hpos
      exact hLowest.1 (hPosEq ▸ hpos)
    exact le_of_not_gt hnot
  have hlow_ne : D.height lowestRoot ≠ 0 := by
    rw [hDP.2.2.2.2 lowestRoot]
    exact b.height_ne_zero (e lowestRoot)
  have hc_pos : 0 < c := by
    omega
  have hHeightBound : ∀ α, D.height α ≤ (c : ℤ) := by
    intro α
    by_cases hαpos : α ∈ positiveRoots
    · have hneg_not : D.neg α ∉ positiveRoots := by
        intro hneg
        have hmem : α ∈ positiveRoots ∩ D.neg ⁻¹' positiveRoots := ⟨hαpos, hneg⟩
        rw [hPositive.1] at hmem
        exact hmem.elim
      have hlow := hLowest.2 (D.neg α) hneg_not
      rw [RootGroupData.IsRealization.neg_height hD] at hlow
      omega
    · have hnonpos : D.height α ≤ 0 := by
        have hnot : ¬ 0 < D.height α := by simpa [hPosEq] using hαpos
        exact le_of_not_gt hnot
      omega
  have hempty : {α : D.Root | ((c + 1 : ℕ) : ℤ) ≤ D.height α} = ∅ := by
    ext α
    constructor
    · intro hα
      have hbound := hHeightBound α
      have hlt : D.height α < ((c + 1 : ℕ) : ℤ) := by omega
      exact (not_le_of_gt hlt hα).elim
    · intro hα
      exact False.elim hα
  have hTerminal : (Uheight (c + 1)).toSubgroup = ⊥ := by
    rw [hUheight (c + 1) (by omega), hempty, RootSubgroupGenerated]
    simp
  exact ⟨hTerminal, hc_pos⟩

/-- The root subgroup of the negative lowest root lies in the center of the
unipotent height filtration. -/
public theorem lowestRootSubgroup_le_map_center
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T)
    (lowestRoot : D.Root) (Uheight : ℕ → ClosedSubgroup K)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (hHeightCommutator : ∀ i, 0 < i →
      ⁅(Uheight i).toSubgroup, U.toSubgroup⁆ ≤ (Uheight (i + 1)).toSubgroup)
    (hUheightLe : ∀ i, 0 < i → Uheight i ≤ U)
    (c : ℕ) (hc : (c : ℤ) = D.height (D.neg lowestRoot))
    (hcpos : 0 < c) (hTerminal : (Uheight (c + 1)).toSubgroup = ⊥) :
    (D.rootSubgroup (D.neg lowestRoot)).toSubgroup ≤
      Subgroup.map U.toSubgroup.subtype (Subgroup.center U.toSubgroup) := by
  have hrootLayer : (D.rootSubgroup (D.neg lowestRoot)).toSubgroup ≤
      (Uheight c).toSubgroup := by
    rw [hUheight c hcpos]
    apply rootSubgroup_le_RootSubgroupGenerated
    change (c : ℤ) ≤ D.height (D.neg lowestRoot)
    exact le_of_eq hc
  intro x hx
  have hxLayer := hrootLayer hx
  have hxU : x ∈ U.toSubgroup := hUheightLe c hcpos hxLayer
  refine ⟨⟨x, hxU⟩, ?_, rfl⟩
  change ⟨x, hxU⟩ ∈ Subgroup.center U.toSubgroup
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hcomm :=
    (Subgroup.commutator_le.mp (hHeightCommutator c hcpos)) x hxLayer g.1 g.2
  rw [hTerminal] at hcomm
  have hzero : ⁅x, (g : Variety.Point K)⁆ = 1 := by simpa using hcomm
  exact (commutatorElement_eq_one_iff_mul_comm.mp hzero).symm

private lemma terminalHeight_layer_nontrivial
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) (hC : IsChevalleySystem D C P e b)
    (Uheight : ℕ → ClosedSubgroup K) (lowestRoot : D.Root)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (c : ℕ) (hcpos : 0 < c)
    (hc : (c : ℤ) = D.height (D.neg lowestRoot)) :
    (Uheight c).toSubgroup ≠ ⊥ := by
  have hrootLayer : (D.rootSubgroup (D.neg lowestRoot)).toSubgroup ≤
      (Uheight c).toSubgroup := by
    rw [hUheight c hcpos]
    apply rootSubgroup_le_RootSubgroupGenerated
    change (c : ℤ) ≤ D.height (D.neg lowestRoot)
    exact le_of_eq hc
  intro hbot
  have hrootbot : (D.rootSubgroup (D.neg lowestRoot)).toSubgroup = ⊥ :=
    le_bot_iff.mp (hbot ▸ hrootLayer)
  exact (rootSubgroup_ne_bot_of_chevalleySystem D C P e b hC
    (D.neg lowestRoot)) hrootbot

/-- Internal proof core for the height-filtration results below.  The public
API exposes each source conclusion separately, rather than a conjunction of
unrelated statements. -/
private lemma nilpotencyClass_bound_from_heightFiltration
    {K : Variety k} [AlgebraicGroup K] (T B U : ClosedSubgroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (lowestRoot : D.Root) (Uheight : ℕ → ClosedSubgroup K)
    (_hK : IsSimpleAlgebraicGroup K) (_hT : IsMaximalTorus T)
    (hD : D.IsRealization) (hDP : IsRootSystemRealization D P e b)
    (hC : IsChevalleySystem D C P e b)
    (_hB : IsBorelSubgroup B) (_hTB : T ≤ B)
    (_hUrad : IsUnipotentRadicalOf B U)
    (hPositive : IsPositiveSystem D positiveRoots)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hLowest : IsLowestRoot D positiveRoots lowestRoot)
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (c : ℕ) (hc : (c : ℤ) = D.height (D.neg lowestRoot)) :
    Group.nilpotencyClass U.toSubgroup ≤ c := by
  rcases initialHeight_filtration T U D P e b positiveRoots Uheight
      hDP hPositiveRoots hU hUheight with ⟨hFirst, _, _⟩
  have hHeightCommutator :=
    heightFiltration_commutator T U D C P e b positiveRoots Uheight
      hDP hC hU hPositiveRoots hUheight
  obtain ⟨hTerminal, hcpos⟩ := terminalHeight_exists T D P e b
    positiveRoots lowestRoot Uheight hD hDP hPositive hPositiveRoots hLowest
    hUheight c hc
  have hClassLe := nilpotencyClass_le_of_subgroupSeries U.toSubgroup
    (fun i => (Uheight i).toSubgroup) c hFirst (by
      intro i
      exact hHeightCommutator (i + 1) (by omega)) hTerminal
  exact hClassLe

/-- The nilpotency-class bound for the unipotent radical filtration. -/
public theorem unipotentRadical_nilpotencyClass_le
    {K : Variety k} [AlgebraicGroup K] (T B U : ClosedSubgroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (lowestRoot : D.Root) (Uheight : ℕ → ClosedSubgroup K)
    (hK : IsSimpleAlgebraicGroup K) (hT : IsMaximalTorus T)
    (hD : D.IsRealization) (hDP : IsRootSystemRealization D P e b)
    (hC : IsChevalleySystem D C P e b)
    (hB : IsBorelSubgroup B) (hTB : T ≤ B)
    (hUrad : IsUnipotentRadicalOf B U)
    (hPositive : IsPositiveSystem D positiveRoots)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hLowest : IsLowestRoot D positiveRoots lowestRoot)
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (c : ℕ) (hc : (c : ℤ) = D.height (D.neg lowestRoot)) :
    Group.nilpotencyClass U.toSubgroup ≤ c := by
  exact (nilpotencyClass_bound_from_heightFiltration T B U D C P e b
    positiveRoots lowestRoot Uheight hK hT hD hDP hC hB hTB hUrad
    hPositive hPositiveRoots hLowest hU hUheight c hc)

/-! Insert a higher-degree correction word at an explicit low-word position.

The prefix/suffix split identifies a target list position.  The high
accumulator is spliced across the prefix and returned as an explicit word,
leaving the suffix untouched.  This is the positional primitive needed by a
degree-layer collection recursion.
-/

variable {k : Type u} [Field k]

private lemma chevalleyCommutatorTermAboveDegreeWord_insert_at_lowWord_exists
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (hC : IsChevalleySystem D C P e b)
    (d : ℕ)
    (highWord : List (ChevalleyCommutatorTerm D.Root × k))
    (leftWord rightWord : List (ChevalleyCommutatorTerm D.Root × k))
    (hhigh : ∀ q ∈ highWord,
      IsValidChevalleyCommutatorTerm D P e α β q.1 ∧ d < q.1.degree)
    (hleft : ∀ q ∈ leftWord,
      IsValidChevalleyCommutatorTerm D P e α β q.1 ∧ q.1.degree ≤ d)
    (_hright : ∀ q ∈ rightWord,
      IsValidChevalleyCommutatorTerm D P e α β q.1 ∧ q.1.degree ≤ d) :
    ∃ highWord' : List (ChevalleyCommutatorTerm D.Root × k),
      (∀ q ∈ highWord',
        IsValidChevalleyCommutatorTerm D P e α β q.1 ∧ d < q.1.degree) ∧
      ChevalleyCommutatorTermWordProduct C highWord *
          ChevalleyCommutatorTermWordProduct C (leftWord ++ rightWord) =
        ChevalleyCommutatorTermWordProduct C leftWord *
          ChevalleyCommutatorTermWordProduct C highWord' *
            ChevalleyCommutatorTermWordProduct C rightWord := by
  obtain ⟨highWord', hhighWord', hmove⟩ :=
    chevalleyCommutatorTermAboveDegreeWord_splice_lowWord_exists
      D C P e b hLI hC d highWord leftWord hhigh hleft
  refine ⟨highWord', hhighWord', ?_⟩
  simp only [ChevalleyCommutatorTermWordProduct, List.map_append,
    List.prod_append]
  have hmove' :
      (highWord.map (fun z => C.x z.1.root z.2)).prod *
          (leftWord.map (fun z => C.x z.1.root z.2)).prod =
        (leftWord.map (fun z => C.x z.1.root z.2)).prod *
          (highWord'.map (fun z => C.x z.1.root z.2)).prod := by
    simpa [ChevalleyCommutatorTermWordProduct] using hmove
  rw [← mul_assoc, hmove', mul_assoc]

/-! A conditional endpoint for Theorem 1.12.7(b).

The unresolved order-independence step is exposed as an explicit parameter
collection premise.  No setup structure stores the desired membership
conclusion: the premise only identifies the degree-ordered Chevalley word with
the requested distributed target order. -/

variable {k : Type u} [Field k]

private lemma targetWord_mem_orderedRootSubgroupProduct
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) {α β : D.Root}
    (hC : IsChevalleySystem D C P e b)
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (order : List (ChevalleyCommutatorTerm D.Root))
    (horder : ∀ q, q ∈ order ↔ IsValidChevalleyCommutatorTerm D P e α β q)
    (params : ChevalleyCommutatorTerm D.Root → k) :
    (order.map fun q => C.x q.root (params q)).prod ∈
      OrderedRootSubgroupProduct D (order.map (·.root)) := by
  classical
  let factor : D.Root → Variety.Point K := fun γ =>
    if h : ∃ q, q ∈ order ∧ q.root = γ then
      C.x γ (params (Classical.choose h))
    else 1
  have hfactor (q : ChevalleyCommutatorTerm D.Root) (hq : q ∈ order) :
      factor q.root = C.x q.root (params q) := by
    dsimp [factor]
    split
    next h =>
      let r := Classical.choose h
      have hr := Classical.choose_spec h
      have hre : r = q := by
        apply validTerm_eq_of_root_eq D P e hLI (horder r |>.mp hr.1)
          (horder q |>.mp hq)
        exact hr.2
      change C.x q.root (params r) = C.x q.root (params q)
      rw [hre]
    next h => exact False.elim (h ⟨q, hq, rfl⟩)
  refine ⟨factor, ?_, ?_⟩
  · intro γ hγ
    rcases List.mem_map.mp hγ with ⟨q, hq, rfl⟩
    rw [hfactor q hq]
    have hxmem : C.x q.root (params q) ∈ Set.range (C.x q.root) :=
      Set.mem_range_self _
    rw [(hC.1 q.root).2] at hxmem
    exact hxmem
  · simp only [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro q hq
    exact (hfactor q hq).symm

public theorem chevalleySystem_commutator_mem_orderedRootSubgroupProduct_of_distributed_collection
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base)
    (hC : IsChevalleySystem D C P e b) (α β : D.Root)
    (hLI : AreLinearlyIndependentRoots D P e α β)
    (canonicalOrder : List (ChevalleyCommutatorTerm D.Root))
    (canonicalCoeff : ChevalleyCommutatorTerm D.Root → k)
    (hformula : ∀ t u,
      (C.x α t)⁻¹ * (C.x β u)⁻¹ * C.x α t * C.x β u =
        (canonicalOrder.map fun q =>
          C.x q.root (canonicalCoeff q * t ^ q.i * u ^ q.j)).prod)
    (order : List (ChevalleyCommutatorTerm D.Root))
    (horder : ∀ q, q ∈ order ↔
      IsValidChevalleyCommutatorTerm D P e α β q)
    (hDistributed : ∀ t u, ∃ params : ChevalleyCommutatorTerm D.Root → k,
      (canonicalOrder.map fun q =>
        C.x q.root (canonicalCoeff q * t ^ q.i * u ^ q.j)).prod =
      (order.map fun q => C.x q.root (params q)).prod) :
    ∀ x, x ∈ D.rootSubgroup α → ∀ y, y ∈ D.rootSubgroup β →
      x⁻¹ * y⁻¹ * x * y ∈
        OrderedRootSubgroupProduct D (order.map (·.root)) := by
  intro x hx y hy
  have hxRange : x ∈ Set.range (C.x α) := by
    simpa [hC.1 α |>.2] using hx
  have hyRange : y ∈ Set.range (C.x β) := by
    simpa [hC.1 β |>.2] using hy
  rcases hxRange with ⟨t, rfl⟩
  rcases hyRange with ⟨u, rfl⟩
  rw [hformula]
  obtain ⟨params, hparams⟩ := hDistributed t u
  rw [hparams]
  exact targetWord_mem_orderedRootSubgroupProduct D C P e b hC hLI order horder params

open scoped commutatorElement

variable {k : Type u} [Field k]

/-! This is the lower-series assembly step isolated from the genuinely
  Chevalley-theoretic reverse inclusion. -/

public theorem lowerCentralSeries_eq_height_filtration
    {K : Variety k} [AlgebraicGroup K] (U : ClosedSubgroup K)
    (Uheight : ℕ → ClosedSubgroup K)
    (hFirst : (Uheight 1).toSubgroup = U.toSubgroup)
    (hHeightCommutator : ∀ i, 0 < i →
      ⁅(Uheight i).toSubgroup, U.toSubgroup⁆ ≤ (Uheight (i + 1)).toSubgroup)
    (hReverse : ∀ i, 0 < i →
      (Uheight (i + 1)).toSubgroup ≤ ⁅(Uheight i).toSubgroup, U.toSubgroup⁆) :
    ∀ i, (Uheight (i + 1)).toSubgroup = U.toSubgroup.lowerCentralSeries i := by
  have hCommEq : ∀ i : ℕ,
      ⁅(Uheight (i + 1)).toSubgroup, U.toSubgroup⁆ =
        (Uheight (i + 2)).toSubgroup := by
    intro i
    apply le_antisymm
    · exact hHeightCommutator (i + 1) (by omega)
    · exact hReverse (i + 1) (by omega)
  exact subgroupSeries_eq_lowerCentralSeries_of_commutator_eq
    U.toSubgroup (fun i => (Uheight i).toSubgroup) hFirst hCommEq

open scoped commutatorElement

variable {k : Type u} [Field k]

/-- The upper-central-series part of Theorem 1.12.9 after isolating the
quotient-layer commutator detection step.  The reversed filtration is
truncated at its top endpoint, so no value of `Uheight 0` is required. -/
public theorem upperCentralSeries_eq_reversed_height_filtration
    {K : Variety k} [AlgebraicGroup K]
    (U : ClosedSubgroup K) (Uheight : ℕ → ClosedSubgroup K) (c : ℕ)
    (hFirst : (Uheight 1).toSubgroup = U.toSubgroup)
    (hHeightLe : ∀ i, 0 < i → Uheight i ≤ U)
    (hHeightCommutator : ∀ i, 0 < i →
      ⁅(Uheight i).toSubgroup, U.toSubgroup⁆ ≤
        (Uheight (i + 1)).toSubgroup)
    (hTerminal : (Uheight (c + 1)).toSubgroup = ⊥)
    (hDetect : ∀ n, n < c →
      ∀ x : U.toSubgroup, x ∉
        (Uheight (c - n)).toSubgroup.subgroupOf U.toSubgroup →
        ∃ y : U.toSubgroup,
          ⁅(x : Variety.Point K), (y : Variety.Point K)⁆ ∉
            (Uheight (c + 1 - n)).toSubgroup) :
    ∀ i, i ≤ c →
      Subgroup.map U.toSubgroup.subtype (Subgroup.upperCentralSeries U.toSubgroup i) =
        (Uheight (c + 1 - i)).toSubgroup := by
  let A : ℕ → Subgroup (Variety.Point K) := fun n =>
    if h : n ≤ c then (Uheight (c + 1 - n)).toSubgroup else U.toSubgroup
  have hAZero : A 0 = ⊥ := by
    simpa [A, show 0 ≤ c by omega] using hTerminal
  have hATop : A (c + 1) = U.toSubgroup := by
    simp [A, show ¬ c + 1 ≤ c by omega]
  have hALe : ∀ n, A n ≤ U.toSubgroup := by
    intro n
    dsimp [A]
    split_ifs with hn
    · exact hHeightLe (c + 1 - n) (by omega)
    · exact le_rfl
  have hComm : ∀ n, ⁅A (n + 1), U.toSubgroup⁆ ≤ A n := by
    intro n
    by_cases hn : n < c
    · have hidx : 0 < c - n := by omega
      have hnext : n + 1 ≤ c := by omega
      have hA_next : A (n + 1) = (Uheight (c - n)).toSubgroup := by
        simp [A, hnext]
      have hA_n : A n = (Uheight (c + 1 - n)).toSubgroup := by
        simp [A, show n ≤ c by omega]
      rw [hA_next, hA_n]
      have hidxEq : c - n + 1 = c + 1 - n := by
        symm
        exact Nat.sub_add_comm (show n ≤ c by omega)
      simpa [hidxEq] using hHeightCommutator (c - n) hidx
    · have hnc : c ≤ n := by omega
      by_cases hEq : n = c
      · have hA_next : A (n + 1) = U.toSubgroup := by
          simp [A, show ¬ n + 1 ≤ c by omega]
        have hA_n : A n = U.toSubgroup := by
          rw [hEq]
          simpa [A] using hFirst
        rw [hA_next, hA_n]
        rw [Subgroup.commutator_le]
        intro x hx y hy
        simpa [commutatorElement_def, mul_assoc] using
          U.toSubgroup.mul_mem
            (U.toSubgroup.mul_mem (U.toSubgroup.mul_mem hx hy)
              (U.toSubgroup.inv_mem hx)) (U.toSubgroup.inv_mem hy)
      · have hA_next : A (n + 1) = U.toSubgroup := by
          simp [A, show ¬ n + 1 ≤ c by omega]
        have hA_n : A n = U.toSubgroup := by
          simp [A, show ¬ n ≤ c by omega]
        rw [hA_next, hA_n]
        rw [Subgroup.commutator_le]
        intro x hx y hy
        simpa [commutatorElement_def, mul_assoc] using
          U.toSubgroup.mul_mem
            (U.toSubgroup.mul_mem (U.toSubgroup.mul_mem hx hy)
              (U.toSubgroup.inv_mem hx)) (U.toSubgroup.inv_mem hy)
  have hDetectA : ∀ n, n < c →
      ∀ x : U.toSubgroup, x ∉ (A (n + 1)).subgroupOf U.toSubgroup →
        ∃ y : U.toSubgroup, ⁅(x : Variety.Point K), (y : Variety.Point K)⁆ ∉ A n := by
    intro n hn x hx
    have hA_next : A (n + 1) = (Uheight (c - n)).toSubgroup := by
      simp [A, show n + 1 ≤ c by omega]
    have hA_n : A n = (Uheight (c + 1 - n)).toSubgroup := by
      simp [A, show n ≤ c by omega]
    rw [hA_next] at hx
    rw [hA_n]
    exact hDetect n hn x hx
  have hUpper := upperCentralSeries_map_eq_of_commutator_detection
    U.toSubgroup A c hAZero hATop hALe hComm hDetectA
  intro i hi
  have hAi : A i = (Uheight (c + 1 - i)).toSubgroup := by
    simp [A, hi]
  rw [hUpper i (by omega), hAi]

open scoped commutatorElement

variable {k : Type u} [Field k]

/-! The Chevalley-theoretic reverse layer inclusion used by the nonsingular
    part of Theorem 1.12.9.  The coefficient and irreducibility inputs are
    kept explicit; they are independent root-system facts, not conclusion-
    bearing fields hidden in a setup structure. -/

public theorem height_filtration_reverse_inclusion_of_nonzero_coefficients
    {K : Variety k} [AlgebraicGroup K] {T U : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [IsAddTorsionFree M]
    [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (Uheight : ℕ → ClosedSubgroup K)
    (hDP : IsRootSystemRealization D P e b)
    (hC : IsChevalleySystem D C P e b)
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (hCoeff11 : ∀ {α β : D.Root} {q : ChevalleyCommutatorTerm D.Root},
      AreLinearlyIndependentRoots D P e α β →
      IsValidChevalleyCommutatorTerm D P e α β q →
      q.i = 1 → q.j = 1 →
      ∀ c : k, HasExpectedChevalleyCoefficient D P e α β q c → c ≠ 0)
    (c : ℕ)
    (hTerminal : (Uheight (c + 1)).toSubgroup = ⊥) :
    ∀ i, 0 < i → i ≤ c →
      (Uheight (i + 1)).toSubgroup ≤
        ⁅(Uheight i).toSubgroup, U.toSubgroup⁆ := by
  classical
  choose coeff hCoeffSupport hCoeffSign hCoeffRoot using
    fun β => b.exists_root_eq_sum_int β
  have hCoeff : HasSimpleRootExpansion P b coeff := by
    intro β
    constructor
    · simpa [Int.cast_smul_eq_zsmul] using hCoeffRoot β
    · intro γ hγ
      by_contra hne
      exact hγ (hCoeffSupport β hne)
  have hRelativeHeight (α : D.Root) :
      RelativeRootHeight coeff b.support (e '' (∅ : Set D.Root)) (e α) =
        D.height α := by
    rw [hDP.2.2.2.2 α]
    rw [b.height_eq_sum (by
      simpa [Int.cast_smul_eq_zsmul] using (hCoeff (e α)).1)]
    simp [RelativeRootHeight]
  have hSeries (n : ℕ) :
      RelativeRootSeries D e b.support coeff (∅ : Set D.Root) n =
        RootSubgroupGenerated D {α | (n : ℤ) ≤ D.height α} := by
    unfold RelativeRootSeries
    congr 1
    ext α
    simp only [Set.mem_ofPred_eq]
    rw [hRelativeHeight α]
  have hLayer (n : ℕ) (hn : 0 < n) :
      (Uheight n).toSubgroup =
        RelativeRootSeries D e b.support coeff (∅ : Set D.Root) n := by
    rw [hUheight n hn, hSeries n]
  have hHeightPositive : positiveRoots = {α | (1 : ℤ) ≤ D.height α} := by
    ext α
    rw [hPositiveRoots]
    change b.IsPos (e α) ↔ (1 : ℤ) ≤ D.height α
    rw [RootPairing.Base.isPos_iff, ← hDP.2.2.2.2 α]
    omega
  have hFirst :
      (Uheight 1).toSubgroup = U.toSubgroup := by
    calc
      (Uheight 1).toSubgroup =
          RootSubgroupGenerated D {α | (1 : ℤ) ≤ D.height α} :=
        hUheight 1 (by omega)
      _ = RootSubgroupGenerated D positiveRoots := by rw [hHeightPositive]
      _ = U.toSubgroup := hU.symm
  have hExact := relativeRootSeries_eq_commutator_of_one_one_nonzero
    D C P e b coeff hCoeff hC hCoeff11 c (by
      simpa [hLayer (c + 1) (by omega)] using hTerminal)
  intro i hi hile
  have hi1 : 0 < i + 1 := by omega
  have hEq := hExact i hi hile
  have hEq' :
      ⁅(Uheight i).toSubgroup, (Uheight 1).toSubgroup⁆ =
        (Uheight (i + 1)).toSubgroup := by
    rw [hLayer i hi, hLayer 1 (by omega), hLayer (i + 1) hi1]
    exact hEq
  rw [hFirst] at hEq'
  exact hEq'.ge

open scoped commutatorElement

variable {k : Type u} [Field k]

/-! The nonsingular reverse layer, isolated from the owner theorem so that the
Chevalley coefficient and irreducibility bridges remain explicit premises. -/

public theorem height_filtration_commutator_eq_of_nonzero_unit_coefficients
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [IsAddTorsionFree M]
    [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) (b : P.Base)
    (Uheight : ℕ → ClosedSubgroup K)
    (hDP : IsRootSystemRealization D P e b)
    (hC : IsChevalleySystem D C P e b)
    (hFirst : (Uheight 1).toSubgroup = U.toSubgroup)
    (hHeightCommutator : ∀ i, 0 < i →
      ⁅(Uheight i).toSubgroup, U.toSubgroup⁆ ≤ (Uheight (i + 1)).toSubgroup)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (hCoeff11 : ∀ {α β : D.Root} {q : ChevalleyCommutatorTerm D.Root},
      AreLinearlyIndependentRoots D P e α β →
      IsValidChevalleyCommutatorTerm D P e α β q →
      q.i = 1 → q.j = 1 →
      ∀ c : k, HasExpectedChevalleyCoefficient D P e α β q c → c ≠ 0)
    (c : ℕ) (hTerminal : (Uheight (c + 1)).toSubgroup = ⊥) :
    ∀ i, 0 < i → i ≤ c →
      ⁅(Uheight i).toSubgroup, U.toSubgroup⁆ = (Uheight (i + 1)).toSubgroup := by
  choose coeff hCoeffSupport hCoeffSign hCoeffRoot using
    fun β => b.exists_root_eq_sum_int β
  have hCoeff : HasSimpleRootExpansion P b coeff := by
    intro β
    constructor
    · simpa [Int.cast_smul_eq_zsmul] using hCoeffRoot β
    · intro γ hγ
      by_contra hne
      exact hγ (hCoeffSupport β hne)
  have hRelativeHeight (α : D.Root) :
      RelativeRootHeight coeff b.support (e '' (∅ : Set D.Root)) (e α) =
        D.height α := by
    rw [hDP.2.2.2.2 α]
    rw [b.height_eq_sum (by
      simpa [Int.cast_smul_eq_zsmul] using (hCoeff (e α)).1)]
    simp [RelativeRootHeight]
  have hSeries (n : ℕ) :
      RelativeRootSeries D e b.support coeff (∅ : Set D.Root) n =
        RootSubgroupGenerated D {α | (n : ℤ) ≤ D.height α} := by
    unfold RelativeRootSeries
    congr 1
    ext α
    simp only [Set.mem_ofPred_eq]
    rw [hRelativeHeight α]
  have hUheightSeries (n : ℕ) (hn : 0 < n) :
      (Uheight n).toSubgroup =
        RelativeRootSeries D e b.support coeff (∅ : Set D.Root) n := by
    rw [hUheight n hn, hSeries n]
  have hTerminalSeries :
      RelativeRootSeries D e b.support coeff (∅ : Set D.Root) (c + 1) = ⊥ := by
    rw [← hUheightSeries (c + 1) (by omega)]
    exact hTerminal
  have hRelativeEq :=
    relativeRootSeries_eq_commutator_of_one_one_nonzero
      D C P e b coeff hCoeff hC hCoeff11 c hTerminalSeries
  intro i hi hile
  have hReverse : (Uheight (i + 1)).toSubgroup ≤
      ⁅(Uheight i).toSubgroup, U.toSubgroup⁆ := by
    have hEq := hRelativeEq i hi hile
    have hEq' : (Uheight (i + 1)).toSubgroup =
        ⁅(Uheight i).toSubgroup, (Uheight 1).toSubgroup⁆ := by
      rw [hUheightSeries (i + 1) (by omega), hUheightSeries i hi,
        hUheightSeries 1 (by omega)]
      exact hEq.symm
    rw [hFirst] at hEq'
    exact hEq'.le
  exact le_antisymm (hHeightCommutator i hi) hReverse

private lemma height_filtration_eq_lowerCentralSeries_of_nonzero_unit_coefficients
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [IsAddTorsionFree M]
    [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (lowestRoot : D.Root) (Uheight : ℕ → ClosedSubgroup K)
    (hD : D.IsRealization) (hDP : IsRootSystemRealization D P e b)
    (hC : IsChevalleySystem D C P e b)
    (hPositive : IsPositiveSystem D positiveRoots)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hLowest : IsLowestRoot D positiveRoots lowestRoot)
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (hCoeff11 : ∀ {α β : D.Root}
      {q : ChevalleyCommutatorTerm D.Root},
      AreLinearlyIndependentRoots D P e α β →
      IsValidChevalleyCommutatorTerm D P e α β q →
      q.i = 1 → q.j = 1 →
      ∀ z : k, HasExpectedChevalleyCoefficient D P e α β q z → z ≠ 0)
    (c : ℕ) (hc : (c : ℤ) = D.height (D.neg lowestRoot)) :
    ∀ i, (Uheight (i + 1)).toSubgroup =
      U.toSubgroup.lowerCentralSeries i := by
  letI := Fintype.ofFinite ι
  rcases initialHeight_filtration T U D P e b positiveRoots Uheight
      hDP hPositiveRoots hU hUheight with ⟨hFirst, _, hDescending⟩
  have hHeightCommutator :=
    heightFiltration_commutator T U D C P e b positiveRoots Uheight
      hDP hC hU hPositiveRoots hUheight
  obtain ⟨hTerminal, _⟩ := terminalHeight_exists T D P e b
    positiveRoots lowestRoot Uheight hD hDP hPositive hPositiveRoots hLowest
    hUheight c hc
  have hCommEq :=
    height_filtration_commutator_eq_of_nonzero_unit_coefficients
      T U D C P e b Uheight hDP hC hFirst hHeightCommutator hUheight
      hCoeff11 c hTerminal
  apply lowerCentralSeries_eq_height_filtration U Uheight hFirst
    hHeightCommutator
  intro i hi
  by_cases hic : i ≤ c
  · exact (hCommEq i hi hic).ge
  · have hle : Uheight (i + 1) ≤ Uheight (c + 1) := by
      refine Nat.decreasingInduction'
        (m := c + 1) (n := i + 1)
        (P := fun n => Uheight (i + 1) ≤ Uheight n) ?_ (by omega)
          (fun _ hx => hx)
      intro n _ hcn hin
      exact hin.trans (hDescending n (by omega))
    have hbot : (Uheight (i + 1)).toSubgroup = ⊥ :=
      le_bot_iff.mp (hTerminal ▸ hle)
    rw [hbot]
    exact bot_le

/-- In characteristic different from two and three, the positive-root height
filtration is the lower central series.  This is the uniform nonsingular case
of Theorem 1.12.9(b). -/
public theorem height_filtration_eq_lowerCentralSeries_of_ringChar_ne_two_three
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [IsAddTorsionFree M]
    [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (lowestRoot : D.Root) (Uheight : ℕ → ClosedSubgroup K)
    (hD : D.IsRealization) (hDP : IsRootSystemRealization D P e b)
    (hC : IsChevalleySystem D C P e b)
    (hPositive : IsPositiveSystem D positiveRoots)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hLowest : IsLowestRoot D positiveRoots lowestRoot)
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (hchar2 : ringChar k ≠ 2) (hchar3 : ringChar k ≠ 3)
    (c : ℕ) (hc : (c : ℤ) = D.height (D.neg lowestRoot)) :
    ∀ i, (Uheight (i + 1)).toSubgroup =
      U.toSubgroup.lowerCentralSeries i := by
  apply height_filtration_eq_lowerCentralSeries_of_nonzero_unit_coefficients
    T U D C P e b positiveRoots lowestRoot Uheight hD hDP hC hPositive
    hPositiveRoots hLowest hU hUheight ?_ c hc
  intro α β q _ _ _ _ z hz
  exact hz.ne_zero_of_ringChar_ne_two_three D P e hchar2 hchar3

/-- For a concrete nonsingular Dynkin type, the positive-root height
filtration is the lower central series.  This is Theorem 1.12.9(b). -/
public theorem height_filtration_eq_lowerCentralSeries_of_nonsingular
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [IsAddTorsionFree M]
    [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (lowestRoot : D.Root) (Uheight : ℕ → ClosedSubgroup K)
    (hD : D.IsRealization) (hDP : IsRootSystemRealization D P e b)
    (hC : IsChevalleySystem D C P e b)
    (hPositive : IsPositiveSystem D positiveRoots)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hLowest : IsLowestRoot D positiveRoots lowestRoot)
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (classification : RootClassification)
    (hType : HasDynkinType P classification)
    (hNonsingular : ¬ IsUSingular classification (ringChar k))
    (c : ℕ) (hc : (c : ℤ) = D.height (D.neg lowestRoot)) :
    ∀ i, (Uheight (i + 1)).toSubgroup =
      U.toSubgroup.lowerCentralSeries i := by
  apply height_filtration_eq_lowerCentralSeries_of_nonzero_unit_coefficients
    T U D C P e b positiveRoots lowestRoot Uheight hD hDP hC hPositive
    hPositiveRoots hLowest hU hUheight ?_ c hc
  intro α β q _ _ _ _ z hz
  exact hz.ne_zero_of_nonsingular_of_hasDynkinType
    D P e classification hType hNonsingular

private lemma height_filtration_nilpotencyClass_eq_of_lowerCentralSeries
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [IsAddTorsionFree M]
    [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (lowestRoot : D.Root) (Uheight : ℕ → ClosedSubgroup K)
    (hD : D.IsRealization) (hDP : IsRootSystemRealization D P e b)
    (hC : IsChevalleySystem D C P e b)
    (hPositive : IsPositiveSystem D positiveRoots)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hLowest : IsLowestRoot D positiveRoots lowestRoot)
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (c : ℕ) (hc : (c : ℤ) = D.height (D.neg lowestRoot)) :
    (∀ i, (Uheight (i + 1)).toSubgroup =
      U.toSubgroup.lowerCentralSeries i) →
    Group.nilpotencyClass U.toSubgroup = c := by
  letI := Fintype.ofFinite ι
  intro hLower
  rcases initialHeight_filtration T U D P e b positiveRoots Uheight
      hDP hPositiveRoots hU hUheight with ⟨_, hHeightLe, _⟩
  obtain ⟨hTerminal, hcpos⟩ := terminalHeight_exists T D P e b
    positiveRoots lowestRoot Uheight hD hDP hPositive hPositiveRoots hLowest
    hUheight c hc
  have hPrevious : (Uheight c).toSubgroup ≠ ⊥ :=
    terminalHeight_layer_nontrivial T D C P e b hC Uheight lowestRoot hUheight
      c hcpos hc
  let S : ℕ → Subgroup (Variety.Point K) := fun n => (Uheight n).toSubgroup
  let H : ℕ → Subgroup U.toSubgroup := fun n => (S n).comap U.toSubgroup.subtype
  have hRange (n : ℕ) (hn : 0 < n) : S n ≤ U.toSubgroup.subtype.range := by
    rw [Subgroup.subtype_range]
    change (Uheight n).toSubgroup ≤ U.toSubgroup
    exact hHeightLe n hn
  apply nilpotencyClass_eq_of_lowerCentralSeries H c
  · intro i
    rw [← Subgroup.map_subtype_inj]
    rw [Subgroup.top_subtype_lowerCentralSeries]
    change ((S (i + 1)).comap U.toSubgroup.subtype).map
        U.toSubgroup.subtype = U.toSubgroup.lowerCentralSeries i
    rw [Subgroup.map_comap_eq_self (hRange (i + 1) (by omega))]
    exact hLower i
  · rw [← Subgroup.map_subtype_inj, Subgroup.map_bot]
    change ((S (c + 1)).comap U.toSubgroup.subtype).map
        U.toSubgroup.subtype = ⊥
    rw [Subgroup.map_comap_eq_self (hRange (c + 1) (by omega))]
    exact hTerminal
  · intro _ hH
    apply hPrevious
    rw [← Subgroup.map_subtype_inj, Subgroup.map_bot] at hH
    change ((S c).comap U.toSubgroup.subtype).map
        U.toSubgroup.subtype = ⊥ at hH
    rwa [Subgroup.map_comap_eq_self (hRange c hcpos)] at hH

/-- In characteristic different from two and three, the height of the
negative lowest root is the exact nilpotency class.  This is the uniform
nonsingular nilpotency-class conclusion of Theorem 1.12.9(c). -/
public theorem height_filtration_nilpotencyClass_eq_of_ringChar_ne_two_three
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [IsAddTorsionFree M]
    [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (lowestRoot : D.Root) (Uheight : ℕ → ClosedSubgroup K)
    (hD : D.IsRealization) (hDP : IsRootSystemRealization D P e b)
    (hC : IsChevalleySystem D C P e b)
    (hPositive : IsPositiveSystem D positiveRoots)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hLowest : IsLowestRoot D positiveRoots lowestRoot)
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (hchar2 : ringChar k ≠ 2) (hchar3 : ringChar k ≠ 3)
    (c : ℕ) (hc : (c : ℤ) = D.height (D.neg lowestRoot)) :
    Group.nilpotencyClass U.toSubgroup = c := by
  apply height_filtration_nilpotencyClass_eq_of_lowerCentralSeries
    T U D C P e b positiveRoots lowestRoot Uheight hD hDP hC hPositive
    hPositiveRoots hLowest hU hUheight c hc
  exact height_filtration_eq_lowerCentralSeries_of_ringChar_ne_two_three
    T U D C P e b positiveRoots lowestRoot Uheight hD hDP hC hPositive
    hPositiveRoots hLowest hU hUheight hchar2 hchar3 c hc

/-- For a concrete nonsingular Dynkin type, the negative lowest-root height
is the exact nilpotency class.  This is Theorem 1.12.9(c). -/
public theorem height_filtration_nilpotencyClass_eq_of_nonsingular
    {K : Variety k} [AlgebraicGroup K] (T U : ClosedSubgroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [IsAddTorsionFree M]
    [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (lowestRoot : D.Root) (Uheight : ℕ → ClosedSubgroup K)
    (hD : D.IsRealization) (hDP : IsRootSystemRealization D P e b)
    (hC : IsChevalleySystem D C P e b)
    (hPositive : IsPositiveSystem D positiveRoots)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hLowest : IsLowestRoot D positiveRoots lowestRoot)
    (hU : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (classification : RootClassification)
    (hType : HasDynkinType P classification)
    (hNonsingular : ¬ IsUSingular classification (ringChar k))
    (c : ℕ) (hc : (c : ℤ) = D.height (D.neg lowestRoot)) :
    Group.nilpotencyClass U.toSubgroup = c := by
  apply height_filtration_nilpotencyClass_eq_of_lowerCentralSeries
    T U D C P e b positiveRoots lowestRoot Uheight hD hDP hC hPositive
    hPositiveRoots hLowest hU hUheight c hc
  exact height_filtration_eq_lowerCentralSeries_of_nonsingular
    T U D C P e b positiveRoots lowestRoot Uheight hD hDP hC hPositive
    hPositiveRoots hLowest hU hUheight classification hType hNonsingular c hc

open scoped commutatorElement

variable {k : Type u} [Field k]

/-- Exact center identification from the explicit quotient-layer detection and
terminal-root uniqueness inputs.  The source-specific implications from
nonsingularity to these hypotheses remain independent of this theorem. -/
public theorem center_eq_terminal_rootLayer_of_commutator_detection
    {K : Variety k} [AlgebraicGroup K] {T U : ClosedSubgroup K}
    (D : RootGroupData K T) (lowestRoot : D.Root)
    (Uheight : ℕ → ClosedSubgroup K) (c : ℕ)
    (hFirst : (Uheight 1).toSubgroup = U.toSubgroup)
    (hHeightLe : ∀ i, 0 < i → Uheight i ≤ U)
    (hHeightCommutator : ∀ i, 0 < i →
      ⁅(Uheight i).toSubgroup, U.toSubgroup⁆ ≤
        (Uheight (i + 1)).toSubgroup)
    (hTerminal : (Uheight (c + 1)).toSubgroup = ⊥)
    (hDetect : ∀ n, n < c →
      ∀ x : U.toSubgroup, x ∉
        (Uheight (c - n)).toSubgroup.subgroupOf U.toSubgroup →
        ∃ y : U.toSubgroup,
          ⁅(x : Variety.Point K), (y : Variety.Point K)⁆ ∉
            (Uheight (c + 1 - n)).toSubgroup)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (hcpos : 0 < c) (hc : (c : ℤ) = D.height (D.neg lowestRoot))
    (hUnique : ∀ α : D.Root, (c : ℤ) ≤ D.height α →
      α = D.neg lowestRoot) :
    Subgroup.map U.toSubgroup.subtype (Subgroup.center U.toSubgroup) =
      (D.rootSubgroup (D.neg lowestRoot)).toSubgroup := by
  have hUpperAll := upperCentralSeries_eq_reversed_height_filtration
    U Uheight c hFirst hHeightLe hHeightCommutator hTerminal hDetect
  have hUpper : Subgroup.map U.toSubgroup.subtype
      (Subgroup.upperCentralSeries U.toSubgroup 1) =
        (Uheight c).toSubgroup := by
    simpa using hUpperAll 1 (by omega)
  exact map_center_eq_terminal_rootSubgroup
    D lowestRoot Uheight c hUheight hcpos hc hUnique hUpper

/-! The generic root-system extrema theorem becomes a usable height-layer
    uniqueness statement after transporting it through a root-data
    realization.  The irreducibility instance is intentionally explicit:
    the maintained simple-group setup does not currently construct it. -/

public lemma terminal_height_root_unique_of_lowest
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (lowestRoot : D.Root)
    (hD : D.IsRealization)
    (hDP : IsRootSystemRealization D P e b)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hLowest : IsLowestRoot D positiveRoots lowestRoot)
    (c : ℕ) (hc : (c : ℤ) = D.height (D.neg lowestRoot)) :
    ∀ α : D.Root, (c : ℤ) ≤ D.height α → α = D.neg lowestRoot := by
  letI := Fintype.ofFinite ι
  obtain ⟨highest, hhighest, hhighest_unique⟩ :=
    RootPairing.Base.existsUnique_heightMaximum (P := P) b
  have hmax : ∀ α : D.Root,
      D.height α ≤ D.height (D.neg lowestRoot) := by
    intro α
    by_cases hαpos : α ∈ positiveRoots
    · have hneg_not : D.neg α ∉ positiveRoots := by
        intro hneg
        have hnegpos : b.IsPos (e (D.neg α)) := (hPositiveRoots _).mp hneg
        have hαpos' : b.IsPos (e α) := (hPositiveRoots _).mp hαpos
        rw [hDP.2.2.1 α] at hnegpos
        exact ((RootPairing.Base.IsPos.neg_iff_not b (e α)).mp
          (by simpa [P.reflectionPerm_self] using hnegpos)) hαpos'
      have hlow := hLowest.2 (D.neg α) hneg_not
      rw [RootGroupData.IsRealization.neg_height hD α] at hlow
      rw [RootGroupData.IsRealization.neg_height hD lowestRoot]
      omega
    · have hαnonpos : D.height α ≤ 0 := by
        have hnot : ¬ 0 < D.height α := by
          intro hpos
          apply hαpos
          rw [hPositiveRoots, RootPairing.Base.isPos_iff]
          rw [← hDP.2.2.2.2 α]
          exact hpos
        exact le_of_not_gt hnot
      have hlow := hLowest.2 α hαpos
      have hlow_nonpos : D.height lowestRoot ≤ 0 := by
        have hnot : ¬ 0 < D.height lowestRoot := by
          intro hpos
          apply hLowest.1
          rw [hPositiveRoots, RootPairing.Base.isPos_iff]
          rw [← hDP.2.2.2.2 lowestRoot]
          exact hpos
        exact le_of_not_gt hnot
      rw [RootGroupData.IsRealization.neg_height hD lowestRoot]
      omega
  have hmaxBase : ∀ γ : ι, b.height γ ≤ b.height (e (D.neg lowestRoot)) := by
    intro γ
    calc
      b.height γ = D.height (e.symm γ) := by
        simpa using (hDP.2.2.2.2 (e.symm γ)).symm
      _ ≤ D.height (D.neg lowestRoot) := hmax (e.symm γ)
      _ = b.height (e (D.neg lowestRoot)) := hDP.2.2.2.2 _
  have hhighestEq : e (D.neg lowestRoot) = highest :=
    hhighest_unique _ hmaxBase
  intro α hα
  have hheightEq : D.height α = D.height (D.neg lowestRoot) := by
    have hupper := hmax α
    have hlower : D.height (D.neg lowestRoot) ≤ D.height α := by
      simpa only [hc] using hα
    exact le_antisymm hupper hlower
  have hαmax : ∀ γ : ι, b.height γ ≤ b.height (e α) := by
    intro γ
    calc
      b.height γ = D.height (e.symm γ) := by
        simpa using (hDP.2.2.2.2 (e.symm γ)).symm
      _ ≤ D.height (D.neg lowestRoot) := hmax (e.symm γ)
      _ = D.height α := hheightEq.symm
      _ = b.height (e α) := hDP.2.2.2.2 _
  have hαEq : e α = highest := hhighest_unique _ hαmax
  apply e.injective
  exact hαEq.trans hhighestEq.symm

/-! The center endpoint with terminal-root uniqueness discharged from the
    root-system extrema theorem.  Only the genuinely independent quotient
    detection premise remains exposed. -/

public theorem center_eq_terminal_rootLayer_of_commutator_detection_of_lowest
    {K : Variety k} [AlgebraicGroup K] {T U : ClosedSubgroup K}
    (D : RootGroupData K T) (lowestRoot : D.Root)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) (b : P.Base) (positiveRoots : Set D.Root)
    (Uheight : ℕ → ClosedSubgroup K) (c : ℕ)
    (hD : D.IsRealization)
    (hDP : IsRootSystemRealization D P e b)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ b.IsPos (e α))
    (hLowest : IsLowestRoot D positiveRoots lowestRoot)
    (hFirst : (Uheight 1).toSubgroup = U.toSubgroup)
    (hHeightLe : ∀ i, 0 < i → Uheight i ≤ U)
    (hHeightCommutator : ∀ i, 0 < i →
      ⁅(Uheight i).toSubgroup, U.toSubgroup⁆ ≤
        (Uheight (i + 1)).toSubgroup)
    (hTerminal : (Uheight (c + 1)).toSubgroup = ⊥)
    (hDetect : ∀ n, n < c →
      ∀ x : U.toSubgroup, x ∉
        (Uheight (c - n)).toSubgroup.subgroupOf U.toSubgroup →
        ∃ y : U.toSubgroup,
          ⁅(x : Variety.Point K), (y : Variety.Point K)⁆ ∉
            (Uheight (c + 1 - n)).toSubgroup)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (hcpos : 0 < c) (hc : (c : ℤ) = D.height (D.neg lowestRoot)) :
    Subgroup.map U.toSubgroup.subtype (Subgroup.center U.toSubgroup) =
      (D.rootSubgroup (D.neg lowestRoot)).toSubgroup := by
  have hUnique : ∀ α : D.Root, (c : ℤ) ≤ D.height α →
      α = D.neg lowestRoot :=
    terminal_height_root_unique_of_lowest D P e b positiveRoots lowestRoot
      hD hDP hPositiveRoots hLowest c hc
  exact center_eq_terminal_rootLayer_of_commutator_detection
    D lowestRoot Uheight c hFirst hHeightLe hHeightCommutator hTerminal
    hDetect hUheight hcpos hc hUnique

end Theory.AlgebraicGroup
