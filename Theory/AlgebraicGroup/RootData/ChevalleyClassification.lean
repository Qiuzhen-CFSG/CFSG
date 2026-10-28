module

public import Theory.AlgebraicGroup.RootData.Chevalley
public import Theory.AlgebraicGroup.RootSystems.Classification

universe u

set_option linter.style.haveILetI false

/-! Dynkin classification consequences for exceptional Chevalley coefficients. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The equal-length, double-length exceptional coefficient pattern occurs
only in a non-simply-laced Dynkin family. -/
public lemma chevalleyCoefficient_doubleLength_kind_of_hasDynkinType
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) {α β : D.Root}
    {q : ChevalleyCommutatorTerm D.Root}
    (hvalid : IsValidChevalleyCommutatorTerm D P e α β q)
    (hqi : q.i = 1) (hqj : q.j = 1)
    (hlen : RootSquaredLength P (e α) = RootSquaredLength P (e β))
    (hlenq : RootSquaredLength P (e q.root) =
      2 * RootSquaredLength P (e α))
    (classification : RootClassification)
    (hType : HasDynkinType P classification) :
    classification.kind = .B ∨ classification.kind = .C ∨
      classification.kind = .F4 ∨ classification.kind = .G2 := by
  letI := Fintype.ofFinite ι
  have hroot : P.root (e q.root) = P.root (e α) + P.root (e β) := by
    simpa [hqi, hqj] using hvalid.2.2
  apply root_sum_double_length_kind_of_hasDynkinType P
    (e α) (e β) (e q.root) hroot
  · simpa [RootSquaredLength] using hlen
  · simpa [RootSquaredLength] using hlenq
  · exact hType

private lemma pairingIn_eq_swap_of_rootForm_eq
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (i j : ι)
    (hlen : P.RootForm (P.root i) (P.root i) =
      P.RootForm (P.root j) (P.root j)) :
    P.pairingIn ℤ i j = P.pairingIn ℤ j i := by
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → R))
  have hrootLen : P.RootForm (P.root i) (P.root i) ≠ 0 :=
    RootPairing.IsAnisotropic.rootForm_root_ne_zero i
  apply mul_right_cancel₀ hrootLen
  have hswap :=
    ((P.posRootForm ℤ).toInvariantForm).pairing_mul_eq_pairing_mul_swap i j
  have hswap' :
      (P.pairingIn ℤ i j : R) * P.RootForm (P.root j) (P.root j) =
        (P.pairingIn ℤ j i : R) * P.RootForm (P.root i) (P.root i) := by
    change P.pairing j i * P.RootForm (P.root i) (P.root i) =
      P.pairing i j * P.RootForm (P.root j) (P.root j) at hswap
    simpa [← P.algebraMap_pairingIn ℤ i j,
      ← P.algebraMap_pairingIn ℤ j i] using hswap.symm
  rwa [← hlen] at hswap'

private lemma rootForm_root_sum
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    (i j γ : ι) (hγ : P.root γ = P.root i + P.root j) :
    P.RootForm (P.root γ) (P.root γ) =
      P.RootForm (P.root i) (P.root i) +
        P.RootForm (P.root j) (P.root j) +
          2 * P.RootForm (P.root i) (P.root j) := by
  rw [hγ]
  simp only [map_add, LinearMap.add_apply, add_assoc]
  rw [show P.RootForm (P.root j) (P.root i) =
    P.RootForm (P.root i) (P.root j) by
      exact P.rootForm_symmetric.eq _ _]
  ring

private lemma exists_pairingIn_three_of_root_sum_triple_length
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (i j γ : ι)
    (hγ : P.root γ = P.root i + P.root j)
    (hlen : P.RootForm (P.root i) (P.root i) =
      P.RootForm (P.root j) (P.root j))
    (hlenγ : P.RootForm (P.root γ) (P.root γ) =
      3 * P.RootForm (P.root i) (P.root i)) :
    ∃ a b, P.pairingIn ℤ a b = 3 := by
  have hrootLen : P.RootForm (P.root i) (P.root i) ≠ 0 :=
    RootPairing.IsAnisotropic.rootForm_root_ne_zero i
  have hpEq := pairingIn_eq_swap_of_rootForm_eq P i j hlen
  have hpair :=
    ((P.posRootForm ℤ).toInvariantForm).two_mul_apply_root_root i j
  have hpair' :
      2 * P.RootForm (P.root i) (P.root j) =
        (P.pairingIn ℤ i j : R) * P.RootForm (P.root j) (P.root j) := by
    change 2 * P.RootForm (P.root i) (P.root j) =
      P.pairing i j * P.RootForm (P.root j) (P.root j) at hpair
    simpa [← P.algebraMap_pairingIn ℤ i j] using hpair
  have hrootEq :
      P.RootForm (P.root γ) (P.root γ) =
        2 * P.RootForm (P.root i) (P.root i) +
          (P.pairingIn ℤ i j : R) *
            P.RootForm (P.root j) (P.root j) := by
    rw [rootForm_root_sum P i j γ hγ, hpair', hlen]
    ring
  have hzero :
      ((P.pairingIn ℤ i j : R) - 1) *
        P.RootForm (P.root j) (P.root j) = 0 := by
    rw [hlenγ, hlen] at hrootEq
    calc
      _ = (2 * P.RootForm (P.root j) (P.root j) +
          (P.pairingIn ℤ i j : R) * P.RootForm (P.root j) (P.root j)) -
          3 * P.RootForm (P.root j) (P.root j) := by ring
      _ = 0 := by rw [← hrootEq]; ring
  have hne : P.RootForm (P.root j) (P.root j) ≠ 0 := by
    intro hj
    exact hrootLen (hlen.trans hj)
  have hpCast : (P.pairingIn ℤ i j : R) = 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hne)
  have hp : P.pairingIn ℤ i j = 1 := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → R))
    simpa using hpCast
  refine ⟨γ, i, ?_⟩
  rw [P.pairingIn_eq_add_of_root_eq_add hγ, ← hpEq, hp]
  norm_num

private lemma exists_pairingIn_three_of_two_root_sum_equal_lengths
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (i j γ δ : ι)
    (hγ : P.root γ = P.root i + P.root j)
    (hδ : P.root δ = (2 : R) • P.root i + (1 : R) • P.root j)
    (hlen : P.RootForm (P.root i) (P.root i) =
      P.RootForm (P.root j) (P.root j))
    (hlenγ : P.RootForm (P.root γ) (P.root γ) =
      P.RootForm (P.root i) (P.root i)) :
    ∃ a b, P.pairingIn ℤ a b = 3 := by
  have hrootLen : P.RootForm (P.root i) (P.root i) ≠ 0 :=
    RootPairing.IsAnisotropic.rootForm_root_ne_zero i
  have hpEq := pairingIn_eq_swap_of_rootForm_eq P i j hlen
  have hpair :=
    ((P.posRootForm ℤ).toInvariantForm).two_mul_apply_root_root i j
  have hpair' :
      2 * P.RootForm (P.root i) (P.root j) =
        (P.pairingIn ℤ i j : R) * P.RootForm (P.root j) (P.root j) := by
    change 2 * P.RootForm (P.root i) (P.root j) =
      P.pairing i j * P.RootForm (P.root j) (P.root j) at hpair
    simpa [← P.algebraMap_pairingIn ℤ i j] using hpair
  have hrootEq :
      P.RootForm (P.root γ) (P.root γ) =
        2 * P.RootForm (P.root i) (P.root i) +
          (P.pairingIn ℤ i j : R) *
            P.RootForm (P.root j) (P.root j) := by
    rw [rootForm_root_sum P i j γ hγ, hpair', hlen]
    ring
  have hzero :
      ((P.pairingIn ℤ i j : R) + 1) *
        P.RootForm (P.root j) (P.root j) = 0 := by
    rw [hlenγ, hlen] at hrootEq
    calc
      _ = (2 * P.RootForm (P.root j) (P.root j) +
            (P.pairingIn ℤ i j : R) * P.RootForm (P.root j) (P.root j)) -
          P.RootForm (P.root j) (P.root j) := by ring
      _ = 0 := by rw [← hrootEq]; ring
  have hne : P.RootForm (P.root j) (P.root j) ≠ 0 := by
    intro hj
    exact hrootLen (hlen.trans hj)
  have hpCast : (P.pairingIn ℤ i j : R) = -1 :=
    eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hzero).resolve_right hne)
  have hp : P.pairingIn ℤ i j = -1 := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → R))
    simpa using hpCast
  refine ⟨δ, i, ?_⟩
  have hδ' : P.root δ = P.root i + P.root γ := by
    rw [hδ, hγ]
    module
  rw [P.pairingIn_eq_add_of_root_eq_add hδ',
    P.pairingIn_eq_add_of_root_eq_add hγ, ← hpEq, hp]
  simp only [P.pairingIn_same]
  norm_num

private lemma exists_pairingIn_three_of_triple_length_term
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (i j γ : ι)
    (hγ : P.root γ = (3 : R) • P.root i + (2 : R) • P.root j)
    (hlen : P.RootForm (P.root j) (P.root j) =
      3 * P.RootForm (P.root i) (P.root i)) :
    ∃ a b, P.pairingIn ℤ a b = 3 := by
  have hrootLen : P.RootForm (P.root i) (P.root i) ≠ 0 :=
    RootPairing.IsAnisotropic.rootForm_root_ne_zero i
  have hswap :=
    ((P.posRootForm ℤ).toInvariantForm).pairing_mul_eq_pairing_mul_swap i j
  have hswap' :
      (P.pairingIn ℤ i j : R) * P.RootForm (P.root j) (P.root j) =
        (P.pairingIn ℤ j i : R) * P.RootForm (P.root i) (P.root i) := by
    change P.pairing j i * P.RootForm (P.root i) (P.root i) =
      P.pairing i j * P.RootForm (P.root j) (P.root j) at hswap
    simpa [← P.algebraMap_pairingIn ℤ i j,
      ← P.algebraMap_pairingIn ℤ j i] using hswap.symm
  have hratioCast :
      (P.pairingIn ℤ j i : R) = 3 * (P.pairingIn ℤ i j : R) := by
    apply mul_right_cancel₀ hrootLen
    calc
      _ = (P.pairingIn ℤ i j : R) *
          P.RootForm (P.root j) (P.root j) := hswap'.symm
      _ = (3 * (P.pairingIn ℤ i j : R)) *
          P.RootForm (P.root i) (P.root i) := by rw [hlen]; ring
  have hratio : P.pairingIn ℤ j i = 3 * P.pairingIn ℤ i j := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → R))
    simpa using hratioCast
  have hγpair :
      P.pairingIn ℤ γ i = 6 + 2 * P.pairingIn ℤ j i := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → R))
    change algebraMap ℤ R (P.pairingIn ℤ γ i) =
      algebraMap ℤ R (6 + 2 * P.pairingIn ℤ j i)
    rw [P.algebraMap_pairingIn, map_add, map_mul,
      P.algebraMap_pairingIn]
    rw [P.pairing_eq_add_of_root_eq_smul_add_smul hγ]
    simp
    ring
  have hpairs :=
    P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  have hγpairs :=
    P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed γ i
  have hthree :
      P.pairingIn ℤ j i = 3 ∨ P.pairingIn ℤ j i = -3 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at hpairs hγpairs
    omega
  rcases hthree with hthree | hthree
  · exact ⟨j, i, hthree⟩
  · refine ⟨P.reflectionPerm j j, i, ?_⟩
    rw [P.pairingIn_reflectionPerm_self_left, hthree]
    norm_num

/-- Every exceptional-two Chevalley coefficient pattern occurs only in a
Dynkin family singular in characteristic two. -/
public lemma chevalleyExceptionalTwo_kind_of_hasDynkinType
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) {α β : D.Root}
    {q : ChevalleyCommutatorTerm D.Root}
    (classification : RootClassification)
    (hType : HasDynkinType P classification)
    (hExceptional : IsChevalleyCoefficientExceptionalTwo D P e α β q) :
    classification.kind = .B ∨ classification.kind = .C ∨
      classification.kind = .F4 ∨ classification.kind = .G2 := by
  letI := Fintype.ofFinite ι
  rcases hExceptional with ⟨hvalid, hfirst | hsecond | hthird⟩
  · rcases hfirst with ⟨hqi, hqj, hlen, hlenq⟩
    exact chevalleyCoefficient_doubleLength_kind_of_hasDynkinType
      D P e hvalid hqi hqj hlen hlenq classification hType
  · rcases hsecond with ⟨hqi, hqj, hlen, hlenq, r, hrvalid, hrij⟩
    have hqroot : P.root (e q.root) = P.root (e α) + P.root (e β) := by
      simpa [hqi, hqj] using hvalid.2.2
    have hG2 : P.IsG2 := by
      rcases hrij with h21 | h12
      · have hrroot : P.root (e r.root) =
            (2 : R) • P.root (e α) + (1 : R) • P.root (e β) := by
          simpa [h21.1, h21.2] using hrvalid.2.2
        obtain ⟨a, b, hpair⟩ :=
          exists_pairingIn_three_of_two_root_sum_equal_lengths P
            (e α) (e β) (e q.root) (e r.root) hqroot hrroot
            (by simpa [RootSquaredLength] using hlen)
            (by simpa [RootSquaredLength] using hlenq)
        let : P.EmbeddedG2 :=
          RootPairing.EmbeddedG2.ofPairingInThree P a b hpair
        infer_instance
      · have hqroot' : P.root (e q.root) =
            P.root (e β) + P.root (e α) := by simpa [add_comm] using hqroot
        have hrroot : P.root (e r.root) =
            (2 : R) • P.root (e β) + (1 : R) • P.root (e α) := by
          rw [hrvalid.2.2, h12.1, h12.2]
          norm_num
          rw [add_comm]
        obtain ⟨a, b, hpair⟩ :=
          exists_pairingIn_three_of_two_root_sum_equal_lengths P
            (e β) (e α) (e q.root) (e r.root) hqroot' hrroot
            (by simpa [RootSquaredLength] using hlen.symm)
            (by simpa [RootSquaredLength] using hlenq.trans hlen)
        let : P.EmbeddedG2 :=
          RootPairing.EmbeddedG2.ofPairingInThree P a b hpair
        infer_instance
    let : P.IsG2 := hG2
    exact Or.inr (Or.inr (Or.inr
      (dynkinKind_eq_g2_of_isG2 P classification hType)))
  · rcases hthird with ⟨hqi, hqj, -, -, -, hlen⟩
    have hqroot : P.root (e q.root) =
        (3 : R) • P.root (e α) + (2 : R) • P.root (e β) := by
      simpa [hqi, hqj] using hvalid.2.2
    obtain ⟨a, b, hpair⟩ :=
      exists_pairingIn_three_of_triple_length_term P
        (e α) (e β) (e q.root) hqroot
        (by simpa [RootSquaredLength] using hlen)
    let : P.EmbeddedG2 := RootPairing.EmbeddedG2.ofPairingInThree P a b hpair
    have : P.IsG2 := inferInstance
    exact Or.inr (Or.inr (Or.inr
      (dynkinKind_eq_g2_of_isG2 P classification hType)))

/-- Either exceptional-three Chevalley pattern produces roots with integer
pairing three. -/
public lemma chevalleyExceptionalThree_pairingIn_three
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) {α β : D.Root}
    {q : ChevalleyCommutatorTerm D.Root}
    (hExceptional : IsChevalleyCoefficientExceptionalThree D P e α β q) :
    ∃ a b, P.pairingIn ℤ a b = 3 := by
  letI := Fintype.ofFinite ι
  rcases hExceptional with ⟨hvalid, hfirst | hsecond⟩
  · rcases hfirst with ⟨hqi, hqj, hlen, hlenq⟩
    have hroot : P.root (e q.root) = P.root (e α) + P.root (e β) := by
      simpa [hqi, hqj] using hvalid.2.2
    apply exists_pairingIn_three_of_root_sum_triple_length P
      (e α) (e β) (e q.root) hroot
    · simpa [RootSquaredLength] using hlen
    · simpa [RootSquaredLength] using hlenq
  · rcases hsecond with ⟨hij, γ, hγ, hlen, hlenγ⟩
    have hroot : P.root (e q.root) =
        (q.i : R) • P.root (e α) + (q.j : R) • P.root (e β) :=
      hvalid.2.2
    have hγroot : P.root (e γ) = P.root (e α) + P.root (e β) := by
      simpa using hγ
    rcases hij with h21 | h12
    · apply exists_pairingIn_three_of_two_root_sum_equal_lengths P
        (e α) (e β) (e γ) (e q.root) hγroot
        (by simpa [h21.1, h21.2] using hroot)
      · simpa [RootSquaredLength] using hlen
      · simpa [RootSquaredLength] using hlenγ
    · have hroot' : P.root (e q.root) =
          (2 : R) • P.root (e β) + (1 : R) • P.root (e α) := by
        rw [hroot, h12.1, h12.2]
        norm_num
        rw [add_comm]
      have hγroot' : P.root (e γ) = P.root (e β) + P.root (e α) := by
        simpa [add_comm] using hγroot
      apply exists_pairingIn_three_of_two_root_sum_equal_lengths P
        (e β) (e α) (e γ) (e q.root) hγroot' hroot'
      · simpa [RootSquaredLength] using hlen.symm
      · simpa [RootSquaredLength] using hlenγ.trans hlen

/-- Every exceptional-three Chevalley coefficient pattern forces an
irreducible root pairing to be of type `G2`. -/
public lemma chevalleyExceptionalThree_isG2
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) {α β : D.Root}
    {q : ChevalleyCommutatorTerm D.Root}
    (hExceptional : IsChevalleyCoefficientExceptionalThree D P e α β q) :
    P.IsG2 := by
  obtain ⟨a, b, hpair⟩ :=
    chevalleyExceptionalThree_pairingIn_three D P e hExceptional
  let : P.EmbeddedG2 := RootPairing.EmbeddedG2.ofPairingInThree P a b hpair
  infer_instance

/-- Every exceptional-three Chevalley coefficient pattern occurs only in
Dynkin type `G₂`. -/
public lemma chevalleyExceptionalThree_kind_of_hasDynkinType
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) {α β : D.Root}
    {q : ChevalleyCommutatorTerm D.Root}
    (classification : RootClassification)
    (hType : HasDynkinType P classification)
    (hExceptional : IsChevalleyCoefficientExceptionalThree D P e α β q) :
    classification.kind = .G2 := by
  let : P.IsG2 := chevalleyExceptionalThree_isG2 D P e hExceptional
  exact dynkinKind_eq_g2_of_isG2 P classification hType

/-- Under a concrete Dynkin classification, GLS nonsingularity makes every
expected Chevalley coefficient nonzero. -/
public lemma HasExpectedChevalleyCoefficient.ne_zero_of_nonsingular_of_hasDynkinType
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (e : D.Root ≃ ι) (classification : RootClassification)
    (hType : HasDynkinType P classification) {α β : D.Root}
    {q : ChevalleyCommutatorTerm D.Root} {c : k}
    (hNonsingular : ¬ IsUSingular classification (ringChar k))
    (h : HasExpectedChevalleyCoefficient D P e α β q c) :
    c ≠ 0 :=
  h.ne_zero_of_nonsingular D P e classification hNonsingular
    (chevalleyExceptionalTwo_kind_of_hasDynkinType
      D P e classification hType)
    (chevalleyExceptionalThree_kind_of_hasDynkinType
      D P e classification hType)

end Theory.AlgebraicGroup
