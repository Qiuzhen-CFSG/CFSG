module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Theory.AlgebraicGroup.RootSubgroups.Defs
public import Theory.AlgebraicGroup.RootSystems.Defs
public import Theory.AlgebraicGroup.Semisimple.Versions

universe u

open scoped BigOperators

/-!
Generic Chevalley-system and root-datum realization interfaces.

Root addition has two compatible interfaces.  The model-specific
`IsRootAdditionRealization` here identifies `D.add` with vector addition in a
chosen root pairing.  An actual root-datum identification transports it to the
model-independent `RootGroupData.IsRootAdditionComplete` contract at the
root-group-data layer.
-/

namespace Theory.AlgebraicGroup

public structure ChevalleyData
    {k : Type u} [Field k]
    (G : Variety k) [AlgebraicGroup G]
    {T : ClosedSubgroup G} (D : RootGroupData G T) where
  x : D.Root → k → Variety.Point G
  n : D.Root → kˣ → Variety.Point G
  h : D.Root → kˣ → Variety.Point G

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def IsUSingular (R : RootClassification) (p : ℕ) : Prop :=
  (p = 2 ∧ (R.kind = .B ∨ R.kind = .C ∨ R.kind = .F4 ∨ R.kind = .G2)) ∨
    (p = 3 ∧ R.kind = .G2)

public structure ChevalleyCommutatorTerm (Root : Type*) where
  i : ℕ
  j : ℕ
  root : Root

@[expose]
public def IsValidChevalleyCommutatorTerm
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (α β : D.Root)
    (q : ChevalleyCommutatorTerm D.Root) : Prop :=
  0 < q.i ∧ 0 < q.j ∧
    P.root (e q.root) =
      (q.i : R) • P.root (e α) + (q.j : R) • P.root (e β)

@[expose]
public def AreLinearlyIndependentRoots
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Field R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (e : D.Root ≃ ι)
    (α β : D.Root) : Prop :=
  ∀ a b : R,
    a • P.root (e α) + b • P.root (e β) = 0 → a = 0 ∧ b = 0

@[expose]
public noncomputable def RootSquaredLength
    {ι R M N : Type*} [Finite ι] [Field R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (α : ι) : R := by
  letI := Fintype.ofFinite ι
  exact P.RootForm (P.root α) (P.root α)

@[expose]
public def IsChevalleyCoefficientExceptionalTwo
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (α β : D.Root)
    (q : ChevalleyCommutatorTerm D.Root) : Prop :=
  -- Exceptional cases classify coefficients of terms that actually occur in
  -- the Chevalley commutator product; arbitrary triples are not exceptional.
  IsValidChevalleyCommutatorTerm D P e α β q ∧
    let len (γ : D.Root) := RootSquaredLength P (e γ)
    (q.i = 1 ∧ q.j = 1 ∧ len α = len β ∧ len q.root = 2 * len α) ∨
    (q.i = 1 ∧ q.j = 1 ∧ len α = len β ∧ len q.root = len α ∧
      ∃ r : ChevalleyCommutatorTerm D.Root,
        IsValidChevalleyCommutatorTerm D P e α β r ∧
          ((r.i = 2 ∧ r.j = 1) ∨ (r.i = 1 ∧ r.j = 2))) ∨
    (q.i = 3 ∧ q.j = 2 ∧ α ∈ D.simple ∧ β ∈ D.simple ∧ α ≠ β ∧
      len β = 3 * len α)

@[expose]
public def IsChevalleyCoefficientExceptionalThree
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (α β : D.Root)
    (q : ChevalleyCommutatorTerm D.Root) : Prop :=
  -- As in the source formula, the exceptional-3 alternatives apply only to
  -- valid commutator terms for the chosen pair of roots.
  IsValidChevalleyCommutatorTerm D P e α β q ∧
    let len (γ : D.Root) := RootSquaredLength P (e γ)
    (q.i = 1 ∧ q.j = 1 ∧ len α = len β ∧ len q.root = 3 * len α) ∨
    (((q.i = 2 ∧ q.j = 1) ∨ (q.i = 1 ∧ q.j = 2)) ∧
      ∃ γ : D.Root,
        P.root (e γ) = P.root (e α) + P.root (e β) ∧
          len α = len β ∧ len γ = len α)

@[expose]
public def HasExpectedChevalleyCoefficient
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (α β : D.Root)
    (q : ChevalleyCommutatorTerm D.Root) (c : k) : Prop :=
  (IsChevalleyCoefficientExceptionalTwo D P e α β q →
    c = 2 ∨ c = -2) ∧
  (IsChevalleyCoefficientExceptionalThree D P e α β q →
    c = 3 ∨ c = -3) ∧
  (¬ IsChevalleyCoefficientExceptionalTwo D P e α β q →
    ¬ IsChevalleyCoefficientExceptionalThree D P e α β q →
      c = 1 ∨ c = -1)

omit [IsAlgClosed k] in
/-- Expected Chevalley coefficients are nonzero when the field
characteristic is neither two nor three. -/
public lemma HasExpectedChevalleyCoefficient.ne_zero_of_ringChar_ne_two_three
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) {α β : D.Root}
    {q : ChevalleyCommutatorTerm D.Root} {c : k}
    (hchar2 : ringChar k ≠ 2) (hchar3 : ringChar k ≠ 3)
    (h : HasExpectedChevalleyCoefficient D P e α β q c) :
    c ≠ 0 := by
  intro hc
  by_cases htwo : IsChevalleyCoefficientExceptionalTwo D P e α β q
  · rcases h.1 htwo with hc2 | hc2
    · rw [hc2] at hc
      exact Ring.two_ne_zero hchar2 hc
    · rw [hc2] at hc
      exact Ring.two_ne_zero hchar2 (neg_eq_zero.mp hc)
  by_cases hthree : IsChevalleyCoefficientExceptionalThree D P e α β q
  · have hthree_ne : (3 : k) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime (R := k) Nat.prime_three hchar3
    rcases h.2.1 hthree with hc3 | hc3
    · rw [hc3] at hc
      exact hthree_ne hc
    · rw [hc3] at hc
      exact hthree_ne (neg_eq_zero.mp hc)
  · rcases h.2.2 htwo hthree with hc1 | hc1
    · rw [hc1] at hc
      exact one_ne_zero hc
    · rw [hc1] at hc
      exact one_ne_zero (neg_eq_zero.mp hc)

omit [IsAlgClosed k] in
/-- Expected Chevalley coefficients are nonzero in a nonsingular
characteristic once the exceptional root patterns are assigned to their
possible Dynkin families. -/
public lemma HasExpectedChevalleyCoefficient.ne_zero_of_nonsingular
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (classification : RootClassification) {α β : D.Root}
    {q : ChevalleyCommutatorTerm D.Root} {c : k}
    (hNonsingular : ¬ IsUSingular classification (ringChar k))
    (hTwoKind : IsChevalleyCoefficientExceptionalTwo D P e α β q →
      classification.kind = .B ∨ classification.kind = .C ∨
        classification.kind = .F4 ∨ classification.kind = .G2)
    (hThreeKind : IsChevalleyCoefficientExceptionalThree D P e α β q →
      classification.kind = .G2)
    (h : HasExpectedChevalleyCoefficient D P e α β q c) :
    c ≠ 0 := by
  intro hc
  by_cases htwo : IsChevalleyCoefficientExceptionalTwo D P e α β q
  · have hchar2 : ringChar k ≠ 2 := by
      intro hchar
      apply hNonsingular
      rcases hTwoKind htwo with hB | hC | hF4 | hG2
      · exact Or.inl ⟨hchar, Or.inl hB⟩
      · exact Or.inl ⟨hchar, Or.inr (Or.inl hC)⟩
      · exact Or.inl ⟨hchar, Or.inr (Or.inr (Or.inl hF4))⟩
      · exact Or.inl ⟨hchar, Or.inr (Or.inr (Or.inr hG2))⟩
    rcases h.1 htwo with hc2 | hc2
    · rw [hc2] at hc
      exact Ring.two_ne_zero hchar2 hc
    · rw [hc2] at hc
      exact Ring.two_ne_zero hchar2 (neg_eq_zero.mp hc)
  by_cases hthree : IsChevalleyCoefficientExceptionalThree D P e α β q
  · have hchar3 : ringChar k ≠ 3 := by
      intro hchar
      exact hNonsingular (Or.inr ⟨hchar, hThreeKind hthree⟩)
    have hthree_ne : (3 : k) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime (R := k) Nat.prime_three hchar3
    rcases h.2.1 hthree with hc3 | hc3
    · rw [hc3] at hc
      exact hthree_ne hc
    · rw [hc3] at hc
      exact hthree_ne (neg_eq_zero.mp hc)
  · rcases h.2.2 htwo hthree with hc1 | hc1
    · rw [hc1] at hc
      exact one_ne_zero hc
    · rw [hc1] at hc
      exact one_ne_zero (neg_eq_zero.mp hc)

@[expose]
public def IsRootSystemRealization
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) : Prop :=
  -- Dynkin classification is deliberately not stored here: it is an
  -- independent root-system theorem/bridge, not a conclusion-bearing field.
  (∀ α β, (D.pairing α β : R) = P.pairing (e α) (e β)) ∧
  (∀ α β, e (D.reflect α β) = P.reflectionPerm (e α) (e β)) ∧
  (∀ α, e (D.neg α) = P.reflectionPerm (e α) (e α)) ∧
  (∀ α, α ∈ D.simple ↔ e α ∈ b.support) ∧
  (∀ α, D.height α = b.height (e α))

/-- The partial operation carried by `D.add` is exactly root addition in the
chosen root-pairing model.  This is kept separate from the older realization
predicate so existing root-group consumers retain their tuple projections. -/
@[expose]
public def IsRootAdditionRealization
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (e : D.Root ≃ ι) : Prop :=
  ∀ α β γ, D.add α β = some γ ↔
    P.root (e γ) = P.root (e α) + P.root (e β)

omit [IsAlgClosed k] in
public lemma IsRootAdditionRealization.add_of_root_eq_add
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} {e : D.Root ≃ ι}
    (hAdd : IsRootAdditionRealization D P e) {α β γ : D.Root}
    (hroot : P.root (e γ) = P.root (e α) + P.root (e β)) :
    D.add α β = some γ :=
  (hAdd α β γ).mpr hroot

@[expose]
public def IsChevalleySystem
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) : Prop :=
  (∀ α, Function.Injective (C.x α) ∧ Set.range (C.x α) = D.rootSubgroup α) ∧
  (∀ α t, C.n α t =
    C.x α t * C.x (D.neg α) (-((t : k)⁻¹)) * C.x α t) ∧
  (∀ α t, C.h α t = (C.n α 1)⁻¹ * C.n α t) ∧
  (∀ α t u, C.x α t * C.x α u = C.x α (t + u)) ∧
  (∀ α β, AreLinearlyIndependentRoots D P e α β →
    ∃ order : List (ChevalleyCommutatorTerm D.Root),
    ∃ c : ChevalleyCommutatorTerm D.Root → k,
      order.Nodup ∧
      order.Pairwise (fun q r => q.i + q.j ≤ r.i + r.j) ∧
      (∀ q, q ∈ order ↔ IsValidChevalleyCommutatorTerm D P e α β q) ∧
      (∀ q ∈ order, HasExpectedChevalleyCoefficient D P e α β q (c q)) ∧
      ∀ t u,
        (C.x α t)⁻¹ * (C.x β u)⁻¹ * C.x α t * C.x β u =
          (order.map fun q => C.x q.root (c q * t ^ q.i * u ^ q.j)).prod) ∧
  (∀ α β t u, C.h α t * C.h β u = C.h β u * C.h α t) ∧
  (∀ α t u, C.h α t * C.h α u = C.h α (t * u)) ∧
  (∃ coeff : D.Root → b.support → ℤ,
    (∀ α, P.coroot (e α) = ∑ i, coeff α i • P.coroot i) ∧
    ∀ α t, C.h α t =
      (b.support.attach.toList.map fun i : b.support =>
        C.h (e.symm i) (t ^ coeff α i)).prod) ∧
  (IsUniversalVersion K →
    ∀ t : b.support → kˣ,
      (b.support.attach.toList.map fun i : b.support =>
        C.h (e.symm i) (t i)).prod = 1 ↔
        ∀ i, t i = 1) ∧
  (IsAdjointVersion K →
    ∀ t : b.support → kˣ,
      (b.support.attach.toList.map fun i : b.support =>
        C.h (e.symm i) (t i)).prod = 1 ↔
        ∀ j, (∏ i, t i ^ D.pairing (e.symm j) (e.symm i)) = 1) ∧
  (∃ weights : b.support → TorusWeight T,
    Set.range D.rootWeight ⊆ Subgroup.closure (Set.range weights) ∧
    ∀ t : b.support → kˣ,
      (b.support.attach.toList.map fun i : b.support =>
        C.h (e.symm i) (t i)).prod = 1 ↔
        ∀ j, (∏ i, t i ^ D.weightPairing (weights j) (e.symm i)) = 1) ∧
  (∀ α β t u, (C.h β u)⁻¹ * C.x α t * C.h β u =
    C.x α ((u : k) ^ D.pairing α β * t)) ∧
  (∃ sign : D.Root → D.Root → kˣ,
    (∀ α β, sign α β = 1 ∨ sign α β = -1) ∧
    (∀ α β t, (C.n β 1)⁻¹ * C.x α t * C.n β 1 =
      C.x (D.reflect β α) ((sign α β : k) * t)) ∧
    (∀ α β t, (C.n β 1)⁻¹ * C.h α t * C.n β 1 =
      C.h (D.reflect β α) t) ∧
    ∀ α β t, (C.n β 1)⁻¹ * C.n α t * C.n β 1 =
      C.n (D.reflect β α) (sign α β * t)) ∧
  ∀ α, C.n α 1 * C.n α 1 = C.h α (-1)

@[expose]
public def ChevalleyCommutatorTermWordProduct
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    (word : List (ChevalleyCommutatorTerm D.Root × k)) : Variety.Point K :=
  (word.map fun z => C.x z.1.root z.2).prod

/-- The root datum is identified with the roots and character lattice of the
chosen maximal torus. -/
@[expose]
public def IsRootDatumRealization
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T) : Prop :=
  ∀ α, weightEquiv (Multiplicative.ofAdd (P.root (e α))) = D.rootWeight α

omit [IsAlgClosed k] in
/-- A root-pairing addition realization becomes complete addition on the actual
torus roots once the root-pairing vectors are identified with their weights. -/
public theorem IsRootAdditionRealization.isRootAdditionComplete
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    {P : RootPairing ι ℤ X Y} {e : D.Root ≃ ι}
    {weightEquiv : Multiplicative X ≃* TorusWeight T}
    (hAdd : IsRootAdditionRealization D P e)
    (hDatum : IsRootDatumRealization D P e weightEquiv) :
    D.IsRootAdditionComplete := by
  intro α β γ hweight
  apply (hAdd α β γ).mpr
  apply Multiplicative.ofAdd.injective
  apply weightEquiv.injective
  rw [ofAdd_add, map_mul, hDatum α, hDatum β, hDatum γ]
  exact hweight

omit [IsAlgClosed k] in
public lemma rootSubgroup_ne_bot_of_chevalleySystem
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base)
    (hC : IsChevalleySystem D C P e b) (α : D.Root) :
    (D.rootSubgroup α).toSubgroup ≠ ⊥ := by
  intro hbot
  have hxmem : C.x α (1 : k) ∈ (D.rootSubgroup α).toSubgroup := by
    change C.x α (1 : k) ∈ (D.rootSubgroup α : Set (Variety.Point K))
    rw [← (hC.1 α).2]
    exact ⟨1, rfl⟩
  rw [hbot] at hxmem
  have hxone : C.x α (1 : k) = 1 := hxmem
  have hxzero : C.x α (0 : k) = 1 := by
    simpa using (hC.2.2.2.1 α 0 0)
  have h10 : (1 : k) = 0 := by
    apply (hC.1 α).1
    rw [hxone, hxzero]
  exact (one_ne_zero : (1 : k) ≠ 0) h10

end

end Theory.AlgebraicGroup
