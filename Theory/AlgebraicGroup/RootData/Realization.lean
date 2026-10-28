module

public import Theory.AlgebraicGroup.RootData.Chevalley

universe u

open scoped BigOperators

/-!
Actual based root-pairing and root-datum realizations.

The realized height clauses make the canonical positive set additive-closed and
disjoint from its negation.  To obtain the covering axiom of a positive system
we keep the genuinely additional hypothesis that every realized root has
nonzero height.  Negation is involutive already: injectivity of `rootWeight`
and the inverse-weight clause force `neg (neg α) = α`.

An actual based root pairing identifies `D.simple` pointwise with the support
of its genuine root-system base.  The set-level image theorem below is the
stable interface used when forming parabolic root subsystems.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Negation reverses the height in a realized root-group datum. -/
public lemma RootGroupData.IsRealization.neg_height
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization) (α : D.Root) :
    D.height (D.neg α) = -D.height α :=
  hD.2.2.2.2.2.2.2.2.1 α

omit [IsAlgClosed k] in
/-- Negation is an involution on a realized root index.

This is not an independent field of `RootGroupData.IsRealization`: applying
the inverse-weight clause twice and using injectivity of `rootWeight` proves it.
-/
public lemma RootGroupData.IsRealization.neg_neg
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization) (α : D.Root) :
    D.neg (D.neg α) = α := by
  rcases hD with ⟨hinj, _, _, hnegweight, _, _, _, _, _, _, _, _, _⟩
  apply hinj
  rw [hnegweight, hnegweight]
  simp

omit [IsAlgClosed k] in
/-- The canonical height-positive roots form a positive system when no root
has zero height.

The nonzero-height premise is explicit because the current realization
contract does not rule out height-zero labels.  The proof uses only the
negation-height and addition-height clauses already stored in the realization;
the covering axiom is the sole place where the extra premise is needed.
-/
public theorem RootGroupData.IsRealization.positive_isPositiveSystem_of_height_ne_zero
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization)
    (hheight : ∀ α : D.Root, D.height α ≠ 0) :
    IsPositiveSystem D D.positive := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, hnegheight, haddheight,
    hpositive, _, _⟩
  rw [hpositive]
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    intro α hα
    rcases hα with ⟨hαpos, hnegpos⟩
    change 0 < D.height α at hαpos
    change 0 < D.height (D.neg α) at hnegpos
    rw [hnegheight α] at hnegpos
    omega
  · rw [Set.eq_univ_iff_forall]
    intro α
    by_cases hαpos : 0 < D.height α
    · exact Or.inl hαpos
    · right
      change 0 < D.height (D.neg α)
      rw [hnegheight α]
      have hαne := hheight α
      have hαneg : D.height α < 0 := by omega
      omega
  · intro α hαpos β hβpos γ hadd
    change 0 < D.height α at hαpos
    change 0 < D.height β at hβpos
    change 0 < D.height γ
    rw [haddheight α β γ hadd]
    omega

omit [IsAlgClosed k] in
/-- Existential form of the realized positive-system witness, using the
canonical set `D.positive` and an explicit nonzero-height certificate. -/
public theorem RootGroupData.IsRealization.exists_positiveSystem_of_height_ne_zero
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization)
    (hheight : ∀ α : D.Root, D.height α ≠ 0) :
    ∃ P : Set D.Root, IsPositiveSystem D P :=
  ⟨D.positive, hD.positive_isPositiveSystem_of_height_ne_zero hheight⟩

@[expose]
public noncomputable def HasSimpleRootExpansion
    {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (base : P.Base)
    (coeff : ι → ι → ℤ) : Prop := by
  letI : Fintype ι := Fintype.ofFinite ι
  exact ∀ β,
    P.root β = ∑ γ ∈ base.support, (coeff β γ : R) • P.root γ ∧
      ∀ γ, γ ∉ base.support → coeff β γ = 0

/-- The root pairing and base are the actual pairing and simple roots carried
by `D`, rather than an unrelated abstract root system. -/
@[expose]
public def IsActualBasedRootPairing
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (base : P.Base) (e : D.Root ≃ ι) : Prop :=
  (∀ α β, (D.pairing α β : R) = P.pairing (e α) (e β)) ∧
    (∀ α β, e (D.reflect α β) = P.reflectionPerm (e α) (e β)) ∧
    (∀ α, e (D.neg α) = P.reflectionPerm (e α) (e α)) ∧
    ∀ α, α ∈ D.simple ↔ e α ∈ base.support

omit [IsAlgClosed k] in
/-- Under an actual based realization, the realized simple roots are exactly
the support of the root-system base. -/
public theorem IsActualBasedRootPairing.image_simple_eq_base_support
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} {base : P.Base} {e : D.Root ≃ ι}
    (hActual : IsActualBasedRootPairing D P base e) :
    e '' D.simple = (base.support : Set ι) := by
  ext i
  constructor
  · rintro ⟨alpha, halpha, rfl⟩
    exact (hActual.2.2.2 alpha).1 halpha
  · intro hi
    refine ⟨e.symm i, (hActual.2.2.2 (e.symm i)).2 ?_, ?_⟩
    · simpa using hi
    · simp

/-- The integral root pairing, its base, and its positive roots are realized
by the actual torus roots carried by `D`. -/
@[expose]
public def IsActualBasedRootDatum
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) (base : P.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (positiveRoots : Set D.Root) : Prop :=
  IsActualBasedRootPairing D P base e ∧
    IsRootDatumRealization D P e weightEquiv ∧
    ∀ α, α ∈ positiveRoots ↔ base.IsPos (e α)

end

end Theory.AlgebraicGroup
