module

public import Theory.AlgebraicGroup.RootData.Realization

/-!
Fundamental roots of a realized positive system.

When the selected positive roots correspond under `e` to the positive roots of
the abstract base, the height compatibility in `IsRootSystemRealization`
identifies that set with `D.positive`.  The defining characterization of
`D.simple` in `D.IsRealization` then says exactly that its elements are the
positive roots not expressible by a declared sum of two positive roots.  This
identifies `FundamentalRootsFor D positiveRoots` with `base.support` and gives
the finite indexing equivalence used by simple-root torus constructions.

The argument uses only the forward equations already present in the
root-group datum: no converse root-addition realization is required.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A positive root is fundamental exactly when its realized root index lies
in the support of the chosen root-system base. -/
public theorem mem_fundamentalRootsFor_iff_mem_baseSupport
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) {positiveRoots : Set D.Root}
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hD : D.IsRealization)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ base.IsPos (e α))
    (hRealization : IsRootSystemRealization D P e base) (α : D.Root) :
    α ∈ FundamentalRootsFor D positiveRoots ↔ e α ∈ base.support := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, hDpositive, hDsimple, _⟩
  rcases hRealization with ⟨_, _, _, hSimpleSupport, hHeight⟩
  have hPositiveEq : positiveRoots = D.positive := by
    ext β
    rw [hPositiveRoots, RootPairing.Base.isPos_iff, ← hHeight β, hDpositive]
    rfl
  rw [hPositiveEq]
  constructor
  · intro hα
    apply (hSimpleSupport α).mp
    apply (hDsimple α).mpr
    exact ⟨hα.1, fun β γ hAdd hβγ => hα.2 β hβγ.1 γ hβγ.2 hAdd⟩
  · intro hα
    have hSimple := (hDsimple α).mp ((hSimpleSupport α).mpr hα)
    exact ⟨hSimple.1, fun β hβ γ hγ hAdd => hSimple.2 β γ hAdd ⟨hβ, hγ⟩⟩

/-- The realized root-index equivalence from fundamental roots to the finite
support of the chosen base.  Its underlying map is the supplied realization
equivalence `e`, so consumers retain the intended root-character indexing. -/
public def fundamentalRootsEquivBaseSupport
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) {positiveRoots : Set D.Root}
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hD : D.IsRealization)
    (hPositiveRoots : ∀ α, α ∈ positiveRoots ↔ base.IsPos (e α))
    (hRealization : IsRootSystemRealization D P e base) :
    {α // α ∈ FundamentalRootsFor D positiveRoots} ≃ base.support where
  toFun α := ⟨e α, (mem_fundamentalRootsFor_iff_mem_baseSupport
    D P e base hD hPositiveRoots hRealization α).mp α.property⟩
  invFun i := ⟨e.symm i, (mem_fundamentalRootsFor_iff_mem_baseSupport
    D P e base hD hPositiveRoots hRealization (e.symm i)).mpr (by
      rw [e.apply_symm_apply]
      exact i.property)⟩
  left_inv α := Subtype.ext (e.symm_apply_apply α)
  right_inv i := Subtype.ext (e.apply_symm_apply i)

end Theory.AlgebraicGroup
