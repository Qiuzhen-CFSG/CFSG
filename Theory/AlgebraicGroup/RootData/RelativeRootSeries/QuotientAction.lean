module

public import Theory.GroupAction.Quotient
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.Basic

universe u v

set_option linter.style.haveILetI false

/-!
Conjugation actions of a subgroup preserving the relative-root filtration.

The constructions in this file are deliberately abstract: no choice of root
parameters is made.  A subgroup which normalizes two adjacent terms acts on
the corresponding quotient by conjugation.  This is the group-theoretic Levi
action used by the relative-root filtration.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- The conjugation action of a subgroup which normalizes a subgroup `S` on
`S`, obtained by composing the canonical normalizer action with the inclusion
of the given subgroup into the normalizer. -/
@[reducible]
private noncomputable def subgroupConjugationAction
    {K : Variety k} [AlgebraicGroup K]
    (L S : Subgroup (Variety.Point K))
    (hL : L ≤ Subgroup.normalizer (S : Set (Variety.Point K))) :
    MulDistribMulAction L S := by
  let ι : L →* Subgroup.normalizer (S : Set (Variety.Point K)) :=
    { toFun := fun l => ⟨l.1, hL l.2⟩
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  exact MulDistribMulAction.compHom S ι

/-- A subgroup preserving two adjacent terms of the relative-root series
induces a multiplicative action on the quotient of the first by the second.

The returned action is the canonical quotient action, so its scalar action on
`QuotientGroup.mk'` is represented by conjugation in the ambient group. -/
@[reducible]
public noncomputable def relativeRootSeries_quotient_conjugation_action
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (J : Set D.Root) (i : ℕ)
    (L : Subgroup (Variety.Point K))
    (hL : ∀ l : L, ∀ j : ℕ,
      (l.1 : Variety.Point K) ∈
        Subgroup.normalizer
          (RelativeRootSeries D e base.support coeff J j :
            Set (Variety.Point K)))
    (hN : ((RelativeRootSeries D e base.support coeff J (i + 1)).subgroupOf
      (RelativeRootSeries D e base.support coeff J i)).Normal) :
    MulDistribMulAction L
      ((RelativeRootSeries D e base.support coeff J i) ⧸
        (RelativeRootSeries D e base.support coeff J (i + 1)).subgroupOf
          (RelativeRootSeries D e base.support coeff J i)) := by
  let S : Subgroup (Variety.Point K) :=
    RelativeRootSeries D e base.support coeff J i
  let Snext : Subgroup (Variety.Point K) :=
    RelativeRootSeries D e base.support coeff J (i + 1)
  let hLi : L ≤ Subgroup.normalizer (S : Set (Variety.Point K)) := by
    intro l hl
    exact hL ⟨l, hl⟩ i
  let hLnext : L ≤ Subgroup.normalizer (Snext : Set (Variety.Point K)) := by
    intro l hl
    exact hL ⟨l, hl⟩ (i + 1)
  letI : MulDistribMulAction L S := subgroupConjugationAction L S hLi
  let N : Subgroup S := Snext.subgroupOf S
  let hInv : IsInvariant L S N := by
    constructor
    intro l x
    change x.1 ∈ Snext ↔
      ((subgroupConjugationAction L S hLi).smul l x :
        Variety.Point K) ∈ Snext
    change x.1 ∈ Snext ↔ l.1 * x.1 * l.1⁻¹ ∈ Snext
    have hnorm := hLnext l.2
    rw [Subgroup.mem_normalizer_iff] at hnorm
    exact hnorm x.1
  let : IsInvariant L S N := hInv
  let : N.Normal := hN
  exact quotientMulDistribMulAction N hInv

/-- Computation rule for the relative-root quotient action.  It is the
pointwise form needed when comparing the abstract quotient action with a
chosen Levi representation. -/
public lemma relativeRootSeries_quotient_conjugation_action_mk
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (J : Set D.Root) (i : ℕ)
    (L : Subgroup (Variety.Point K))
    (hL : ∀ l : L, ∀ j : ℕ,
      (l.1 : Variety.Point K) ∈
        Subgroup.normalizer
          (RelativeRootSeries D e base.support coeff J j :
            Set (Variety.Point K)))
    (hN : ((RelativeRootSeries D e base.support coeff J (i + 1)).subgroupOf
      (RelativeRootSeries D e base.support coeff J i)).Normal)
    (l : L) (x : RelativeRootSeries D e base.support coeff J i) :
    (relativeRootSeries_quotient_conjugation_action D P e base coeff J i L hL hN).smul l
        (QuotientGroup.mk' ((RelativeRootSeries D e base.support coeff J (i + 1)).subgroupOf
          (RelativeRootSeries D e base.support coeff J i)) x) =
      QuotientGroup.mk'
        ((RelativeRootSeries D e base.support coeff J (i + 1)).subgroupOf
          (RelativeRootSeries D e base.support coeff J i))
        ⟨l.1 * x.1 * l.1⁻¹, by
          have hnorm := hL l i
          rw [Subgroup.mem_normalizer_iff] at hnorm
          exact (hnorm x.1).mp x.2⟩ := by
  let S : Subgroup (Variety.Point K) :=
    RelativeRootSeries D e base.support coeff J i
  let Snext : Subgroup (Variety.Point K) :=
    RelativeRootSeries D e base.support coeff J (i + 1)
  let hLi : L ≤ Subgroup.normalizer (S : Set (Variety.Point K)) := by
    intro a ha
    exact hL ⟨a, ha⟩ i
  letI : MulDistribMulAction L S := subgroupConjugationAction L S hLi
  let N : Subgroup S := Snext.subgroupOf S
  let hInv : IsInvariant L S N := by
    constructor
    intro a y
    change y.1 ∈ Snext ↔
      ((subgroupConjugationAction L S hLi).smul a y : Variety.Point K) ∈ Snext
    change y.1 ∈ Snext ↔ a.1 * y.1 * a.1⁻¹ ∈ Snext
    have hnorm := hL (⟨a.1, a.2⟩ : L) (i + 1)
    rw [Subgroup.mem_normalizer_iff] at hnorm
    exact hnorm y.1
  let : IsInvariant L S N := hInv
  let : N.Normal := hN
  change _ = QuotientGroup.mk' N
    ⟨l.1 * x.1 * l.1⁻¹, by
      have hnorm := hL l i
      rw [Subgroup.mem_normalizer_iff] at hnorm
      exact (hnorm x.1).mp x.2⟩
  rfl

/-- The monoid homomorphism recording the automorphism of an adjacent-layer
quotient induced by each Levi element. -/
@[reducible]
public noncomputable def relativeRootSeries_quotient_conjugation_hom
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (J : Set D.Root) (i : ℕ)
    (L : Subgroup (Variety.Point K))
    (hL : ∀ l : L, ∀ j : ℕ,
      (l.1 : Variety.Point K) ∈
        Subgroup.normalizer
          (RelativeRootSeries D e base.support coeff J j :
            Set (Variety.Point K)))
    (hN : ((RelativeRootSeries D e base.support coeff J (i + 1)).subgroupOf
      (RelativeRootSeries D e base.support coeff J i)).Normal) :
    L →* MulAut
      ((RelativeRootSeries D e base.support coeff J i) ⧸
        (RelativeRootSeries D e base.support coeff J (i + 1)).subgroupOf
          (RelativeRootSeries D e base.support coeff J i)) := by
  letI : MulDistribMulAction L
      ((RelativeRootSeries D e base.support coeff J i) ⧸
        (RelativeRootSeries D e base.support coeff J (i + 1)).subgroupOf
          (RelativeRootSeries D e base.support coeff J i)) :=
    relativeRootSeries_quotient_conjugation_action D P e base coeff J i L hL hN
  exact MulDistribMulAction.toMulAut L _

end
end Theory.AlgebraicGroup
