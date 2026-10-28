module

public import Theory.AlgebraicGroup.RootSystems.CliffordSpinCarrier
public import Theory.AlgebraicGroup.RootSystems.CliffordSplitLipschitz
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalSpinAction

/-!
# The closed split Clifford Spin carrier

For a finite-dimensional quadratic space equipped with an explicit
`SplitQuadraticForm` witness over an algebraically closed field of arbitrary
characteristic, this module realizes Mathlib's generated `spinGroup Q` as an
exact closed subgroup of `GL (CliffordAlgebra Q)`.  Its carrier is the image of
the left-regular representation, not its Zariski closure, and its variety
points are multiplicatively equivalent to `spinGroup Q`.

In positive split rank, the finite polynomial characterization from
`CliffordSpinCarrier` is applied with characteristic-free Spin conjugation and
the split-even reverse normalizer theorem from `CliffordSplitLipschitz`.  In
rank zero, the generating set in Mathlib's `lipschitzGroup` is empty: every
vector is zero, whose Clifford image is not a unit.  Thus the Spin group and
its left-regular image are both trivial, and the identity closed subgroup
gives the exact carrier.  These two cases prove closedness of the actual image
in every split rank.

The resulting carrier, exact membership theorem, point equivalence, and
ambient-linear compatibility are the lower-layer inputs for the split even
orthogonal Spin model.
-/

universe u

open CliffordAlgebra

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

omit [IsAlgClosed k] in
private lemma splitSpin_lipschitzGroup_eq_bot
    (s : SplitQuadraticForm Q) (hs : s.rank = 0) :
    lipschitzGroup Q = ⊥ := by
  let : Nontrivial (CliffordAlgebra Q) :=
    s.cliffordToExterior.symm.injective.nontrivial
  have hrank : Module.finrank k V = 0 := by
    rw [s.isometry.toLinearEquiv.finrank_eq]
    simp [hs]
  let _ : Subsingleton V :=
    (Module.finrank_eq_zero_iff_of_free k V).mp hrank
  rw [lipschitzGroup]
  have hgenerators :
      ((↑) ⁻¹' Set.range (CliffordAlgebra.ι Q) :
        Set (CliffordAlgebra Q)ˣ) = ∅ := by
    ext x
    constructor
    · rintro ⟨v, hv⟩
      have hv0 : v = 0 := Subsingleton.elim _ _
      subst v
      simp only [map_zero] at hv
      exact x.ne_zero hv.symm
    · simp
  rw [hgenerators, Subgroup.closure_empty]

omit [IsAlgClosed k] in
private lemma splitSpin_eq_one_of_rank_eq_zero
    (s : SplitQuadraticForm Q) (hs : s.rank = 0)
    (x : spinGroup Q) : x = 1 := by
  apply spinGroup.toUnits_injective
  have hx := spinGroup.units_mem_lipschitzGroup
    (x := spinGroup.toUnits x) x.property
  rw [splitSpin_lipschitzGroup_eq_bot s hs] at hx
  simpa using hx

private lemma splitSpinLeftRegularPointHom_range_eq_bot
    (s : SplitQuadraticForm Q) (hs : s.rank = 0)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    (spinLeftRegularPointHom e).range = ⊥ := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    rw [splitSpin_eq_one_of_rank_eq_zero s hs x]
    simp
  · intro hg
    have hg1 : g = 1 := by simpa using hg
    subst g
    exact ⟨1, map_one (spinLeftRegularPointHom e)⟩

private lemma splitSpinLeftRegularPointHom_range_isZariskiClosed
    (s : SplitQuadraticForm Q)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    IsZariskiClosed (glVarietyOf k (CliffordAlgebra Q))
      ((spinLeftRegularPointHom e).range :
        Set (Variety.Point (glVarietyOf k (CliffordAlgebra Q)))) := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  by_cases hs : 0 < s.rank
  · refine spinLeftRegularPointHom_range_isZariskiClosed
      (Q := Q) (b := b) (e := e) ?_ ?_
    · intro x v
      constructor
      · have hx := spinGroup.conjAct_smul_ι_mem_range_ι_of_field
          s.actionForm (x := spinGroup.toUnits x) x.prop v
        have hstar : star (x : CliffordAlgebra Q) =
            (x⁻¹ : spinGroup Q) := rfl
        simpa [ConjAct.units_smul_def, hstar] using hx
      · have hx := spinGroup.conjAct_smul_ι_mem_range_ι_of_field
          s.actionForm (x := spinGroup.toUnits x⁻¹) (x⁻¹).prop v
        have hstar : star (x : CliffordAlgebra Q) =
            (x⁻¹ : spinGroup Q) := rfl
        simpa [ConjAct.units_smul_def, hstar] using hx
    · intro u huEven huNormalizer
      exact
        mem_lipschitzGroup_of_mem_even_of_conjAct_smul_range_ι_eq_of_split
          s hs huEven huNormalizer
  · have hs0 : s.rank = 0 := Nat.eq_zero_of_not_pos hs
    rw [splitSpinLeftRegularPointHom_range_eq_bot s hs0 e]
    exact (ClosedSubgroup.bot
      (G := glVarietyOf k (CliffordAlgebra Q))).isZariskiClosed

/-- The characteristic-free PBW basis used to put the split Clifford algebra
inside the general-linear variety. -/
public noncomputable def splitSpinCliffordBasis
    (s : SplitQuadraticForm Q) :
    Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q) :=
  s.finBasis

/-- The exact closed left-regular carrier of Mathlib's generated split
Clifford Spin group. -/
public noncomputable def splitSpinClosedSubgroup
    (s : SplitQuadraticForm Q) :
    ClosedSubgroup (glVarietyOf k (CliffordAlgebra Q)) := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let b := Module.finBasis k V
  let e := splitSpinCliffordBasis s
  exact ClosedSubgroup.ofSubgroup (spinLeftRegularPointHom e).range
    (splitSpinLeftRegularPointHom_range_isZariskiClosed s b e)

/-- Membership in the split Spin carrier is exactly left multiplication by a
genuine element of Mathlib's generated `spinGroup Q`. -/
public theorem splitSpinClosedSubgroup_carrier
    (s : SplitQuadraticForm Q)
    (g : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    g ∈ (splitSpinClosedSubgroup s).toSubgroup ↔
      ∃ x : spinGroup Q,
        LinearMap.GeneralLinearGroup.generalLinearEquiv k (CliffordAlgebra Q)
            (glPointEquivOf k (CliffordAlgebra Q)
              (splitSpinCliffordBasis s) g) =
          (spinGroup.toUnits x).mulLeftLinearEquiv k (CliffordAlgebra Q) := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  change g ∈ (spinLeftRegularPointHom (splitSpinCliffordBasis s)).range ↔ _
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    rw [← cliffordSpinLinearPointMulEquiv_apply_eq]
    exact cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom
      (splitSpinCliffordBasis s) x
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply (cliffordSpinLinearPointMulEquiv
      (splitSpinCliffordBasis s)).injective
    rw [cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom]
    rw [cliffordSpinLinearPointMulEquiv_apply_eq]
    exact hx.symm

/-- Rational points of the exact split carrier, with their inherited product,
are multiplicatively equivalent to Mathlib's generated `spinGroup Q`. -/
public noncomputable def splitSpinClosedSubgroupPoints
    (s : SplitQuadraticForm Q) :
    let H := splitSpinClosedSubgroup s
    letI := H.carrierAlgebraicGroup
    Variety.Point H.carrierVariety ≃* spinGroup Q := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let H := splitSpinClosedSubgroup s
  let pointEquiv : Variety.Point H.carrierVariety ≃* H.toSubgroup :=
    { toEquiv := H.pointEquiv
      map_mul' := fun _ _ => rfl }
  exact pointEquiv.trans
    (MonoidHom.ofInjective
      (spinLeftRegularPointHom_injective (splitSpinCliffordBasis s))).symm

/-- The point equivalence agrees with the ambient left-regular representation
under the chosen split Clifford basis. -/
public theorem splitSpinClosedSubgroup_linear_points
    (s : SplitQuadraticForm Q) :
    let H := splitSpinClosedSubgroup s
    letI := H.carrierAlgebraicGroup
    ∀ x,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k (CliffordAlgebra Q)
          (glPointEquivOf k (CliffordAlgebra Q) (splitSpinCliffordBasis s)
            (H.inclusion.onPoints x)) =
        (spinGroup.toUnits
          (splitSpinClosedSubgroupPoints s x)).mulLeftLinearEquiv
            k (CliffordAlgebra Q) := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  dsimp only
  intro x
  let H := splitSpinClosedSubgroup s
  let y : H.toSubgroup := H.pointEquiv x
  rw [← cliffordSpinLinearPointMulEquiv_apply_eq]
  change cliffordSpinLinearPointMulEquiv (splitSpinCliffordBasis s)
      (H.inclusion.onPoints x) =
    (spinGroup.toUnits
      ((MonoidHom.ofInjective
        (spinLeftRegularPointHom_injective (splitSpinCliffordBasis s))).symm
          y)).mulLeftLinearEquiv k (CliffordAlgebra Q)
  rw [← cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom]
  congr 1
  have hy := congrArg Subtype.val
    ((MonoidHom.ofInjective
      (spinLeftRegularPointHom_injective (splitSpinCliffordBasis s))).apply_symm_apply y)
  exact hy.symm

end Theory.AlgebraicGroup
