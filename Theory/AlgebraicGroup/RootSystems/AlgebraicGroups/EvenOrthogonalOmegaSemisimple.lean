module

public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
public import Theory.AlgebraicGroup.Dimension.Finite
public import Theory.AlgebraicGroup.Representations.NormalSolvableScalar
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenSpinIsogeny
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalOmegaConnected
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalNaturalIrreducibility
public import Theory.AlgebraicGroup.Semisimple.Defs

/-!
# Semisimplicity of the split even-orthogonal Omega carrier

For a split quadratic form of hyperbolic rank at least four, this module proves
that the closed image of the characteristic-free Spin action is semisimple.  It
combines the connectedness of that image with the irreducibility of its natural
representation, without using the type-D classification.

Indeed, a radical acts by scalars because it is connected, normal, and
solvable.  Preservation of the quadratic form on an explicit norm-one
hyperbolic vector forces every such scalar `a` to satisfy `a * a = 1`.
Faithfulness of the natural action therefore makes the radical finite.  Its
connectedness then forces it to be trivial by the positive-dimension theorem
for nontrivial connected closed subgroups.  This supplies the structural input
needed to construct the projective Omega quotient.
-/

universe u

open scoped BigOperators

namespace Theory.AlgebraicGroup

set_option linter.style.haveILetI false

variable {k V : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

private theorem evenOrthogonalNaturalRepresentation_action_injective
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    Function.Injective (evenOrthogonalNaturalRepresentation s).action := by
  dsimp only
  intro x y hxy
  rw [evenOrthogonalNaturalRepresentation_action s,
    evenOrthogonalNaturalRepresentation_action s] at hxy
  apply (evenSpinActionImageClosedSubgroup Q s).inclusion_injective
  exact (glPointEquivOf k V (Module.finBasis k V)).injective hxy

private noncomputable def splitNormOneVector
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) : V :=
  s.isometry.symm
    (Pi.single ⟨0, lt_of_lt_of_le (by decide) hrank⟩ 1,
      Pi.single ⟨0, lt_of_lt_of_le (by decide) hrank⟩ 1)

omit [IsAlgClosed k] in
private theorem splitNormOneVector_norm
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    Q (splitNormOneVector s hrank) = 1 := by
  rw [splitNormOneVector, ← s.isometry.map_app]
  simp only [hyperbolicForm_apply]
  rw [Fintype.sum_eq_single
    ⟨0, lt_of_lt_of_le (by decide) hrank⟩]
  · simp
  · intro j hj
    simp [hj]

private theorem omega_scalar_sq_one
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank)
    (g : Variety.Point (evenSpinActionImageClosedSubgroup Q s).carrierVariety)
    (a : k) (ha :
      ((evenOrthogonalNaturalRepresentation s).action g : Module.End k V) =
        a • LinearMap.id) :
    a * a = 1 := by
  let S := splitSpinClosedSubgroup s
  let I := evenSpinActionImageClosedSubgroup Q s
  letI := S.carrierAlgebraicGroup
  letI := I.carrierAlgebraicGroup
  let v := splitNormOneVector s hrank
  let e := evenSpinActionImageClosedSubgroupPoints Q s hrank g
  have he : Q (e.1.1 v) = Q v :=
    (mem_quadraticIsometrySubgroup Q e.1.1).1 e.1.2 v
  have haction :
      ((evenOrthogonalNaturalRepresentation s).action g : Module.End k V) = e.1.1 := by
    apply LinearMap.ext
    intro w
    exact LinearEquiv.congr_fun
      (evenOrthogonalNaturalRepresentation_action_linear_points s hrank g) w
  have haction_v : e.1.1 v = a • v := by
    have haction_v' := LinearMap.congr_fun haction v
    calc
      e.1.1 v =
          ((evenOrthogonalNaturalRepresentation s).action g : Module.End k V) v := by
        exact haction_v'.symm
      _ = (a • LinearMap.id) v := by rw [ha]
      _ = a • v := by simp
  rw [haction_v, QuadraticMap.map_smul] at he
  rw [splitNormOneVector_norm s hrank] at he
  simpa only [smul_eq_mul, mul_one] using he

private theorem omega_radical_eq_bot
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank)
    (hconnected : _root_.IsConnected
      (Set.univ : Set (Variety.Point
        (evenSpinActionImageClosedSubgroup Q s).carrierVariety)))
    (hirr : IsIrreducibleRepresentation (evenOrthogonalNaturalRepresentation s))
    (R : ClosedSubgroup
      (evenSpinActionImageClosedSubgroup Q s).carrierVariety)
    (hR : IsRadicalSubgroup R) : R.toSubgroup = ⊥ := by
  let S := splitSpinClosedSubgroup s
  let I := evenSpinActionImageClosedSubgroup Q s
  letI := S.carrierAlgebraicGroup
  letI := I.carrierAlgebraicGroup
  let ρ := evenOrthogonalNaturalRepresentation s
  have hvne : splitNormOneVector s hrank ≠ 0 := by
    intro hv
    have hvnorm := splitNormOneVector_norm s hrank
    rw [hv, map_zero] at hvnorm
    exact zero_ne_one hvnorm
  letI : Nontrivial V := ⟨⟨splitNormOneVector s hrank, 0, hvne⟩⟩
  have hRvar : Variety.IsConnected R.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph R.isZariskiClosed
    let : ConnectedSpace
        {x : Variety.Point I.carrierVariety // x ∈
          (R : Set (Variety.Point I.carrierVariety))} :=
      Subtype.connectedSpace hR.connected
    let : ConnectedSpace (Variety.Point R.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  obtain ⟨χ, hχ⟩ := ρ.acts_by_scalars_of_isIrreducible hirr
    hconnected R hR.normal hR.solvable hRvar
  have hroots : ({a : k | a * a = 1} : Set k).Finite := by
    apply ((Set.finite_singleton (-1 : k)).insert (1 : k)).subset
    intro a ha
    have hfactor : (a - 1) * (a + 1) = 0 := by
      calc
        (a - 1) * (a + 1) = a * a - 1 := by ring
        _ = 0 := by rw [ha]; ring
    rcases mul_eq_zero.mp hfactor with h | h
    · left
      exact sub_eq_zero.mp h
    · right
      exact eq_neg_of_add_eq_zero_left h
  let roots := {a : k // a * a = 1}
  letI : Finite roots := Set.finite_coe_iff.mpr hroots
  let embed : R.toSubgroup → roots := fun r =>
    ⟨χ r, omega_scalar_sq_one s hrank r.1 (χ r) (hχ r)⟩
  have hembed : Function.Injective embed := by
    intro x y hxy
    apply Subtype.ext
    apply evenOrthogonalNaturalRepresentation_action_injective s
    change ρ.action (x : Variety.Point I.carrierVariety) =
      ρ.action (y : Variety.Point I.carrierVariety)
    have hsc : χ x = χ y := by
      have hval := congrArg Subtype.val hxy
      change χ x = χ y at hval
      exact hval
    apply Units.ext
    rw [hχ x, hχ y, hsc]
  letI : Finite R.toSubgroup := Finite.of_injective embed hembed
  have hRpointsFinite : Finite (Variety.Point R.carrierVariety) :=
    (Equiv.finite_iff R.pointEquiv).mpr inferInstance
  have hRdim : Variety.dimension R.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points R.carrierVariety).mpr hRpointsFinite
  by_contra hRne
  have hRpos := connected_closedSubgroup_dimension_pos_of_ne_bot
    R hR.connected hRne
  rw [hRdim] at hRpos
  exact (lt_irrefl 0 hRpos)

/-- The closed image of the split even Spin action is semisimple in hyperbolic
rank at least four. -/
public theorem evenSpinActionImageClosedSubgroup_isSemisimple
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    IsSemisimpleAlgebraicGroup
      (evenSpinActionImageClosedSubgroup Q s).carrierVariety := by
  have hconnected := evenSpinActionImageClosedSubgroup_isConnected s hrank
  refine ⟨hconnected, ?_⟩
  intro R hR
  exact omega_radical_eq_bot s hrank hconnected
    (evenOrthogonalNaturalRepresentation_isIrreducible s hrank) R hR

end Theory.AlgebraicGroup
