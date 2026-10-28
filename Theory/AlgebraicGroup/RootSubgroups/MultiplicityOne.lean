module

public import Theory.AlgebraicGroup.RootSubgroups.Conjugation

universe u

/-!
An operational form of the one-dimensional root-weight-space input needed for
root-subgroup uniqueness.  The predicate deliberately records only the
ambient scalar reparametrization; it does not package the desired subgroup
equality as an assumption.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

@[expose]
public def RootWeightSpaceMultiplicityOne
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (χ : TorusWeight T) : Prop :=
  ∀ {X Y : ClosedSubgroup K},
    IsTorusRootSubgroup T X → RootWeightEquation T X χ →
    IsTorusRootSubgroup T Y → RootWeightEquation T Y χ →
    ∀ (x : OneParameterParametrization X.carrierVariety)
      (y : OneParameterParametrization Y.carrierVariety),
      ∃ c : k, c ≠ 0 ∧ ∀ t,
        X.includePoint (x.value t) =
          Y.includePoint (y.value (c * t))

public lemma RootWeightSpaceMultiplicityOne.rootSubgroup_eq
    {K : Variety k} [AlgebraicGroup K]
    {T X Y : ClosedSubgroup K} {χ : TorusWeight T}
    (hmult : RootWeightSpaceMultiplicityOne T χ)
    (hX : IsTorusRootSubgroup T X) (hXχ : RootWeightEquation T X χ)
    (hY : IsTorusRootSubgroup T Y) (hYχ : RootWeightEquation T Y χ) :
    X = Y := by
  let x : OneParameterParametrization X.carrierVariety :=
    Classical.choice hX.2
  let y : OneParameterParametrization Y.carrierVariety :=
    Classical.choice hY.2
  obtain ⟨c, hc, hxy⟩ := hmult hX hXχ hY hYχ x y
  exact rootSubgroup_eq_of_parametrization_rescale x y c hc hxy

end

end Theory.AlgebraicGroup
