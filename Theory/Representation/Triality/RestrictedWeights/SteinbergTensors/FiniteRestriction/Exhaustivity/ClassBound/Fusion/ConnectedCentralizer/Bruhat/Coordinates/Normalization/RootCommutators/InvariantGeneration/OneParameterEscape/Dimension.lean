module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.InvariantGeneration.OneParameterEscape.FixedSubgroups
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment

/-!
# Fixed-subgroup dimensions from earlier Borel geometry

The unipotent radical of the intersection of the Borels containing the torus
vanishes once its ambient normality is known. Semisimple geometry then bounds
the subtorus fixed subgroups of the positive Borel radical by dimension one.
For a semiregular subtorus the fixed subgroup is trivial; for a singular
codimension-one subtorus the bound is Borel IV, 13.15(1), with its actual
intersection denominator proved trivial here.

The centralizer inclusions, singular dimension bound and intersection-radical
normality remain explicit earlier geometric inputs. They are the outputs of
the independent Bor1 geometry owners, not one-parameter escape assumptions.
Source: `refs/KGroup/Bor1/Chapter4.tex`, 13.12--13.17.
-/

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.SemisimpleCenterContainment
open Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry
open Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
namespace ConnectedCentralizer.Bruhat.Coordinates.Normalization.OneParameterEscape
noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] [CharP k 2] in
private theorem dimension_zero_of_subgroup_eq_bot (Y : ClosedSubgroup K)
    (hY : Y.toSubgroup = ⊥) : Variety.dimension Y.carrierVariety = 0 := by
  apply (dimension_zero_iff_finite_points Y.carrierVariety).mpr
  have hf : Finite Y.toSubgroup := by rw [hY]; infer_instance
  exact Y.pointEquiv.finite_iff.mpr hf

/-- Ambient normality kills the actual intersection radical in the supplied
semisimple D4 group. No relative-normality premise is silently strengthened. -/
public theorem intersectionRadical_eq_bot (S : Geometry K)
    (hnormal : ∀ U : ClosedSubgroup K,
      IsUnipotentRadicalOf (torusBorelIntersection S.torus) U → U.toSubgroup.Normal)
    (U : ClosedSubgroup K)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection S.torus) U) :
    U.toSubgroup = ⊥ :=
  connectedRadical_eq_bot_of_reductive
    (isReductive_of_isSemisimple S.universal.semisimple) U (hnormal U hU)
    (intersection_radical_isConnected S.torus U S.maximalTorus.1 hU) hU.2.1

/-- A fixed subgroup contained in the Borel intersection is trivial under the
proved-normality input to Borel 13.16. -/
public theorem fixedSubgroup_eq_bot_of_le_intersection (S : Geometry K)
    (X : ClosedSubgroup K) (hXu : IsUnipotentAlgebraicGroup X.carrierVariety)
    (hnormal : ∀ U : ClosedSubgroup K,
      IsUnipotentRadicalOf (torusBorelIntersection S.torus) U → U.toSubgroup.Normal)
    (q : FixedIndex S)
    (hq : fixedSubgroup S X q ≤ torusBorelIntersection S.torus) :
    (fixedSubgroup S X q).toSubgroup = ⊥ := by
  obtain ⟨hIc, hIs⟩ := torusBorelIntersection_connected_solvable S.torus S.maximalTorus.1
  obtain ⟨U, hU, _⟩ := exists_unipotentRadical_of_connected_solvable
    (torusBorelIntersection S.torus) hIc hIs
  have hle := hU.contains_unipotent_closedSubgroup hIc hIs hq
    (fixedSubgroup_unipotent S X hXu q)
  exact le_antisymm ((intersectionRadical_eq_bot S hnormal U hU) ▸ hle) bot_le

/-- Earlier centralizer and singular-Borel geometry bound every member of the
fixed-subgroup generating family by dimension one. -/
public theorem fixedSubgroup_dimension_le_one_of_borel_geometry (S : Geometry K)
    (X : ClosedSubgroup K) (hXU : X ≤ S.bigCell.data.positive_witness.unipotent)
    (hXc : IsConnected (X : Set (Variety.Point K)))
    (hXt : IsClosedSubgroupInvariant S.torus X)
    (hXu : IsUnipotentAlgebraicGroup X.carrierVariety)
    (hnormal : ∀ U : ClosedSubgroup K,
      IsUnipotentRadicalOf (torusBorelIntersection S.torus) U → U.toSubgroup.Normal)
    (hcentralizer : S.torus.centralizer ≤ torusBorelIntersection S.torus)
    (hsemiregular : ∀ Q : CodimensionOneSubtorus S.torus,
      Finite (BorelContainingIndex Q.1) → Q.1.centralizer ≤ torusBorelIntersection S.torus)
    (hsingular : ∀ (U : ClosedSubgroup K),
      IsUnipotentRadicalOf (torusBorelIntersection S.torus) U →
      ∀ Q : CodimensionOneSubtorus S.torus, Infinite (BorelContainingIndex Q.1) →
        Variety.dimension
          (S.bigCell.data.positive_witness.unipotent.pointwiseCentralizer Q.1).carrierVariety ≤
        Variety.dimension
          ((S.bigCell.data.positive_witness.unipotent.pointwiseCentralizer Q.1).inter U).carrierVariety + 1)
    (q : FixedIndex S) : Variety.dimension (fixedSubgroup S X q).carrierVariety ≤ 1 := by
  classical
  cases q with
  | none =>
      have hbot := fixedSubgroup_eq_bot_of_le_intersection S X hXu hnormal none
        (fun _ hx => hcentralizer hx.2)
      rw [dimension_zero_of_subgroup_eq_bot _ hbot]
      exact zero_le
  | some Q =>
      by_cases hfin : Finite (BorelContainingIndex Q.1)
      · have hbot := fixedSubgroup_eq_bot_of_le_intersection S X hXu hnormal (some Q)
          (fun _ hx => hsemiregular Q hfin hx.2)
        rw [dimension_zero_of_subgroup_eq_bot _ hbot]
        exact zero_le
      · have hinf : Infinite (BorelContainingIndex Q.1) := not_finite_iff_infinite.mp hfin
        obtain ⟨hIc, hIs⟩ := torusBorelIntersection_connected_solvable S.torus S.maximalTorus.1
        obtain ⟨U, hU, _⟩ := exists_unipotentRadical_of_connected_solvable
          (torusBorelIntersection S.torus) hIc hIs
        have hUbot := intersectionRadical_eq_bot S hnormal U hU
        have hinter :
            ((S.bigCell.data.positive_witness.unipotent.pointwiseCentralizer Q.1).inter U).toSubgroup = ⊥ := by
          apply le_antisymm
          · intro x hx
            exact hUbot ▸ hx.2
          · exact bot_le
        have hdim := hsingular U hU Q hinf
        rw [dimension_zero_of_subgroup_eq_bot _ hinter, zero_add] at hdim
        apply le_trans _ hdim
        exact connected_closedSubgroup_dimension_le_of_le _ _
          (fixedSubgroup_connected S X hXc hXt hXu (some Q))
          (fun _ hx => ⟨hXU hx.1, hx.2⟩)

end
end ConnectedCentralizer.Bruhat.Coordinates.Normalization.OneParameterEscape
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
