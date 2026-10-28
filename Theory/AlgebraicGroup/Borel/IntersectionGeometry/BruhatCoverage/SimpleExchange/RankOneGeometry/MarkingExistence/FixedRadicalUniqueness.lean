module

public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.Inputs
public import Theory.AlgebraicGroup.Borel.PositiveRootSupportGeometry.FixedRadicalRoots.Weights
public import Theory.AlgebraicGroup.RootSubgroups.BorelContainment
public import Theory.AlgebraicGroup.RootSubgroups.MultiplicityOne
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups.Reduction
public import Theory.AlgebraicGroup.Dimension.Strict

/-!
Root-subgroup uniqueness from the existing fixed-radical geometric input.

Put a root subgroup and the torus inside a Borel. The root subgroup lies in
the unipotent radical fixed by the connected kernel of its character. That
kernel has codimension one. If every such fixed radical is trivial or a
chosen root group, nontriviality and dimension one force equality with a
chosen group. Uniqueness of the weight then identifies the root index.
Algebraic automorphisms of the additive line give the scalar comparison of
any two parametrizations.

This connects the fixed-radical input of Borel §§13.14 and 13.18(4)--(5) to
GLS3, 1.9.5(b). It does not assume or construct a normalizer root action.
-/

universe u
namespace Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry

open SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
open BorelFixedRadicalRoots
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
variable {D : RootGroupData G T}

/-- The fixed-radical assertion supplied by the existing codimension-one
Borel geometry task, universally over Borels containing this torus. -/
@[expose] public def HasBorelFixedRootGroups (D : RootGroupData G T) : Prop :=
  ∀ B U : ClosedSubgroup G, IsBorelSubgroup B → T ≤ B →
    IsUnipotentRadicalOf B U → ∀ Q : CodimensionOneSubtorus T,
      (U.pointwiseCentralizer Q.val).toSubgroup = ⊥ ∨
        ∃ a, U.pointwiseCentralizer Q.val = D.rootSubgroup a

private theorem oneParameter_eq_of_le {X Y : ClosedSubgroup G}
    (hX : IsOneParameterGroup X.carrierVariety)
    (hY : IsOneParameterGroup Y.carrierVariety) (hXY : X ≤ Y) : X = Y := by
  have hconn (Z : ClosedSubgroup G) (hZ : IsOneParameterGroup Z.carrierVariety) :
      _root_.IsConnected (Z : Set (Variety.Point G)) := by
    have h := hZ.isConnected.image Z.inclusion.onPoints
      Z.inclusion.toVariety.continuous.continuousOn
    rwa [Set.image_univ, Z.range_inclusion] at h
  by_contra hne
  have hlt := connected_closedSubgroup_dimension_lt_of_le_of_ne X Y hXY hne
    (hconn X hX) (hconn Y hY)
  rw [hX.dimension_eq_one, hY.dimension_eq_one] at hlt
  exact (lt_irrefl _) hlt

/-- Every root subgroup with a specified realized weight is the chosen root
subgroup, provided the codimension-one fixed radicals have the source form. -/
public theorem rootSubgroup_eq_of_borel_fixed_roots (hD : D.IsRealization)
    (hT : IsSubtorus T) (hfixed : HasBorelFixedRootGroups D)
    (β : D.Root) (X : ClosedSubgroup G) (hX : IsTorusRootSubgroup T X)
    (hχ : RootWeightEquation T X (D.rootWeight β)) : X = D.rootSubgroup β := by
  obtain ⟨B, hB, hTB, hXB⟩ := exists_borelSubgroup_containing_torusRootSubgroup T X hT hX
  obtain ⟨U, hU, _⟩ := exists_unipotentRadical_of_connected_solvable B hB.connected hB.solvable
  let χ := D.rootWeight β
  have hne : χ ≠ 1 := realized_rootWeight_ne_one hD β
  have hK := χ.connectedKernel_codimension_one T hT hne
  let Q : CodimensionOneSubtorus T := ⟨χ.ambientConnectedKernel T,
    hK.ambientConnectedKernel_isSubtorus, hK.ambientConnectedKernel_le,
    hK.ambientConnectedKernel_dimension_add_one⟩
  have hXU : X ≤ U := hU.contains_unipotent_closedSubgroup hB.connected hB.solvable
    hXB hX.2.isUnipotentAlgebraicGroup
  have hXC : X ≤ Q.val.centralizer := root_le_connectedKernel_centralizer hT hX hχ hne
  have hXF : X ≤ U.pointwiseCentralizer Q.val := fun _ hx => ⟨hXU hx, hXC hx⟩
  rcases hfixed B U hB hTB hU Q with hbot | ⟨a, ha⟩
  · exfalso
    apply hX.invariant_unipotent_ne_bot.2.2
    apply le_antisymm _ bot_le
    intro x hx
    rw [← hbot]
    exact hXF hx
  · rw [ha] at hXF
    have hXa := oneParameter_eq_of_le hX.2 (hD.2.2.1 a).1.2 hXF
    rw [hXa] at hχ
    have hβa : β = a := hD.1 (rootWeightEquation_unique T (D.rootSubgroup a)
      (hD.2.2.1 a).1.2 hχ (hD.2.2.1 a).2)
    rwa [hβa]

/-- Fixed-radical geometry supplies the operational multiplicity-one premise
used by the SL₂ marking assembly. -/
public theorem multiplicityOne_of_borel_fixed_roots (hD : D.IsRealization)
    (hT : IsSubtorus T) (hfixed : HasBorelFixedRootGroups D)
    (β : D.Root) : RootWeightSpaceMultiplicityOne T (D.rootWeight β) := by
  intro X Y hX hXχ hY hYχ x y
  have hXY : X = Y :=
    (rootSubgroup_eq_of_borel_fixed_roots hD hT hfixed β X hX hXχ).trans
      (rootSubgroup_eq_of_borel_fixed_roots hD hT hfixed β Y hY hYχ).symm
  subst Y
  let e : Iso (KPlus k) (KPlus k) := y.symm.comp x
  obtain ⟨c, hc, _⟩ := kPlus_automorphism_eq_scalar e
  refine ⟨c, hc.1, ?_⟩
  intro t
  have h := congrArg y.hom.onPoints (hc.2 t)
  change y.hom.onPoints (y.inv.onPoints (x.value t)) = y.value (c * t) at h
  rw [y.inv_hom_id] at h
  exact congrArg X.includePoint h

end Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry
