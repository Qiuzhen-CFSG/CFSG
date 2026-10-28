module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.Inputs
public import Theory.AlgebraicGroup.Representations.Algebraic.SL2HighestWeight

/-!
# A rank-one orientation obstruction for the requested fundamental weights

`RootWeightEquation` uses inverse conjugation, whereas `IsWeightVector` uses a
left representation. Thus a rank-one morphism taking the standard upper root
into the positive unipotent subgroup takes the standard diagonal to the inverse
of the root cocharacter. Under exactly these two pointwise compatibilities,
the proved SL2 highest-weight endpoint forces each relevant coordinate to be
nonpositive, ruling out the corresponding requested fundamental weight.

The rank-one morphism is explicit: this file does not assert its construction
from `Geometry`, nor an unconditional counterexample to that structure. It
isolates the convention obstruction that must be resolved before using the
usual fundamental-module constructions with the published positive coordinates.

Sources: GLS3, Definitions 1.9.2 and 1.14.5, and Theorems 1.12.1(g), 1.14.6.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- With the inverse-coroot convention, a positive-unipotent-fixed highest
vector has a nonpositive coordinate, by the rational SL2 endpoint theorem. -/
theorem highestWeight_coordinate_nonpos_of_inverseCoroot
    (S : Geometry K) (i : Fin 4)
    (π : Theory.AlgebraicGroup.Morphism (slVariety k 2) K)
    (hupper : ∀ t : k, π.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) ∈
      RootSubgroupGenerated S.roots S.roots.positive)
    (hdiagonal : ∀ t : Variety.Point (KMult k),
      π.onPoints (standardSL2DiagonalMorphism.onPoints t) =
        S.torus.includePoint ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints t⁻¹))
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hr : IsRationalRepresentation ρ)
    (x : V) (a : Weight)
    (hx : HasHighWeight ρ S.bigCell.data.B S.torus x (S.coordinateEmbedding a)) :
    a i ≤ 0 := by
  have hfixed := invariantLine_fixed_of_unipotent_subgroup ρ hr S.bigCell.data.B
    S.bigCell.data.positive_witness.unipotent x hx.1
    S.bigCell.data.positive_witness.radical.1
    S.bigCell.data.positive_witness.radical.2.1
  have hupper_fixed : ∀ t : k,
      (ρ.action (π.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)))).1 x = x := by
    intro t
    apply hfixed
    change π.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) ∈
      S.bigCell.data.positive_witness.unipotent.toSubgroup
    rw [S.bigCell.data.positive_witness.root_generated]
    exact hupper t
  have hdiag : ∀ t : Variety.Point (KMult k),
      (ρ.action (π.onPoints (standardSL2DiagonalMorphism.onPoints t))).1 x =
        (dPointEquiv 1 t 0 : k) ^ (-a i) • x := by
    intro t
    rw [hdiagonal, hx.2.2]
    have hp := S.realized.weightPairing_spec (S.coordinateEmbedding a)
      (S.simpleRoot i).val t⁻¹
    change (S.coordinateEmbedding a).pointCharacter
      ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints t⁻¹) =
        (dPointEquiv 1 t⁻¹ 0 : k) ^
          S.roots.weightPairing (S.weight (Multiplicative.ofAdd a)) (S.simpleRoot i).val at hp
    rw [S.weight_coordinate] at hp
    rw [hp]
    let e : Variety.Point (KMult k) →* (Fin 1 → kˣ) := {
      toFun := dPointEquiv 1
      map_one' := dPointEquiv_one 1
      map_mul' := dPointEquiv_mul 1 }
    have hinv : (dPointEquiv 1 t⁻¹ 0 : k) = (dPointEquiv 1 t 0 : k)⁻¹ := by
      simpa [e] using congrArg (fun f : Fin 1 → kˣ => (f 0 : k)) (e.map_inv t)
    rw [hinv, inv_zpow, zpow_neg]
  have h := standardSL2_highestWeightExponent_nonneg_of_pullback π ρ hr
    x (-a i) hx.1.1 hupper_fixed hdiag
  omega

/-- A single compatible inverse-coroot SL2 rules out the published predicate
requiring all four *positive* fundamental coordinates for the positive Borel. -/
theorem not_fundamentalRationalExistence_of_inverseCoroot
    (S : Geometry K) (i : Fin 4)
    (π : Theory.AlgebraicGroup.Morphism (slVariety k 2) K)
    (hupper : ∀ t : k, π.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) ∈
      RootSubgroupGenerated S.roots S.roots.positive)
    (hdiagonal : ∀ t : Variety.Point (KMult k),
      π.onPoints (standardSL2DiagonalMorphism.onPoints t) =
        S.torus.includePoint ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints t⁻¹)) :
    ¬ FundamentalRationalExistence S := by
  intro h
  obtain ⟨A, x, hx⟩ := h i
  have hnonpos := highestWeight_coordinate_nonpos_of_inverseCoroot S i π hupper hdiagonal
    A.action A.irreducible.1 x (Pi.single i 1) hx
  simp at hnonpos

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
