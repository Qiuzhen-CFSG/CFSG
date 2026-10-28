module

public import Theory.AlgebraicGroup.RootSystems.TypeE6PinnedDiagram
public import Theory.SpecificGroups.LieType.TwistedE6Field
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The concrete ambient graph–field involution for twisted E6

On the integral Chevalley coordinates, compose the specified E6 diagram
permutation with the `q`-power automorphism of the field of order `q²`.
The two actions commute, so their composite is an involution. The entrywise
fixed-point equations are recorded for use in the root-generated construction.

The ambient fixed subgroup here is a subgroup of the full matrix-unit group;
it is not the finite simple group. The E6 root-generated subgroup must still
be imposed before taking the characteristic-prime-generated subgroup and its
central quotient. See GLS3, §§2.1–2.3 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

namespace TwistedE6

open Theory.AlgebraicGroup.StandardRootSystem

variable (p : ℕ) [Fact p.Prime] (m : ℕ)

/-- Invertible matrices on the concrete E6 Chevalley coordinates. -/
abbrev AmbientGroup :=
  (Matrix typeE6PinnedIndex typeE6PinnedIndex (CoefficientField p m))ˣ

/-- Entrywise `q`-power Frobenius on the ambient matrix-unit group. -/
noncomputable def ambientFieldTwist : AmbientGroup p m ≃* AmbientGroup p m :=
  Units.mapEquiv (fieldTwist p m).mapMatrix.toMulEquiv

@[simp] theorem ambientFieldTwist_apply (g : AmbientGroup p m)
    (i j : typeE6PinnedIndex) :
    (ambientFieldTwist p m g : Matrix _ _ (CoefficientField p m)) i j =
      fieldTwist p m ((g : Matrix _ _ (CoefficientField p m)) i j) := rfl

@[simp] theorem ambientFieldTwist_twice (g : AmbientGroup p m) :
    ambientFieldTwist p m (ambientFieldTwist p m g) = g := by
  apply Units.ext
  ext i j
  simp only [ambientFieldTwist_apply, fieldTwist_twice]

/-- The concrete diagram permutation commutes with coefficient Frobenius. -/
theorem ambientDiagram_field_commute (g : AmbientGroup p m) :
    typeE6PinnedUnitsEquiv (CoefficientField p m) (ambientFieldTwist p m g) =
      ambientFieldTwist p m (typeE6PinnedUnitsEquiv (CoefficientField p m) g) := by
  apply Units.ext
  ext i j
  simp only [typeE6PinnedUnitsEquiv_apply, ambientFieldTwist_apply]

/-- The specified graph–field twist, with no chosen or assumed graph action. -/
noncomputable def ambientGraphFieldTwist : AmbientGroup p m ≃* AmbientGroup p m :=
  (ambientFieldTwist p m).trans (typeE6PinnedUnitsEquiv (CoefficientField p m))

@[simp] theorem ambientGraphFieldTwist_apply (g : AmbientGroup p m)
    (i j : typeE6PinnedIndex) :
    (ambientGraphFieldTwist p m g : Matrix _ _ (CoefficientField p m)) i j =
      fieldTwist p m ((g : Matrix _ _ (CoefficientField p m))
        (typeE6PinnedIndexEquiv i) (typeE6PinnedIndexEquiv j)) := by
  change (typeE6PinnedUnitsEquiv (CoefficientField p m) (ambientFieldTwist p m g) :
    Matrix _ _ (CoefficientField p m)) i j = _
  rw [typeE6PinnedUnitsEquiv_apply, ambientFieldTwist_apply]

@[simp] theorem ambientGraphFieldTwist_twice (g : AmbientGroup p m) :
    ambientGraphFieldTwist p m (ambientGraphFieldTwist p m g) = g := by
  apply Units.ext
  ext i j
  simp only [ambientGraphFieldTwist_apply, typeE6PinnedIndexEquiv_twice,
    fieldTwist_twice]

/-- The ambient fixed-point equations, expressed directly in matrix entries. -/
theorem ambientGraphFieldTwist_eq_self_iff (g : AmbientGroup p m) :
    ambientGraphFieldTwist p m g = g ↔
      ∀ i j : typeE6PinnedIndex,
        fieldTwist p m ((g : Matrix _ _ (CoefficientField p m))
          (typeE6PinnedIndexEquiv i) (typeE6PinnedIndexEquiv j)) =
            (g : Matrix _ _ (CoefficientField p m)) i j := by
  constructor
  · intro h i j
    simpa only [ambientGraphFieldTwist_apply] using
      congrArg (fun u : AmbientGroup p m => (u : Matrix _ _ (CoefficientField p m)) i j) h
  · intro h
    apply Units.ext
    ext i j
    simpa only [ambientGraphFieldTwist_apply] using h i j

/-- Ambient fixed points, before imposing membership in the E6 group. -/
noncomputable def ambientFixedSubgroup : Subgroup (AmbientGroup p m) :=
  (ambientGraphFieldTwist p m).toMonoidHom.eqLocus (MonoidHom.id _)

@[simp] theorem mem_ambientFixedSubgroup (g : AmbientGroup p m) :
    g ∈ ambientFixedSubgroup p m ↔ ambientGraphFieldTwist p m g = g := Iff.rfl

instance : Finite (AmbientGroup p m) := by
  unfold AmbientGroup
  infer_instance

instance : Finite (ambientFixedSubgroup p m) := inferInstance

end TwistedE6
