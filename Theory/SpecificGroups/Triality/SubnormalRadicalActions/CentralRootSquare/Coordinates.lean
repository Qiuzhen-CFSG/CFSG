module

public import Theory.SpecificGroups.Triality.RadicalCoordinates
public import Mathlib.Algebra.Module.LinearMap.Prod

/-!
# The marked first root layer of the central triality radical

The published positive-root normal form identifies the central radical with
three cubic-field and two fixed-field parameters. The first layer records
the first two cubic parameters, in short-root orbits (0,1,2) and (4,5,6).
The coordinates retain elementary restriction and the genuine central
quotient. Surjectivity here is a set-theoretic fact; additivity and the full
parabolic action require separate root computations.

Source: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`), for the
central local group of Aschbacher–Smith F.1.12(I)(4), printed p.263
(`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section

open Subgroup
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.LeviCommutators

namespace Triality.Standard.Parabolics.CentralRootSquare

/-- Faithful root coordinates on the actual central radical. -/
def coordinates (P : Parameters) (hp : P.prime = 2) :
    RootOrbitParameters P .central ≃ radical P .central :=
  (rootOrbitEquiv P .central).trans
    ((fixedRootEquiv P hp .central).trans
      ((descendedRootEquiv P hp .central).toEquiv.trans
        (MulEquiv.subgroupCongr
          (radical_eq_descendedRootSubgroup P hp .central).symm).toEquiv))

theorem coordinates_val (P : Parameters) (hp : P.prime = 2)
    (v : RootOrbitParameters P .central) :
    (coordinates P hp v).val = toCarrier P (rootElement P hp .central v) := rfl

/-- The first two short-root coordinates, over the genuine cubic field. -/
def firstLayer (P : Parameters) (hp : P.prime = 2)
    (r : radical P .central) : ExtensionField P × ExtensionField P :=
  let v := (coordinates P hp).symm r
  (v.1 0, v.1 1)

theorem firstLayer_coordinates (P : Parameters) (hp : P.prime = 2)
    (v : RootOrbitParameters P .central) :
    firstLayer P hp (coordinates P hp v) = (v.1 0, v.1 1) := by
  simp [firstLayer]

theorem firstLayer_surjective (P : Parameters) (hp : P.prime = 2) :
    Function.Surjective (firstLayer P hp) := by
  intro v
  exact ⟨coordinates P hp (![v.1, v.2, 0], 0), firstLayer_coordinates P hp _⟩

theorem firstLayer_one (P : Parameters) (hp : P.prime = 2) :
    firstLayer P hp 1 = 0 := by
  have hz : coordinates P hp (0, 0) = 1 := by
    apply Subtype.ext
    rw [coordinates_val, rootElement_factorization]
    simp [extendOrbit]
  rw [← hz, firstLayer_coordinates]
  rfl

/-- Actual parabolic conjugation on the central radical. -/
def conjugation (P : Parameters) :
    parabolic P .central →* MulAut (radical P .central) :=
  (radical P .central).normalizerMonoidHom.comp
    (Subgroup.inclusion
      ((normal_subgroupOf_iff_le_normalizer (radical_le_parabolic P .central)).mp
        (radical_normal P .central)))

theorem conjugation_val (P : Parameters) (g : parabolic P .central)
    (r : radical P .central) :
    (conjugation P g r).val = g.val * r.val * g.val⁻¹ := rfl

end Triality.Standard.Parabolics.CentralRootSquare

end
