module
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.OrbitCriterion

/-!
# Binary-vector orbit certificate interface

The unit group of the ATLAS matrix algebra acts on column vectors by ordinary
matrix multiplication. An orbit certificate records distinct vectors, exact
matrix transition identities, and reachability in the generated subgroup.
The independent counting criterion turns these checks into a divisor.

Column-vector multiplication is explicit in every computational obligation;
ATLAS row-action data must be converted before use here.
-/

@[expose] public section
namespace BabyMonster.OrderLowerBound.FivePart

/-- Column vectors for the fixed binary representation. -/
abbrev Vector := Fin 4370 → ZMod 2

/-- The usual matrix action, installed locally when using orbit–stabilizer. -/
@[instance_reducible] def vectorAction : MulAction MatrixGroup Vector where
  smul g v := (g : AtlasMatrix).mulVec v
  one_smul v := Matrix.one_mulVec v
  mul_smul g h v := (Matrix.mulVec_mulVec v (g : AtlasMatrix) (h : AtlasMatrix)).symm

/-- Candidate data only; no mathematical validity is asserted by these fields. -/
structure MatrixOrbitData (J : Type*) where
  size : ℕ
  point : Fin size → Vector
  base : Fin size
  perm : J → Equiv.Perm (Fin size)

/-- The exact proof obligations for a complete matrix orbit. -/
structure MatrixOrbitCertificate {J : Type*} (g : J → MatrixGroup)
    (d : MatrixOrbitData J) : Prop where
  distinct : Function.Injective d.point
  step : ∀ j i, (g j : AtlasMatrix).mulVec (d.point i) = d.point (d.perm j i)
  reachable : ∀ i, ∃ w : Subgroup.closure (Set.range g),
    ((w : MatrixGroup) : AtlasMatrix).mulVec (d.point d.base) = d.point i

/-- A certified orbit size divides the order of the subgroup of actual matrices. -/
theorem MatrixOrbitCertificate.card_dvd {J : Type*} {g : J → MatrixGroup}
    {d : MatrixOrbitData J} (h : MatrixOrbitCertificate g d) :
    d.size ∣ Nat.card (Subgroup.closure (Set.range g)) := by
  let _ := vectorAction
  apply enumeratedOrbit_card_dvd g d.point d.base h.distinct d.perm
  · exact h.step
  · exact h.reachable

/-- An explicit decreasing spanning tree discharges all reachability obligations. -/
theorem matrixOrbitCertificate_of_tree {J : Type*} (g : J → MatrixGroup)
    (d : MatrixOrbitData J) (hdistinct : Function.Injective d.point)
    (hstep : ∀ j i, (g j : AtlasMatrix).mulVec (d.point i) = d.point (d.perm j i))
    (parent : Fin d.size → Fin d.size) (edge : Fin d.size → J)
    (hlt : ∀ i, i ≠ d.base → (parent i).val < i.val)
    (hedge : ∀ i, i ≠ d.base → d.perm (edge i) (parent i) = i) :
    MatrixOrbitCertificate g d := by
  let _ := vectorAction
  exact ⟨hdistinct, hstep,
    reachable_of_tree g d.point d.base d.perm hstep parent edge hlt hedge⟩

end BabyMonster.OrderLowerBound.FivePart
