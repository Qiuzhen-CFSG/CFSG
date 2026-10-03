module

public import Stellmacher.Recognition.SuzukiThreeRootNoncommuting
public import Theory.SpecificGroups.UnitaryThree.PermutationModel

/-!
# Coordinate data for Suzuki's degree-28 action

A root-group isomorphism gives a bijection from the action domain to the
Hermitian coordinate set. Root translations already match under this bijection.
An equivariant torus isomorphism adds Borel coordinates; full coordinates also
specify a swapping element acting by reciprocal coordinates. These structures
record explicit equations to prove, without assuming their existence.

This shared boundary lets the algebraic coordinate proofs and matrix realization
feed the final assembly without cyclic imports.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Sections IV–VI.
-/

public section

open MulAction
namespace Stellmacher.Recognition
namespace SuzukiThreeHypotheses
variable {G Ω : Type*} [Group G] [MulAction G Ω]
  {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
  (h : SuzukiThreeHypotheses G Ω a Q)

/-- Hermitian coordinates induced by a root-group isomorphism. -/
noncomputable def pointCoordinates (b : Ω) (hb : b ≠ a)
    (e : Q ≃* UnitaryThree.Root) : Ω ≃ UnitaryThree.Point :=
  (h.rootPointEquiv b hb).symm.trans (Equiv.optionCongr e.toEquiv)

@[simp] theorem pointCoordinates_base (b : Ω) (hb : b ≠ a)
    (e : Q ≃* UnitaryThree.Root) : h.pointCoordinates b hb e a = none := by
  change (Equiv.optionCongr e.toEquiv) ((h.rootPointEquiv b hb).symm a) = none
  rw [(h.rootPointEquiv b hb).symm_apply_eq.mpr (h.rootPointEquiv_none b hb).symm]
  rfl

@[simp] theorem pointCoordinates_root (b : Ω) (hb : b ≠ a)
    (e : Q ≃* UnitaryThree.Root) (q : Q) :
    h.pointCoordinates b hb e (((q : stabilizer G a) : G) • b) = some (e q) := by
  change (Equiv.optionCongr e.toEquiv)
    ((h.rootPointEquiv b hb).symm (((q : stabilizer G a) : G) • b)) = some (e q)
  rw [(h.rootPointEquiv b hb).symm_apply_eq.mpr (h.rootPointEquiv_some b hb q).symm]
  rfl

@[simp] theorem pointCoordinates_other (b : Ω) (hb : b ≠ a)
    (e : Q ≃* UnitaryThree.Root) : h.pointCoordinates b hb e b = some 1 := by
  simpa using h.pointCoordinates_root b hb e 1

theorem pointCoordinates_root_smul (b : Ω) (hb : b ≠ a)
    (e : Q ≃* UnitaryThree.Root) (q : Q) (x : Ω) :
    h.pointCoordinates b hb e (((q : stabilizer G a) : G) • x) =
      UnitaryThree.rootPerm (e q) (h.pointCoordinates b hb e x) := by
  obtain ⟨p, rfl⟩ := (h.rootPointEquiv b hb).surjective x
  cases p with
  | none =>
    simp only [rootPointEquiv_none, mem_stabilizer_iff.mp q.val.property,
      pointCoordinates_base]
    rfl
  | some p =>
    rw [rootPointEquiv_some, ← mul_smul]
    change h.pointCoordinates b hb e (((q * p : Q) : G) • b) = _
    rw [pointCoordinates_root, pointCoordinates_root]
    change some (e (q * p)) = some (e q * e p)
    rw [map_mul]

end SuzukiThreeHypotheses

/-- Root and torus coordinates, before solving the swapping-map equation. -/
structure SuzukiThreeBorelCoordinates
    {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q) (b : Ω) (hb : b ≠ a) where
  rootEquiv : Q ≃* UnitaryThree.Root
  torusEquiv : stabilizer (stabilizer G a) b ≃* FiniteField.Nineˣ
  torus_smul : ∀ (k : stabilizer (stabilizer G a) b) (x : Ω),
    h.pointCoordinates b hb rootEquiv (((k : stabilizer G a) : G) • x) =
      UnitaryThree.torusPerm (torusEquiv k) (h.pointCoordinates b hb rootEquiv x)

/-- Construct Borel coordinates from an equivariant root-group isomorphism. -/
noncomputable def SuzukiThreeBorelCoordinates.ofRootTorusEquiv
    {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q) (b : Ω) (hb : b ≠ a)
    (e : Q ≃* UnitaryThree.Root)
    (kappa : stabilizer (stabilizer G a) b ≃* FiniteField.Nineˣ)
    (he : ∀ (k : stabilizer (stabilizer G a) b) (q : Q),
      e (SuzukiThreeHypotheses.torusRootAut (Q := Q) b k q) =
        UnitaryThree.scale (kappa k) (e q)) : SuzukiThreeBorelCoordinates h b hb where
  rootEquiv := e
  torusEquiv := kappa
  torus_smul k x := by
    obtain ⟨p, rfl⟩ := (h.rootPointEquiv b hb).surjective x
    change e.toEquiv.optionCongr
      ((h.rootPointEquiv b hb).symm
        (((k : stabilizer G a) : G) • h.rootPointEquiv b hb p)) =
      UnitaryThree.torusPerm (kappa k)
        (e.toEquiv.optionCongr ((h.rootPointEquiv b hb).symm (h.rootPointEquiv b hb p)))
    rw [← h.rootCoordinateAction_apply, h.rootCoordinateAction_torus,
      Equiv.symm_apply_apply]
    cases p with
    | none => rfl
    | some q =>
      change some (e (SuzukiThreeHypotheses.torusRootAut (Q := Q) b k q)) =
        some (UnitaryThree.scale (kappa k) (e q))
      rw [he]

/-- Full coordinates include the action of an element interchanging zero and infinity. -/
structure SuzukiThreeCoordinates
    {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q) (b : Ω) (hb : b ≠ a)
    extends SuzukiThreeBorelCoordinates h b hb where
  swap : G
  swap_smul : ∀ x : Ω,
    h.pointCoordinates b hb rootEquiv (swap • x) =
      UnitaryThree.swapPerm (h.pointCoordinates b hb rootEquiv x)

end Stellmacher.Recognition
end
