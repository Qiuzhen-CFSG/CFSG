module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Source

/-!
# Common coordinates for the local construction in B.4.9(1)

The quotient is placed in its natural matrix model by an explicit change
of basis. In the dual case the actor marking is the corresponding conjugate
of inverse transpose of the original natural marking. The
coordinate hyperplane, complementary defining-field line, full axis group,
and special-linear Levi subgroup are then actual subspaces and subgroups.
These definitions are shared by the independent generation, fixed-lift, and
larger-field complement arguments; existence is not postulated.

Source: Aschbacher–Smith B.4.9(1), printed pp.92–94, combined manuscript
of 1 March 2004.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}

/-- A natural coordinate model of the actual quotient. Its marking is the
original marking or its inverse transpose, conjugated by one recorded matrix
to place the given axis in a coordinate hyperplane. -/
structure QuotientCoordinates (d : DoubleNatural F n ρ) where
  action : ActionEquiv d.space.quotientRepresentation (linearNatural F n)
  basisChange : Matrix.SpecialLinearGroup (Fin n) F.Carrier
  marking : (∀ g, action.groupEquiv g =
      basisChange * d.natural.groupEquiv g * basisChange⁻¹) ∨
    (∀ g, action.groupEquiv g =
      basisChange * Matrix.SpecialLinearGroup.transpose ((d.natural.groupEquiv g)⁻¹) *
        basisChange⁻¹)

namespace QuotientCoordinates
variable {d : DoubleNatural F n ρ} (m : QuotientCoordinates d) (j : Fin n)

/-- The actual preimage of the coordinate F-hyperplane x_j = 0. -/
def axis : Submodule (ZMod 2) (V ⧸ d.space.toSubmodule) :=
  let ev : (Fin n → F.Carrier) →ₗ[ZMod 2] F.Carrier :=
    (LinearMap.proj j : (Fin n → F.Carrier) →ₗ[F.Carrier] F.Carrier).restrictScalars (ZMod 2)
  LinearMap.ker (ev.comp m.action.linearEquiv.toLinearMap)

/-- The actual preimage of the complementary coordinate F-line. -/
def line : Submodule (ZMod 2) (V ⧸ d.space.toSubmodule) :=
  let L : Submodule F.Carrier (Fin n → F.Carrier) :=
    Submodule.span F.Carrier {Pi.single j 1}
  (L.restrictScalars (ZMod 2)).comap m.action.linearEquiv.toLinearMap

/-- Q, the entire pointwise centralizer of the coordinate quotient axis. -/
noncomputable def Q : Subgroup G := axisGroup d (m.axis j)

/-- K, fixing the quotient line pointwise and preserving its complementary
axis. In the marked SL model this is the literal SL_(n-1) block subgroup. -/
noncomputable def K : Subgroup G :=
  subspaceStabilizer d.space.quotientRepresentation (m.axis j) ⊓
    subspaceKernel d.space.quotientRepresentation (m.line j) ⊤

/-- The precise fixed-lift assertion used by the complement construction.
It concerns only lifting the quotient line into C_V(K), not splitting V. -/
def FixedLifts : Prop :=
  m.line j ≤ (fixedSpace ρ (m.K j)).map d.space.toSubmodule.mkQ

/-- The unit vector on the quotient line, in the original quotient space. -/
def lineVector : V ⧸ d.space.toSubmodule :=
  m.action.linearEquiv.symm (Pi.single j (1 : F.Carrier))

/-- A fixed lift of the canonical quotient line vector. This is the literal
application of `FixedLifts` used by the binary displacement construction. -/
theorem exists_fixed_lineVector (hf : m.FixedLifts j) :
    ∃ v : V, v ∈ fixedSpace ρ (m.K j) ∧ d.space.toSubmodule.mkQ v = m.lineVector j := by
  have hm : m.lineVector j ∈ m.line j := by
    unfold line lineVector
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact Submodule.subset_span (Set.mem_singleton _)
  exact hf hm

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
