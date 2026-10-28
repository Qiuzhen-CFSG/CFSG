module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.DoubleNatural
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces

/-!
# The quadratic-four hypothesis of B.4.9(1)

An axis is the literal common fixed space on the quotient by the original
natural submodule. Its binary codimension is the degree of the defining field.
Root groups are conjugates of the actual elementary matrix groups, under the
same actor marking as the natural submodule. Thus both quotient orientations
are covered without changing either the actor or the original submodule.

The definitions below only state source hypotheses and identify the full
pointwise axis centralizer. They assert no splitting or generation theorem.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9(1),
printed pp.92–94.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}

/-- The source range includes every binary dimension at least four. -/
def SourceFamily (F : BinaryField) (n : ℕ) : Prop :=
  n = 3 ∨ (F.degree = 1 ∧ 4 ≤ n)

/-- A four-group whose three nonidentity elements have one fixed axis on the
actual quotient. The natural-or-dual quotient in `d` identifies this fixed
space with a defining-field hyperplane. -/
def IsAxisFour (d : DoubleNatural F n ρ) (E : Subgroup G) : Prop :=
  IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧
    ∃ I : Submodule (ZMod 2) (V ⧸ d.space.toSubmodule),
      Module.finrank (ZMod 2) ((V ⧸ d.space.toSubmodule) ⧸ I) = F.degree ∧
      ∀ e ∈ E, e ≠ 1 → fixedSpace d.space.quotientRepresentation (Subgroup.zpowers e) = I

/-- Containment in an actual root group of the marked special linear group. -/
def InRootGroup (d : DoubleNatural F n ρ) (E : Subgroup G) : Prop :=
  ∃ s : Matrix.SpecialLinearGroup (Fin n) F.Carrier,
    ∃ i j : Fin n, ∃ hij : i ≠ j, ∀ e ∈ E, ∃ c : F.Carrier,
      d.natural.groupEquiv e =
        s * Matrix.SpecialLinearGroup.transvection hij c * s⁻¹

/-- All hypotheses of B.4.9(1), including the extra universal clause over F₄. -/
structure SourceHypotheses (d : DoubleNatural F n ρ) : Prop where
  family : SourceFamily F n
  four : ∃ E : Subgroup G, IsAxisFour d E ∧ IsQuadratic ρ E ∧
    (n = 3 → ¬ InRootGroup d E)
  fourField : F.degree = 2 → ∀ E : Subgroup G,
    IsAxisFour d E → ¬ InRootGroup d E → IsQuadratic ρ E

/-- The full group fixing the specified quotient axis pointwise. -/
noncomputable def axisGroup (d : DoubleNatural F n ρ)
    (I : Submodule (ZMod 2) (V ⧸ d.space.toSubmodule)) : Subgroup G :=
  subspaceKernel d.space.quotientRepresentation I ⊤

/-- The four-subgroups allowed in the source generation argument. For F₄,
all axis four-groups outside root groups are available. Otherwise the
argument uses conjugates of the original quadratic four-group. -/
def AvailableFour (d : DoubleNatural F n ρ) (E A : Subgroup G) : Prop :=
  (∃ g : G, A = E.map (MulAut.conj g).toMonoidHom) ∨
    (F.degree = 2 ∧ IsAxisFour d A ∧ ¬ InRootGroup d A)

/-- The precise group-geometric generation assertion used to propagate
quadraticity. It is an intermediate obligation, not a source hypothesis. -/
def AxisGeneration (d : DoubleNatural F n ρ) (E Q : Subgroup G) : Prop :=
  ∀ e ∈ Q, e ≠ 1 → Q ≤ ⨆ (A : Subgroup G) (_ : e ∈ A ∧ AvailableFour d E A), A

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
