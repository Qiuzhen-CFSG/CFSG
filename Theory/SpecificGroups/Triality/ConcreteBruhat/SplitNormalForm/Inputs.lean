module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.Basic
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates

/-!
# Inputs and coordinates for the split D4 Bruhat calculation

The Weyl input identifies the subgroup of actual simple Geck words with the
permutation group on the 24 roots. Its conjugation formula uses left
conjugation. Thus the right factor of `u t n(w) v` is supported on positive
roots whose image under `w` is negative, as in GLS3 2.3.5 and 2.3.8(c).

The additional inputs are torus normalization, its root characters, and the
disjoint semidirect product decomposition of the existing Borel. There is no
cell coverage, exchange, separation, or normal-form assertion in these inputs.
They are intended to be discharged by the concrete Weyl and torus calculations.

Source: `refs/KGroup/GLS3/chapter2.tex`, 2.3.4–8 and §2.4.
-/

@[expose] public section
noncomputable section
open scoped Pointwise
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace Triality.Standard.ConcreteBruhat.SplitNormalForm
open Parabolics

/-- All 24 canonical integral curves in the literal split matrix group. -/
def rootCurve (P : Parameters) (r : TypeDRootIndex 4) (t : ExtensionField P) :
    SplitGroup P :=
  ⟨rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2)) r t,
    rootCurveUnit_mem_simpleSubgroup _ _⟩

@[simp] theorem rootCurve_positive (P : Parameters) (i : Fin 12) (t : ExtensionField P) :
    rootCurve P (PositiveCoordinates.rootIndex i) t = PositiveCoordinates.curve P i t := rfl

/-- The actual matrix representative selected by a matrix/root Weyl equivalence. -/
def representative (P : Parameters) (e : splitWeylSubgroup P ≃* rootWeylGroup) :
    rootWeylGroup →* SplitGroup P :=
  (splitWeylSubgroup P).subtype.comp e.symm.toMonoidHom

/-- Precise matrix and torus inputs, without any Bruhat conclusions. -/
structure Inputs (P : Parameters) where
  weylEquiv : splitWeylSubgroup P ≃* rootWeylGroup
  simple : ∀ i, weylEquiv (splitWeylGenerator P i) = rootWeylGenerator i
  conjugate_root : ∀ w r t,
    representative P weylEquiv w * rootCurve P r t *
      (representative P weylEquiv w)⁻¹ = rootCurve P (w.val r) t
  graphField_index : ∀ (w : splitWeylSubgroup P) (r : TypeDRootIndex 4),
    (weylEquiv (splitWeylGraphField P w)).val (typeD4DiagramEquiv.indexEquiv r) =
      typeD4DiagramEquiv.indexEquiv ((weylEquiv w).val r)
  weyl_normalizes_torus : splitWeylSubgroup P ≤ Subgroup.normalizer (splitTorus P)
  torus_normalizes_positive : splitTorus P ≤ Subgroup.normalizer (positiveSubgroup P)
  positive_disjoint_torus : Disjoint (positiveSubgroup P) (splitTorus P)
  rootCharacter : TypeDRootIndex 4 → splitTorus P →* (ExtensionField P)ˣ
  character_simple : ∀ r i t,
    rootCharacter r ⟨torusWord P i t, Subgroup.subset_closure ⟨i, t, rfl⟩⟩ =
      t ^ ((typeDRootPairing 2).pairingIn ℤ r (typeDSimpleRootIndex 2 i))
  torus_conjugate_root : ∀ (h : splitTorus P) r t,
    h.val * rootCurve P r t * h.val⁻¹ =
      rootCurve P r ((rootCharacter r h : ExtensionField P) * t)

namespace Inputs
variable {P : Parameters} (D : Inputs P)

/-- A homomorphic choice of representatives, possible for these binary matrices. -/
def lift : rootWeylGroup →* SplitGroup P := representative P D.weylEquiv

@[simp] theorem lift_simple (i : Fin 4) : D.lift (rootWeylGenerator i) = weylWord P i 1 := by
  change (D.weylEquiv.symm (rootWeylGenerator i)).val = _
  rw [← D.simple i, D.weylEquiv.symm_apply_apply]
  rfl

theorem lift_injective : Function.Injective D.lift := by
  intro v w h
  exact D.weylEquiv.symm.injective (Subtype.ext h)

/-- The transported graph-field action; the input formula identifies its root action. -/
def weylTwist : rootWeylGroup ≃* rootWeylGroup :=
  (D.weylEquiv.symm.trans (splitWeylGraphField P)).trans D.weylEquiv

@[simp] theorem graphField_lift (w : rootWeylGroup) :
    graphFieldAutomorphism P (D.lift w) = D.lift (D.weylTwist w) := by
  change _ = (D.weylEquiv.symm (D.weylEquiv
    (splitWeylGraphField P (D.weylEquiv.symm w)))).val
  rw [D.weylEquiv.symm_apply_apply]
  rfl

theorem weylTwist_apply_diagram (w : rootWeylGroup) (r : TypeDRootIndex 4) :
    (D.weylTwist w).val (typeD4DiagramEquiv.indexEquiv r) =
      typeD4DiagramEquiv.indexEquiv (w.val r) := by
  simpa only [weylTwist, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using
    D.graphField_index (D.weylEquiv.symm w) r

include D in
/-- The allowed torus inputs give the full unique Borel factorization. -/
theorem existsUnique_borel_factors (b : splitBorel P) :
    ∃! a : positiveSubgroup P × splitTorus P, a.1.val * a.2.val = b.val := by
  have hset : (splitBorel P : Set (SplitGroup P)) =
      (positiveSubgroup P : Set (SplitGroup P)) * splitTorus P :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ D.torus_normalizes_positive
  have hb : b.val ∈ (positiveSubgroup P : Set (SplitGroup P)) * splitTorus P := by
    rw [← hset]
    exact b.property
  obtain ⟨u, hu, t, ht, h⟩ := hb
  exact ⟨(⟨u, hu⟩, ⟨t, ht⟩), h, fun a ha =>
    Subgroup.mul_injective_of_disjoint D.positive_disjoint_torus (ha.trans h.symm)⟩

end Inputs

/-- Positive coordinates outside the inversion set must vanish. -/
def Supported (P : Parameters) (w : rootWeylGroup) (a : PositiveCoordinates.Coordinates P) :
    Prop := ∀ i, (typeDRootPairing_base 2).IsPos (w.val (PositiveCoordinates.rootIndex i)) → a i = 0

/-- The four factors, with the right factor in the existing twelve-root order. -/
@[ext] structure Coordinates (P : Parameters) where
  left : positiveSubgroup P
  torus : splitTorus P
  weyl : rootWeylGroup
  right : PositiveCoordinates.Coordinates P
  supported : Supported P weyl right

/-- Evaluate a proposed normal form in the original split matrix group. -/
def evaluate {P : Parameters} (D : Inputs P) (a : Coordinates P) : SplitGroup P :=
  a.left.val * a.torus.val * D.lift a.weyl * PositiveCoordinates.orderedProduct P a.right

/-- The split double coset indexed by an actual root permutation. -/
def cell {P : Parameters} (D : Inputs P) (w : rootWeylGroup) : Set (SplitGroup P) :=
  {g | ∃ b₁ ∈ splitBorel P, ∃ b₂ ∈ splitBorel P, g = b₁ * D.lift w * b₂}

/-- The Weyl subgroup attached to one of the original diagram-orbit parabolics. -/
def parabolicWeyl (a : Node) : Subgroup rootWeylGroup :=
  Subgroup.closure {w | ∃ i ∈ a.support, w = rootWeylGenerator i}

end Triality.Standard.ConcreteBruhat.SplitNormalForm
