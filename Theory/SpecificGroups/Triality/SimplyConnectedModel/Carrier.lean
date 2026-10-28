module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalSpinModel
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalSpinSemisimplicity
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenSpinActionCharacteristicTwo
public import Theory.AlgebraicGroup.RootSystems.HyperbolicStandardSplitForm

/-!
# The concrete Clifford carrier for the D4 setup

We use the exact closed left-regular Clifford Spin group of four hyperbolic
planes. Its point group is identified with Mathlib's generated Spin group.
The regular Spin cover maps it onto the commutator subgroup of the full
quadratic-isometry group. Existing geometric results prove semisimplicity;
an explicit nonidentity upper-root element in the image proves nontriviality.
In characteristic two, the scalar-kernel calculation makes this cover an
isomorphism of point groups.

This fixes the carrier and natural action for the D4 graph-field construction.
The pinned torus, the simple and simply connected root datum, and the regular
diagram and Frobenius maps require further geometry. In particular, the
point-group isomorphism `omegaPointEquiv` supplies no algebraic inverse and
cannot transport torus characters from the orthogonal image.

Sources: GLS3, §§1.10–1.12 and 2.2 (`refs/KGroup/GLS3/Chapter1.tex` and
`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section

namespace Triality.SimplyConnected
open Theory.AlgebraicGroup

universe u
variable (k : Type u) [Field k] [IsAlgClosed k]

/-- Four hyperbolic planes, with their standard coordinates. -/
abbrev QuadraticSpace := HyperbolicSpace k 4

/-- The nonsingular form given by the sum of four hyperbolic products. -/
abbrev quadraticForm : QuadraticForm k (QuadraticSpace k) :=
  hyperbolicForm 4

/-- The concrete split Clifford Spin model in dimension eight. -/
def cliffordModel : EvenOrthogonalSpinModel (quadraticForm k) :=
  splitEvenOrthogonalSpinModel (standardHyperbolicSplit 4) (by simp)

/-- The exact closed left-regular Spin carrier. -/
abbrev groupVariety : Variety k :=
  (cliffordModel k).spin.carrierVariety

instance groupVarietyAlgebraicGroup : AlgebraicGroup (groupVariety k) :=
  (cliffordModel k).spin.carrierAlgebraicGroup

/-- Identification with the generated Clifford Spin group. -/
def pointEquiv : Variety.Point (groupVariety k) ≃* spinGroup (quadraticForm k) :=
  (cliffordModel k).spinPoints

/-- Points of the algebraic Spin carrier. -/
abbrev Points := Variety.Point (groupVariety k)

/-- Semisimplicity of the concrete algebraic carrier. -/
theorem isSemisimple : IsSemisimpleAlgebraicGroup (groupVariety k) := by
  have h := splitEvenOrthogonalSpinCarrier_isSemisimple
    (standardHyperbolicSplit (k := k) 4) (by simp)
  rw [splitEvenOrthogonalSpinCarrier_spin] at h
  exact h

/-- Connectedness of the concrete algebraic carrier. -/
theorem isConnected : _root_.IsConnected (Set.univ : Set (Points k)) :=
  (isSemisimple k).1

/-- The commutator of the full quadratic-isometry point group. -/
abbrev OmegaPoints := commutator (quadraticIsometrySubgroup (quadraticForm k))

/-- The point map of the regular Spin cover, in quadratic-isometry coordinates. -/
def toOmega : Points k →* OmegaPoints k :=
  (cliffordModel k).omegaPoints.toMonoidHom.comp (cliffordModel k).spinCover.onPoints

/-- The regular Spin cover reaches the entire orthogonal commutator group. -/
theorem toOmega_surjective : Function.Surjective (toOmega k) :=
  (cliffordModel k).omegaPoints.surjective.comp (cliffordModel k).spinCoverIsogeny.1

/-- The cover agrees with the Clifford natural action. -/
theorem toOmega_val (x : Points k) :
    (toOmega k x).1 = (cliffordModel k).spinAction (pointEquiv k x) := by
  have h := (cliffordModel k).spinCover_points (pointEquiv k x)
  simpa only [pointEquiv, toOmega, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using h

/-- The natural action on the eight-dimensional quadratic space. -/
def naturalAction : Points k →* quadraticIsometrySubgroup (quadraticForm k) :=
  (commutator (quadraticIsometrySubgroup (quadraticForm k))).subtype.comp (toOmega k)

/-- The natural action is Clifford conjugation. -/
theorem naturalAction_clifford (x : Points k) (v : QuadraticSpace k) :
    CliffordAlgebra.ι (quadraticForm k) ((naturalAction k x).1 v) =
      (pointEquiv k x : CliffordAlgebra (quadraticForm k)) *
        CliffordAlgebra.ι (quadraticForm k) v *
          (↑((spinGroup.toUnits (pointEquiv k x))⁻¹) :
            CliffordAlgebra (quadraticForm k)) := by
  change CliffordAlgebra.ι (quadraticForm k) ((toOmega k x).1.1 v) = _
  rw [toOmega_val]
  exact (cliffordModel k).spinAction_clifford (pointEquiv k x) v

/-- An upper-root element in the cover image witnesses nontriviality. -/
instance pointsNontrivial : Nontrivial (Points k) := by
  classical
  let z := hyperbolicUpperRootPoint (k := k) 4 0 1 (by decide) 1
  obtain ⟨g, h, hcomm⟩ :=
    hyperbolicUpperRootPoint_is_commutator (k := k) 4 0 1 (by decide) 1
  have hzmem : z ∈ commutator (quadraticIsometrySubgroup (quadraticForm k)) := by
    rw [show z = _ from hcomm]
    rw [commutator_eq_closure]
    exact Subgroup.subset_closure (commutator_mem_commutatorSet g h)
  have hzne : z ≠ 1 := by
    intro hz
    have he := congrArg
      (fun f : quadraticIsometrySubgroup (quadraticForm k) =>
        (f.1 (Pi.single 1 1, 0)).1 0) hz
    simp [z, hyperbolicUpperRootPoint, hyperbolicUpperRoot,
      hyperbolicUpperRootLinearEquiv] at he
  obtain ⟨x, hx⟩ := toOmega_surjective k ⟨z, hzmem⟩
  refine ⟨⟨x, 1, ?_⟩⟩
  intro hx1
  have he := congrArg Subtype.val hx
  rw [hx1, map_one] at he
  exact hzne he.symm

section CharacteristicTwo
variable [CharP k 2]

/-- In characteristic two the regular cover is injective on points. -/
theorem toOmega_injective : Function.Injective (toOmega k) := by
  intro x y h
  apply (pointEquiv k).injective
  apply cliffordSpinActionOfSplit_injective_charTwo (standardHyperbolicSplit 4)
  change (cliffordModel k).spinAction (pointEquiv k x) =
    (cliffordModel k).spinAction (pointEquiv k y)
  rw [← toOmega_val, ← toOmega_val, h]

/-- The Spin-to-Omega point-group isomorphism in characteristic two.
This is not an algebraic-group isomorphism. -/
def omegaPointEquiv : Points k ≃* OmegaPoints k :=
  MulEquiv.ofBijective (toOmega k) ⟨toOmega_injective k, toOmega_surjective k⟩

@[simp] theorem omegaPointEquiv_apply (x : Points k) :
    omegaPointEquiv k x = toOmega k x := rfl

/-- The natural representation is faithful on points in characteristic two. -/
theorem naturalAction_injective : Function.Injective (naturalAction k) := by
  intro x y h
  apply toOmega_injective k
  exact Subtype.ext h

end CharacteristicTwo

end Triality.SimplyConnected
