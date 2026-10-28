module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.FixedDescent.SubfieldLifts.Coordinates
public import Theory.SpecificGroups.Triality.ConcreteBruhat.InputRealization

/-!
# Subfield descent by uniqueness of the split Bruhat form

A coefficient automorphism preserves the two positive factors, the torus,
and the inversion support of a split Bruhat normal form, and fixes its Weyl
representative. Uniqueness of the four factors therefore makes each factor
fixed. The coordinate lifts from `Coordinates` reassemble them into an
actual product of smaller-field Geck-group elements.

Only the larger field needs the binary normal-form theorem. The smaller
carrier needs neither a normal form nor simplicity or perfectness. The
scalar lifting premise is discharged by the literal fixed-field embedding
in the parent `SubfieldLifts` module.

Source: GLS3 2.3.5, 2.3.8 and §§2.2, 2.5–2.6
(`refs/KGroup/GLS3/chapter2.tex`); the field case of Aschbacher–Smith
16.1.4(4), printed p.1171 (`refs/quasithin.pdf`).
-/

public section
noncomputable section
namespace Triality.Standard.EvenField.SubfieldLifts
open Parabolics ConcreteBruhat SplitNormalForm

private def coefficientCoordinates (P : Parameters)
    (e : ExtensionField P ≃+* ExtensionField P) (a : Coordinates P) : Coordinates P where
  left := ⟨RootPairing.SimpleGeckGroup.map e.toRingHom a.left.val,
    map_mem_positive P P e.toRingHom a.left.property⟩
  torus := ⟨RootPairing.SimpleGeckGroup.map e.toRingHom a.torus.val,
    map_mem_torus P P e.toRingHom a.torus.property⟩
  weyl := a.weyl
  right := fun i => e (a.right i)
  supported := by
    intro i hi
    simp only [a.supported i hi, map_zero]

private theorem evaluate_coefficientCoordinates (P : Parameters) (D : Inputs P)
    (e : ExtensionField P ≃+* ExtensionField P) (a : Coordinates P) :
    evaluate D (coefficientCoordinates P e a) =
      RootPairing.SimpleGeckGroup.map e.toRingHom (evaluate D a) := by
  have hw : RootPairing.SimpleGeckGroup.map e.toRingHom (D.lift a.weyl) = D.lift a.weyl :=
    map_weyl_fixed P e (D.weylEquiv.symm a.weyl).property
  simp only [evaluate, coefficientCoordinates, map_mul, hw, map_orderedProduct]
  rfl

/-- Scalar fixed-field lifts extend to the root-generated split D4 group,
using the unique concrete Bruhat form in the larger binary field. -/
theorem split_lift_of_fixed (n : ℕ) (hn : 0 < n) (P : Parameters)
    (f : ExtensionField P →+* ExtensionField (binaryParameters n hn))
    (e : ExtensionField (binaryParameters n hn) ≃+* ExtensionField (binaryParameters n hn))
    (hfield : ∀ t, e t = t → ∃ s, f s = t)
    (x : SplitGroup (binaryParameters n hn))
    (hx : RootPairing.SimpleGeckGroup.map e.toRingHom x = x) :
    ∃ y : SplitGroup P, RootPairing.SimpleGeckGroup.map f y = x := by
  let D := InputRealization.inputs (binaryParameters n hn) rfl
  obtain ⟨a,ha,_⟩ := existsUnique_coordinates n hn D x
  have hfix : coefficientCoordinates (binaryParameters n hn) e a = a :=
    evaluate_injective n hn D
      ((evaluate_coefficientCoordinates _ D e a).trans
        ((congrArg (RootPairing.SimpleGeckGroup.map e.toRingHom) ha).trans (hx.trans ha.symm)))
  have hu : RootPairing.SimpleGeckGroup.map e.toRingHom a.left.val = a.left.val :=
    congrArg (fun c : Coordinates (binaryParameters n hn) => c.left.val) hfix
  have ht : RootPairing.SimpleGeckGroup.map e.toRingHom a.torus.val = a.torus.val :=
    congrArg (fun c : Coordinates (binaryParameters n hn) => c.torus.val) hfix
  have hv : (fun i => e (a.right i)) = a.right := congrArg Coordinates.right hfix
  choose b hb using fun i => hfield (a.right i) (congrFun hv i)
  have hright : PositiveCoordinates.orderedProduct (binaryParameters n hn) a.right ∈
      (RootPairing.SimpleGeckGroup.map f).range := by
    refine ⟨PositiveCoordinates.orderedProduct P b, ?_⟩
    exact (map_orderedProduct _ _ f b).trans
      (congrArg (PositiveCoordinates.orderedProduct _) (funext hb))
  have hweyl : D.lift a.weyl ∈ (RootPairing.SimpleGeckGroup.map f).range :=
    weyl_le_range P (binaryParameters n hn) f (D.weylEquiv.symm a.weyl).property
  change x ∈ (RootPairing.SimpleGeckGroup.map f).range
  rw [← ha, evaluate]
  exact (RootPairing.SimpleGeckGroup.map f).range.mul_mem
    ((RootPairing.SimpleGeckGroup.map f).range.mul_mem
      ((RootPairing.SimpleGeckGroup.map f).range.mul_mem
        (positive_lift n hn P f e hfield a.left hu)
        (torus_lift _ rfl P f e hfield a.torus ht)) hweyl) hright

end Triality.Standard.EvenField.SubfieldLifts
