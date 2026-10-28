module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.Geometry
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.Reduction

/-!
# Split coordinates for the binary octad lattice

The congruences in the eight coordinates give a triangular integral basis. For parameters
`a₀, …, a₇`, its coordinates are `2a₀`, `2a₀ + 4aᵢ` for `1 ≤ i ≤ 6`, and
`2a₀ + 8a₇ - 4(a₁ + ⋯ + a₆)`. Conversely, the first coordinate divided by two,
the six differences divided by four, and the sum of all seven differences divided by eight
recover these parameters. Thus this is a basis of the actual supported Leech
sublattice, including both of its residue classes modulo four.

The squared norm is 32 times `normPolynomial`. Reducing the integral parameters
modulo two has kernel exactly twice the lattice. An explicit change of basis
puts the resulting polynomial into four hyperbolic pairs and supplies the full
`Coordinates.norm` identity for every lattice vector. The construction requires
no assumptions about the group image or faithfulness.

Source: Aschbacher, *Sporadic Groups* (1994), 25.4–25.5(4)–(6), pp.133–134.
-/

@[expose] public noncomputable section
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization.OmegaImage.LatticeModel
namespace BinaryCoordinates

def octadIndex : Fin 8 ≃ Coordinate := (Fintype.equivFinOfCardEq coordinate_card).symm

def basisVector (a : Fin 8 → ℤ) : Fin 8 → ℤ :=
  ![2 * a 0, 2 * a 0 + 4 * a 1, 2 * a 0 + 4 * a 2, 2 * a 0 + 4 * a 3,
    2 * a 0 + 4 * a 4, 2 * a 0 + 4 * a 5, 2 * a 0 + 4 * a 6,
    2 * a 0 + 8 * a 7 - 4 * (a 1 + a 2 + a 3 + a 4 + a 5 + a 6)]

def basisMap : (Fin 8 → ℤ) →ₗ[ℤ] coordinateModel where
  toFun a := ⟨fun i => basisVector a (octadIndex.symm i), by
    apply (mem_coordinateModel _).mpr
    constructor
    · have h (i : Fin 8) : basisVector a i % 4 = (2 * a 0) % 4 := by
        fin_cases i <;> simp [basisVector]; omega
      have hz : (2 * a 0) % 4 = 0 ∨ (2 * a 0) % 4 = 2 := by omega
      exact hz.imp (fun hz i => (h _).trans hz) (fun hz i => (h _).trans hz)
    · rw [octadIndex.symm.sum_comp]
      simp [basisVector, Fin.sum_univ_succ]
      omega⟩
  map_add' a b := by
    apply Subtype.ext
    funext i
    change basisVector (a + b) (octadIndex.symm i) =
      basisVector a (octadIndex.symm i) + basisVector b (octadIndex.symm i)
    generalize octadIndex.symm i = j
    fin_cases j <;> simp [basisVector] <;> ring
  map_smul' n a := by
    apply Subtype.ext
    funext i
    change basisVector (n • a) (octadIndex.symm i) = n * basisVector a (octadIndex.symm i)
    generalize octadIndex.symm i = j
    fin_cases j <;> simp [basisVector] <;> ring

theorem basisMap_injective : Function.Injective basisMap := by
  intro a b h
  have he (i : Fin 8) : basisVector a i = basisVector b i := by
    have := congrArg (fun v : coordinateModel => v.val (octadIndex i)) h
    simpa [basisMap] using this
  have h0 : a 0 = b 0 := by
    have hh := he 0
    simp only [basisVector, Matrix.cons_val] at hh
    omega
  have h1 : a 1 = b 1 := by
    have hh := he 1
    simp only [basisVector, Matrix.cons_val] at hh
    omega
  have h2 : a 2 = b 2 := by
    have hh := he 2
    simp only [basisVector, Matrix.cons_val] at hh
    omega
  have h3 : a 3 = b 3 := by
    have hh := he 3
    simp only [basisVector, Matrix.cons_val] at hh
    omega
  have h4 : a 4 = b 4 := by
    have hh := he 4
    simp only [basisVector, Matrix.cons_val] at hh
    omega
  have h5 : a 5 = b 5 := by
    have hh := he 5
    simp only [basisVector, Matrix.cons_val] at hh
    omega
  have h6 : a 6 = b 6 := by
    have hh := he 6
    simp only [basisVector, Matrix.cons_val] at hh
    omega
  have h7 : a 7 = b 7 := by
    have hh := he 7
    simp only [basisVector, Matrix.cons_val] at hh
    omega
  funext i
  fin_cases i <;> assumption

theorem basisMap_surjective : Function.Surjective basisMap := by
  intro x
  let v : Fin 8 → ℤ := fun i => x.val (octadIndex i)
  have hs : (∑ i, v i) % 8 = 0 := by
    rw [show (∑ i, v i) = ∑ i, x.val i from octadIndex.sum_comp x.val]
    exact ((mem_coordinateModel _).mp x.prop).2
  have hr := ((mem_coordinateModel _).mp x.prop).1
  have hm : (∀ i, v i % 4 = 0) ∨ (∀ i, v i % 4 = 2) :=
    hr.imp (fun h i => h (octadIndex i)) (fun h i => h (octadIndex i))
  let a : Fin 8 → ℤ :=
    ![v 0 / 2, (v 1 - v 0) / 4, (v 2 - v 0) / 4, (v 3 - v 0) / 4,
      (v 4 - v 0) / 4, (v 5 - v 0) / 4, (v 6 - v 0) / 4,
      (v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + v 7 - 7 * v 0) / 8]
  refine ⟨a, ?_⟩
  have he : basisVector a = v := by
    rcases hm with hm | hm <;>
      have h0 := hm 0 <;> have h1 := hm 1 <;> have h2 := hm 2 <;>
      have h3 := hm 3 <;> have h4 := hm 4 <;> have h5 := hm 5 <;>
      have h6 := hm 6 <;> have h7 := hm 7 <;>
      simp [Fin.sum_univ_succ] at hs <;>
      funext i <;> fin_cases i <;> simp [basisVector, a] <;> omega
  apply Subtype.ext
  funext i
  change basisVector a (octadIndex.symm i) = x.val i
  rw [he]
  simp [v]

/-- Integral parameters for the actual octad lattice. -/
def integralBasis : (Fin 8 → ℤ) ≃ₗ[ℤ] lattice :=
  (LinearEquiv.ofBijective basisMap ⟨basisMap_injective, basisMap_surjective⟩).trans
    coordinateEquiv.symm

/-- The integral squared norm divided by 32 in the triangular basis. -/
def normPolynomial {R : Type*} [CommRing R] (a : Fin 8 → R) : R :=
  a 0 ^ 2 + a 0 * a 7 + 2 * a 7 ^ 2 - 2 * a 7 * (a 1 + a 2 + a 3 + a 4 + a 5 + a 6) +
    a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 +
    a 1 * a 2 + a 1 * a 3 + a 1 * a 4 + a 1 * a 5 + a 1 * a 6 +
    a 2 * a 3 + a 2 * a 4 + a 2 * a 5 + a 2 * a 6 +
    a 3 * a 4 + a 3 * a 5 + a 3 * a 6 + a 4 * a 5 + a 4 * a 6 + a 5 * a 6

def splitFun (a : Fin 8 → ZMod 2) : SelectedGeometry.Space :=
  Sum.elim
    ![a 0 + a 7, a 3 + a 5 + a 6, a 1 + a 3 + a 4 + a 5, a 2 + a 3 + a 4]
    ![a 0, a 4 + a 5 + a 6, a 1 + a 2 + a 6, a 2 + a 3 + a 4 + a 6]

def unsplitFun (v : SelectedGeometry.Space) : Fin 8 → ZMod 2 :=
  let l := fun i => v (Sum.inl i)
  let r := fun i => v (Sum.inr i)
  ![r 0, l 1 + r 1 + r 2 + r 3, l 1 + l 3 + r 1, l 1 + l 2 + l 3 + r 2,
    l 2 + l 3 + r 1 + r 2, l 2 + r 2 + r 3, l 3 + r 3, l 0 + r 0]

/-- Four explicit hyperbolic pairs in the binary parameter space. -/
def splitEquiv : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] SelectedGeometry.Space where
  toFun := splitFun
  invFun := unsplitFun
  left_inv a := by
    funext i
    fin_cases i <;> simp [unsplitFun, splitFun] <;> ring_nf <;>
      simp [show (2 : ZMod 2) = 0 from rfl, show (3 : ZMod 2) = 1 from rfl,
        show (4 : ZMod 2) = 0 from rfl]
  right_inv v := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [unsplitFun, splitFun] <;> ring_nf <;>
      simp [show (2 : ZMod 2) = 0 from rfl, show (3 : ZMod 2) = 1 from rfl,
        show (4 : ZMod 2) = 0 from rfl]
  map_add' a b := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [splitFun] <;> ring
  map_smul' n a := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [splitFun] <;> ring

theorem splitEquiv_norm (a : Fin 8 → ZMod 2) :
    SelectedGeometry.form (splitEquiv a) = normPolynomial a := by
  simp [SelectedGeometry.form, ClassicalOrthogonal.formD_apply, splitEquiv,
    splitFun, normPolynomial, Fin.sum_univ_succ]
  ring_nf
  simp only [show (3 : ZMod 2) = 1 from rfl, mul_one, ZMod.pow_card]
  ring

theorem integralBasis_coordinate (a : Fin 8 → ℤ) (i : Fin 8) :
    (integralBasis a).val.val (octadIndex i).val = basisVector a i := by
  change extendCoordinates (fun j => basisVector a (octadIndex.symm j))
    (octadIndex i).val = basisVector a i
  simp [extendCoordinates, (octadIndex i).prop]

theorem integralBasis_dot (a : Fin 8 → ℤ) :
    integerDot (integralBasis a).val.val (integralBasis a).val.val =
      32 * normPolynomial a := by
  have hd (x : lattice) : integerDot x.val.val x.val.val =
      ∑ i : Coordinate, x.val.val i.val * x.val.val i.val := by
    symm
    apply Fintype.sum_of_injective (fun i : Coordinate => i.val) Subtype.val_injective
    · intro i hi
      have hz : (golayBasis 0).val i = 0 := by
        by_contra hn
        exact hi ⟨⟨i, hn⟩, rfl⟩
      rw [(mem_lattice_iff_support x.val).mp x.prop i hz, zero_mul]
    · intro i
      rfl
  rw [hd, ← octadIndex.sum_comp]
  simp only [integralBasis_coordinate]
  simp [basisVector, normPolynomial, Fin.sum_univ_succ]
  ring

def castParameters : (Fin 8 → ℤ) →+ (Fin 8 → ZMod 2) where
  toFun a i := (a i : ZMod 2)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def binaryMap : lattice →+ (Fin 8 → ZMod 2) :=
  castParameters.comp integralBasis.symm.toAddEquiv.toAddMonoidHom

theorem binaryMap_basis (a : Fin 8 → ℤ) :
    binaryMap (integralBasis a) = castParameters a := by
  simp [binaryMap]

def binaryReduction : ModTwo →+ (Fin 8 → ZMod 2) :=
  QuotientAddGroup.lift twiceLattice binaryMap (by
    rintro x ⟨y, rfl⟩
    change binaryMap ((2 : ℕ) • y) = 0
    rw [map_nsmul, two_nsmul]
    exact ZModModule.add_self _)

theorem binaryReduction_reduction (x : lattice) :
    binaryReduction (reduction x) = binaryMap x := rfl

theorem binaryReduction_injective : Function.Injective binaryReduction := by
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm ?_ bot_le
  intro a ha
  obtain ⟨x, rfl⟩ := reduction_surjective a
  change binaryMap x = 0 at ha
  apply (reduction_eq_zero x).mpr
  refine ⟨integralBasis (fun i => integralBasis.symm x i / 2), ?_⟩
  apply integralBasis.symm.injective
  rw [map_nsmul, LinearEquiv.symm_apply_apply]
  funext i
  have hi := congrFun ha i
  change ((integralBasis.symm x i : ℤ) : ZMod 2) = 0 at hi
  have hm := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hi
  change 2 * (integralBasis.symm x i / 2) = integralBasis.symm x i
  omega

theorem binaryReduction_surjective : Function.Surjective binaryReduction := by
  intro a
  refine ⟨reduction (integralBasis (fun i => (a i).val)), ?_⟩
  rw [binaryReduction_reduction, binaryMap_basis]
  ext i
  simp [castParameters]

/-- Reduction of basis coefficients identifies the literal lattice quotient. -/
def binaryEquiv : ModTwo ≃ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  { AddEquiv.ofBijective binaryReduction
      ⟨binaryReduction_injective, binaryReduction_surjective⟩ with
    map_smul' := ZMod.map_smul binaryReduction }

theorem binaryEquiv_basis (a : Fin 8 → ℤ) :
    binaryEquiv (reduction (integralBasis a)) = castParameters a := binaryMap_basis a

/-- Split coordinates with the prescribed norm on every integral representative. -/
def coordinateWitness : Coordinates where
  coordinates := binaryEquiv.trans splitEquiv
  norm x := by
    obtain ⟨a, rfl⟩ := integralBasis.surjective x
    change SelectedGeometry.form (splitEquiv (binaryEquiv (reduction (integralBasis a)))) = _
    rw [binaryEquiv_basis, splitEquiv_norm, integralBasis_dot]
    rw [Int.mul_ediv_cancel_left _ (by norm_num : (32 : ℤ) ≠ 0)]
    simp [normPolynomial, castParameters]

/-- The coordinate constructor on integral parameters, for geometric consumers. -/
theorem coordinateWitness_basis (a : Fin 8 → ℤ) :
    coordinateWitness.coordinates (reduction (integralBasis a)) =
      splitEquiv (castParameters a) := by
  change splitEquiv (binaryEquiv (reduction (integralBasis a))) = _
  rw [binaryEquiv_basis]

end BinaryCoordinates

/-- The actual binary octad lattice is the split quadratic space of dimension eight. -/
theorem nonempty_coordinates : Nonempty Coordinates :=
  ⟨BinaryCoordinates.coordinateWitness⟩

end Realization.OmegaImage.LatticeModel
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
