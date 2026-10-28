module

public import Theory.AlgebraicGroup.RootSystems.E6RootLattice
public import Theory.AlgebraicGroup.RootSystems.TypeE6DiagramInvolution

/-!
# The E6 diagram action on central characters

In fundamental-weight coordinates the nontrivial E6 diagram symmetry sends
`(x₀,x₁,x₂,x₃,x₄,x₅)` to `(x₅,x₄,x₂,x₃,x₁,x₀)`. On the integral
weight/root quotient its action is negation. The quotient has exponent three,
so a character value fixed by this action is trivial in any target group.
This includes characteristic three and does not use division by three.

These are lattice facts, not an identification of any matrix kernel with the
lattice quotient. The matrix comparison in `WordKernels` consumes them only
with that representation-theoretic input explicit.

Source: GLS3 §§1.12 and 2.5, especially the E6 central diagram action preceding
§2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralLattice

/-- The pinned diagram action in the fundamental-weight coordinates. -/
def weightDiagram : typeE6WeightModule ≃+ typeE6WeightModule where
  toFun x i := x (typeE6DiagramPermutation i)
  invFun x i := x (typeE6DiagramPermutation i)
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := rfl

theorem quotientMap_weightDiagram (x : typeE6WeightModule) :
    typeE6WeightLatticeQuotientMap (weightDiagram x) =
      -typeE6WeightLatticeQuotientMap x := by
  apply eq_neg_iff_add_eq_zero.mpr
  rw [← map_add]
  change (((x 5 + x 0 + 2 * (x 4 + x 1) + (x 1 + x 4) +
    2 * (x 0 + x 5) : ℤ)) : ZMod 3) = 0
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr
  exact ⟨x 0 + x 1 + x 4 + x 5, by ring⟩

/-- In particular the diagram action preserves the actual integral root lattice. -/
theorem weightDiagram_mem_rootLattice_iff (x : typeE6WeightModule) :
    weightDiagram x ∈ typeE6RootLattice ↔ x ∈ typeE6RootLattice := by
  rw [← typeE6WeightLatticeQuotientMap_ker]
  change typeE6WeightLatticeQuotientMap (weightDiagram x) = 0 ↔
    typeE6WeightLatticeQuotientMap x = 0
  rw [quotientMap_weightDiagram, neg_eq_zero]

/-- The induced action on the genuine weight/root lattice quotient. -/
def quotientDiagram : typeE6WeightLatticeQuotient →+ typeE6WeightLatticeQuotient :=
  QuotientAddGroup.map typeE6RootLattice typeE6RootLattice weightDiagram.toAddMonoidHom
    (fun x hx => (weightDiagram_mem_rootLattice_iff x).mpr hx)

@[simp] theorem quotientDiagram_mk (x : typeE6WeightModule) :
    quotientDiagram (QuotientAddGroup.mk' typeE6RootLattice x) =
      QuotientAddGroup.mk' typeE6RootLattice (weightDiagram x) := rfl

/-- The graph automorphism acts by minus one on the E6 fundamental group. -/
theorem quotientDiagram_eq_neg (x : typeE6WeightLatticeQuotient) :
    quotientDiagram x = -x := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    change quotientDiagram (QuotientAddGroup.mk' typeE6RootLattice x) =
      -QuotientAddGroup.mk' typeE6RootLattice x
    apply typeE6WeightLatticeQuotientEquiv.injective
    simpa only [quotientDiagram_mk, map_neg, typeE6WeightLatticeQuotientEquiv_mk]
      using quotientMap_weightDiagram x

theorem three_nsmul_eq_zero (x : typeE6WeightLatticeQuotient) : 3 • x = 0 := by
  apply typeE6WeightLatticeQuotientEquiv.injective
  rw [map_nsmul, map_zero]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, show (3 : ZMod 3) = 0 by decide, zero_mul]

/-- The class of the zeroth fundamental weight in the central-character domain. -/
def centralWeight : typeE6WeightLatticeQuotient :=
  QuotientAddGroup.mk' typeE6RootLattice (Pi.single 0 1)

@[simp] theorem centralWeight_coordinate :
    typeE6WeightLatticeQuotientEquiv centralWeight = 1 := by
  rw [centralWeight, typeE6WeightLatticeQuotientEquiv_mk]
  norm_num [typeE6WeightLatticeQuotientMap, Pi.single_apply, Fin.ext_iff]

section Characters
variable {G : Type*} [Group G]

/-- A multiplicative value of a character of the integral E6 fundamental group. -/
def characterValue (c : typeE6WeightLatticeQuotient →+ Additive G)
    (x : typeE6WeightLatticeQuotient) : G := Additive.toMul (c x)

@[simp] theorem characterValue_zero (c : typeE6WeightLatticeQuotient →+ Additive G) :
    characterValue c 0 = 1 := by simp [characterValue]

theorem characterValue_diagram (c : typeE6WeightLatticeQuotient →+ Additive G)
    (x : typeE6WeightLatticeQuotient) :
    characterValue c (quotientDiagram x) = (characterValue c x)⁻¹ := by
  simp [characterValue, quotientDiagram_eq_neg]

theorem characterValue_cube (c : typeE6WeightLatticeQuotient →+ Additive G)
    (x : typeE6WeightLatticeQuotient) : (characterValue c x) ^ 3 = 1 := by
  have h := congrArg (fun z => Additive.toMul (c z)) (three_nsmul_eq_zero x)
  simpa [characterValue] using h

/-- A fixed central-character value is trivial; no field hypothesis is required. -/
theorem characterValue_eq_one_of_fixed
    (c : typeE6WeightLatticeQuotient →+ Additive G)
    (x : typeE6WeightLatticeQuotient)
    (h : characterValue c (quotientDiagram x) = characterValue c x) :
    characterValue c x = 1 := by
  have hInv : (characterValue c x)⁻¹ = characterValue c x := by
    simpa only [characterValue_diagram] using h
  have hSq : characterValue c x * characterValue c x = 1 := by
    calc
      characterValue c x * characterValue c x =
          (characterValue c x)⁻¹ * characterValue c x :=
        congrArg (fun z => z * characterValue c x) hInv.symm
      _ = 1 := inv_mul_cancel _
  have hCube : (characterValue c x) ^ 3 = characterValue c x := by
    rw [pow_succ, pow_two, hSq, one_mul]
  exact hCube.symm.trans (characterValue_cube c x)

end Characters
end TwistedE6.FoldedSubsystem.HigherRealizations.CentralLattice
