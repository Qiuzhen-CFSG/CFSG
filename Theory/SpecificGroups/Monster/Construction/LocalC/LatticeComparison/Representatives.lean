module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.QuadraticData
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechQuadraticSpace

/-!
# Source representatives for the Golay–Leech comparison

For a Golay word `v`, the source vector `f_v` is twice its integral indicator.
For an arbitrary binary word `J`, `f(J)` is four times its indicator minus
its weight times the all-ones vector. It is the sum of the negatives of the
odd glue vectors on `J`. Reduction modulo twice the actual Leech lattice
is linear in `J` and kills the Golay code, so it descends to the cocode.
This defines the precise set map in Lemmas 23.10 and 27.2 before proving
its compatibility with the twisted coordinate addition.

Source: Aschbacher, *Sporadic Groups*, Lemmas 23.8–23.10, pp. 119–121,
and Lemma 27.2, pp. 144–145. The integral Golay and Leech definitions are
the attributed ATLAS ports imported above.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped BigOperators
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

/-- The source `f_v = 2 e_v`, in the actual integral lattice. -/
def sourceCodeVector (v : golay) : leech :=
  ⟨(2 : ℤ) • golayIntegerLift v.val,
    Or.inl ⟨golayIntegerLift v.val, lift_mem_evenHalfLattice v.val v.prop, rfl⟩⟩

@[simp] theorem sourceCodeVector_apply (v : golay) (i : Omega) :
    (sourceCodeVector v).val i = 2 * golayIntegerLift v.val i := rfl

@[simp] theorem sourceCodeVector_zero : sourceCodeVector 0 = 0 := by
  apply Subtype.ext
  ext i
  simp [sourceCodeVector, golayIntegerLift]

@[simp] theorem sourceCodeVector_one_apply (i : Omega) :
    (sourceCodeVector golayOne).val i = 2 := by
  simp [sourceCodeVector, golayIntegerLift, golayOne, allOnes]

/-- The source vector `-λ_x`, whose coordinates are `3` at `x` and `-1` elsewhere. -/
def sourcePointVector (x : Omega) : leech :=
  -⟨oddGlue x, by
    change oddGlue x ∈ leechAt ((0,0),0)
    rw [leechAt_independent ((0,0),0) x]
    exact oddGlue_mem x⟩

@[simp] theorem sourcePointVector_apply (x i : Omega) :
    (sourcePointVector x).val i = (if i = x then 4 else 0) - 1 := by
  change -(1 - if i = x then 4 else 0) = _
  ring

/-- The source `f(J) = 2 f_J - |J| f_X / 2`, realized as a sum in `Λ`. -/
def sourceCocodeVector (J : BinaryWord) : leech :=
  ∑ x, if J x = 0 then 0 else sourcePointVector x

/-- The integral coordinate formula fixes the source normalization. -/
theorem sourceCocodeVector_apply (J : BinaryWord) (i : Omega) :
    (sourceCocodeVector J).val i =
      4 * golayIntegerLift J i - (hammingNorm J : ℤ) := by
  change (∑ x, if J x = 0 then (0 : leech) else sourcePointVector x).val i = _
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  calc
    _ = ∑ x, ((if i = x then 4 * golayIntegerLift J x else 0) -
        golayIntegerLift J x) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : J x = 0 <;> simp [h, sourcePointVector_apply, golayIntegerLift]
    _ = _ := by simp [Finset.sum_sub_distrib, sum_golayIntegerLift]

/-- Before cocode descent, reduction of `f(J)` is a linear function of `J`. -/
def sourceWordClass : BinaryWord →ₗ[Bit] LeechModTwo :=
  ∑ x : Omega, (LinearMap.proj x).smulRight (leechReduction (sourcePointVector x))

theorem sourceWordClass_eq_reduction (J : BinaryWord) :
    sourceWordClass J = leechReduction (sourceCocodeVector J) := by
  simp only [sourceWordClass, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, sourceCocodeVector, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rcases bit_cases (J x) with h | h <;> simp [h]

/-- On a codeword, an explicit half of `f(v)` lies in the Leech lattice. -/
theorem sourceCocodeVector_code (v : golay) :
    sourceCocodeVector v.val = (2 : ℕ) •
      (sourceCodeVector v - ((hammingNorm v.val / 4 : ℕ) : ℤ) •
        sourceCodeVector golayOne) := by
  apply Subtype.ext
  ext i
  have hw := Nat.mod_add_div (hammingNorm v.val) 4
  have hd := Nat.mod_eq_zero_of_dvd (golay_doublyEven v.val v.prop)
  have he : (hammingNorm v.val : ℤ) = 4 * (hammingNorm v.val / 4 : ℕ) := by
    exact_mod_cast (show hammingNorm v.val = 4 * (hammingNorm v.val / 4) by omega)
  rw [sourceCocodeVector_apply]
  change 4 * golayIntegerLift v.val i - (hammingNorm v.val : ℤ) =
    2 * ((sourceCodeVector v).val i - (hammingNorm v.val / 4 : ℕ) *
      (sourceCodeVector golayOne).val i)
  rw [sourceCodeVector_apply, sourceCodeVector_one_apply, he]
  ring

theorem sourceWordClass_code (v : golay) : sourceWordClass v.val = 0 := by
  rw [sourceWordClass_eq_reduction]
  exact (leechReduction_eq_zero _).mpr ⟨_, (sourceCocodeVector_code v).symm⟩

/-- The class of the source `f(J)` depends only on `J + Golay`. -/
def sourceCocodeClass : Cocode →ₗ[Bit] LeechModTwo :=
  golay.liftQ sourceWordClass (fun J hJ => sourceWordClass_code ⟨J,hJ⟩)

@[simp] theorem sourceCocodeClass_mk (J : BinaryWord) :
    sourceCocodeClass (Submodule.Quotient.mk J) =
      leechReduction (sourceCocodeVector J) :=
  sourceWordClass_eq_reduction J

/-- The actual map in 23.10 and 27.2; its additivity uses `coordinateSum`. -/
def sourceCoordinateMap (x : QuadraticCoordinates) : LeechModTwo :=
  leechReduction (sourceCodeVector x.code) + sourceCocodeClass x.cocode

/-- Exact source formula, with no choice of cocode representative in the map. -/
theorem sourceCoordinateMap_mk (v : golay) (J : BinaryWord) :
    sourceCoordinateMap ⟨v, Submodule.Quotient.mk J⟩ =
      leechReduction (sourceCodeVector v + sourceCocodeVector J) := by
  rw [sourceCoordinateMap, sourceCocodeClass_mk, map_add]

@[simp] theorem sourceCoordinateMap_zero : sourceCoordinateMap coordinateZero = 0 := by
  simp [sourceCoordinateMap, coordinateZero]

end Sporadic.Monster.Construction.LocalC
