module
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.Representatives
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.QuadraticSpace.Coordinates

/-!
# Additivity of the source Golay–Leech map

The integral identity for the sum of two code vectors gives the intersection
cocode and the half-overlap multiple of the all-ones vector. Complementation
and reduction modulo twice the actual lattice then give exactly the twisted
coordinate sum, so the prescribed map is linear over the binary field.

Source: Aschbacher, *Sporadic Groups*, Lemmas 23.8 and 23.10(1), printed
pp. 119–121, specialized in Lemma 27.2, pp. 144–145. The imported Golay
and Leech constructions are the attributed ATLAS ports.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped BigOperators
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

private theorem lift_add (a b : BinaryWord) (i : Omega) :
    golayIntegerLift (a + b) i = golayIntegerLift a i + golayIntegerLift b i -
      2 * golayIntegerLift (fun j => a j * b j) i := by
  rcases bit_cases (a i) with ha | ha <;> rcases bit_cases (b i) with hb | hb <;>
    simp [golayIntegerLift, ha, hb]

private theorem weight_intersection (a b : BinaryWord) :
    hammingNorm (fun i => a i * b i) = overlap a b := by
  simp only [hammingNorm_eq_sum, overlap_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases bit_cases (a i) with ha | ha <;> rcases bit_cases (b i) with hb | hb <;>
    simp [ha, hb]

/-- Complementation contributes the all-ones vector modulo twice the lattice. -/
theorem sourceCodeVector_complement (v : golay) :
    sourceCodeVector (v + golayOne) = sourceCodeVector golayOne - sourceCodeVector v := by
  apply Subtype.ext
  ext i
  change 2 * golayIntegerLift (v.val + golayOne.val) i =
    (sourceCodeVector golayOne).val i - (sourceCodeVector v).val i
  rw [sourceCodeVector_one_apply, sourceCodeVector_apply]
  rcases bit_cases (v.val i) with h | h <;>
    simp [golayIntegerLift, golayOne, allOnes, h]

/-- The integral identity behind the two correction terms in the twisted sum. -/
theorem sourceCodeVector_add (v w : golay) :
    sourceCodeVector v + sourceCodeVector w = sourceCodeVector (v + w) +
      sourceCocodeVector (fun i => v.val i * w.val i) +
      ((overlap v.val w.val / 2 : ℕ) : ℤ) • sourceCodeVector golayOne := by
  have hd := golay_overlap_two_dvd v w
  have he : (overlap v.val w.val : ℤ) = 2 * (overlap v.val w.val / 2 : ℕ) := by
    exact_mod_cast (show overlap v.val w.val = 2 * (overlap v.val w.val / 2) by omega)
  apply Subtype.ext
  ext i
  change (sourceCodeVector v).val i + (sourceCodeVector w).val i =
    (sourceCodeVector (v + w)).val i + (sourceCocodeVector _).val i +
      (overlap v.val w.val / 2 : ℕ) * (sourceCodeVector golayOne).val i
  rw [sourceCodeVector_one_apply]
  simp only [sourceCodeVector_apply, sourceCocodeVector_apply,
    Submodule.coe_add, weight_intersection, he, lift_add]
  ring

/-- A code class gains exactly the all-ones class under complementation. -/
theorem sourceCodeClass_add_one (v : golay) :
    leechReduction (sourceCodeVector (v + golayOne)) =
      leechReduction (sourceCodeVector v) + leechReduction (sourceCodeVector golayOne) := by
  rw [sourceCodeVector_complement, map_sub]
  have hn : -(leechReduction (sourceCodeVector v)) = leechReduction (sourceCodeVector v) :=
    neg_eq_of_add_eq_zero_left (by
      rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul Bit]
      exact zero_smul Bit _)
  rw [sub_eq_add_neg, hn, add_comm]

theorem sourceCodeClass_add_smul_one (v : golay) (s : Bit) :
    leechReduction (sourceCodeVector (v + s • golayOne)) =
      leechReduction (sourceCodeVector v) + s • leechReduction (sourceCodeVector golayOne) := by
  rcases bit_cases s with rfl | rfl
  · simp
  · simpa using sourceCodeClass_add_one v

/-- The source map respects the half-overlap and intersection corrections. -/
theorem sourceCodeClass_twisted_sum (v w : golay) :
    leechReduction (sourceCodeVector (v + w + golayHalfOverlap v w • golayOne)) +
      sourceCocodeClass (intersectionCocode v w) =
      leechReduction (sourceCodeVector v) + leechReduction (sourceCodeVector w) := by
  rw [sourceCodeClass_add_smul_one, intersectionCocode, sourceCocodeClass_mk]
  have h := congrArg leechReduction (sourceCodeVector_add v w)
  simp only [map_add, map_zsmul] at h
  rw [h]
  have hs : ((overlap v.val w.val / 2 : ℕ) : ℤ) •
      leechReduction (sourceCodeVector golayOne) =
      golayHalfOverlap v w • leechReduction (sourceCodeVector golayOne) := by
    simp only [golayHalfOverlap, Nat.cast_smul_eq_nsmul]
  rw [hs]
  ac_rfl

theorem sourceCoordinateMap_add (x y : QuadraticCoordinates) :
    sourceCoordinateMap (x + y) = sourceCoordinateMap x + sourceCoordinateMap y := by
  change sourceCoordinateMap (TrialitySpin.coordinateSum x y) = _
  simp only [sourceCoordinateMap, TrialitySpin.coordinateSum, map_add]
  calc
    _ = (leechReduction (sourceCodeVector
        (x.code + y.code + golayHalfOverlap x.code y.code • golayOne)) +
        sourceCocodeClass (intersectionCocode x.code y.code)) +
        (sourceCocodeClass x.cocode + sourceCocodeClass y.cocode) := by ac_rfl
    _ = _ := by rw [sourceCodeClass_twisted_sum]; ac_rfl

/-- Linearization of the explicit source representative map. -/
def sourceCoordinateLinearMap : QuadraticCoordinates →ₗ[Bit] LeechModTwo :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := sourceCoordinateMap
      map_zero' := sourceCoordinateMap_zero
      map_add' := sourceCoordinateMap_add }

@[simp] theorem sourceCoordinateLinearMap_apply (x : QuadraticCoordinates) :
    sourceCoordinateLinearMap x = sourceCoordinateMap x := rfl

end Sporadic.Monster.Construction.LocalC
