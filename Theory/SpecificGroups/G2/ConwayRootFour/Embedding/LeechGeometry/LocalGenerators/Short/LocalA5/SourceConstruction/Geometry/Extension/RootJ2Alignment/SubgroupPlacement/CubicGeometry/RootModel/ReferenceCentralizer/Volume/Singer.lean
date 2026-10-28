module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Coordinates

/-!
# An explicit forbidden candidate in the reference matrix coordinates

The companion matrix of X³ + X² + X + ω has determinant ω and order 63.
Explicit three-by-three products over the retained GoldenFour carrier certify
its third, seventh, ninth and twenty-first powers. Field transport retains the
literal `referenceScalar`, and the ninth and twenty-first power tests exclude
all proper divisors of 63 as eigenvalue orders. No assertion that this matrix
is excluded from the reference centralizer is made here.

This supplies the concrete matrix used by `Volume.Reduction` for the
determinant step in Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, and
49.5, p.283. The finite-field calculation is independent of the source
centralizer identification.
-/

@[expose] public noncomputable section
open Atlas.Algebra Atlas.Conway Atlas.Lattices Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long

private theorem order_mapMatrix {K L : Type*} [CommRing K] [CommRing L]
    (e : K ≃+* L) (M : Matrix (Fin 3) (Fin 3) K) :
    orderOf (e.toRingHom.mapMatrix M) = orderOf M :=
  e.mapMatrix.toMulEquiv.orderOf_eq M

private def goldenSinger : Matrix (Fin 3) (Fin 3) GoldenFour :=
  !![0,0,goldenFourTau; 1,0,1; 0,1,1]

private theorem goldenSinger_det : goldenSinger.det = goldenFourTau := by decide +kernel

private def goldenSingerCube : Matrix (Fin 3) (Fin 3) GoldenFour :=
  let w := goldenFourTau
  !![w,w,0; 1,w+1,w; 1,0,w+1]

private def goldenSingerSeventh : Matrix (Fin 3) (Fin 3) GoldenFour :=
  let w := goldenFourTau
  !![w,w+1,w+1; 0,0,1; w,w,w]

private def goldenSingerNinth : Matrix (Fin 3) (Fin 3) GoldenFour :=
  let w := goldenFourTau
  !![w+1,w+1,1; 1,1,0; w,w+1,w]

private theorem goldenSinger_cube : goldenSinger ^ 3 = goldenSingerCube := by
  decide +kernel

private theorem goldenSinger_seventh : goldenSinger ^ 7 = goldenSingerSeventh := by
  calc
    goldenSinger ^ 7 = (goldenSinger ^ 3) ^ 2 * goldenSinger := by noncomm_ring
    _ = goldenSingerSeventh := by rw [goldenSinger_cube]; decide +kernel

private theorem goldenSinger_ninth : goldenSinger ^ 9 = goldenSingerNinth := by
  rw [show 9 = 3 * 3 from rfl, pow_mul, goldenSinger_cube]
  decide +kernel

private theorem goldenSinger_twentyFirst :
    goldenSinger ^ 21 = goldenFourTau • (1 : Matrix (Fin 3) (Fin 3) GoldenFour) := by
  rw [show 21 = 7 * 3 from rfl, pow_mul, goldenSinger_seventh]
  decide +kernel

private theorem goldenSinger_sixtyThird : goldenSinger ^ 63 = 1 := by
  rw [show 63 = 21 * 3 from rfl, pow_mul, goldenSinger_twentyFirst, smul_pow]
  rw [show goldenFourTau ^ 3 = 1 from by decide +kernel, one_pow, one_smul]

private theorem goldenSinger_order : orderOf goldenSinger = 63 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) goldenSinger_sixtyThird
  intro p hp hd
  have hm := hp.mem_primeFactors hd (by decide : (63 : ℕ) ≠ 0)
  rw [show (63 : ℕ).primeFactors = {3,7} from by decide +kernel,
    Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · change goldenSinger ^ 21 ≠ 1
    rw [goldenSinger_twentyFirst]
    decide +kernel
  · change goldenSinger ^ 9 ≠ 1
    rw [goldenSinger_ninth]
    decide +kernel

/-- A fixed Singer matrix, transported through the exact scalar-field equivalence. -/
def referenceSinger : Matrix (Fin 3) (Fin 3) F :=
  !![0,0,referenceScalar; 1,0,1; 0,1,1]

private theorem referenceSinger_map : referenceSinger =
    Long.scalarFieldEquiv.symm.toRingHom.mapMatrix goldenSinger := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [referenceSinger, goldenSinger, referenceScalar]

/-- This matrix has the chosen nontrivial determinant. -/
theorem referenceSinger_det : referenceSinger.det = referenceScalar := by
  rw [referenceSinger_map, ← Long.scalarFieldEquiv.symm.toRingHom.map_det, goldenSinger_det]
  rfl

/-- The matrix has order 63; small product certificates establish the power tests. -/
theorem referenceSinger_order : orderOf referenceSinger = 63 := by
  rw [referenceSinger_map, order_mapMatrix]
  exact goldenSinger_order

theorem referenceSinger_pow_sixtyThree : referenceSinger ^ 63 = 1 := by
  rw [← referenceSinger_order]
  exact pow_orderOf_eq_one _

/-- There are no trivial coordinates in this matrix action. -/
theorem referenceSinger_sub_one_det_ne_zero : (referenceSinger - 1).det ≠ 0 := by
  have h : (goldenSinger - 1).det ≠ 0 := by decide +kernel
  have he : referenceSinger - 1 =
      Long.scalarFieldEquiv.symm.toRingHom.mapMatrix (goldenSinger - 1) := by
    rw [map_sub, map_one, referenceSinger_map]
  rw [he, ← Long.scalarFieldEquiv.symm.toRingHom.map_det]
  exact fun hz => h (Long.scalarFieldEquiv.symm.injective
    (hz.trans (map_zero _).symm))

/-- No eigenvalue has order dividing nine. -/
theorem referenceSinger_ninth_sub_one_det_ne_zero : (referenceSinger ^ 9 - 1).det ≠ 0 := by
  have h : (goldenSinger ^ 9 - 1).det ≠ 0 := by
    rw [goldenSinger_ninth]
    decide +kernel
  have he : referenceSinger ^ 9 - 1 =
      Long.scalarFieldEquiv.symm.toRingHom.mapMatrix (goldenSinger ^ 9 - 1) := by
    rw [map_sub, map_one, map_pow, referenceSinger_map]
  rw [he, ← Long.scalarFieldEquiv.symm.toRingHom.map_det]
  exact fun hz => h (Long.scalarFieldEquiv.symm.injective
    (hz.trans (map_zero _).symm))

/-- No eigenvalue has order dividing twenty-one. Together with the 63rd-power
identity, these two tests force every eigenvalue to have order 63. -/
theorem referenceSinger_twentyFirst_sub_one_det_ne_zero :
    (referenceSinger ^ 21 - 1).det ≠ 0 := by
  have h : (goldenSinger ^ 21 - 1).det ≠ 0 := by
    rw [goldenSinger_twentyFirst]
    decide +kernel
  have he : referenceSinger ^ 21 - 1 =
      Long.scalarFieldEquiv.symm.toRingHom.mapMatrix (goldenSinger ^ 21 - 1) := by
    rw [map_sub, map_one, map_pow, referenceSinger_map]
  rw [he, ← Long.scalarFieldEquiv.symm.toRingHom.map_det]
  exact fun hz => h (Long.scalarFieldEquiv.symm.injective
    (hz.trans (map_zero _).symm))

theorem referenceScalar_ne_one : referenceScalar ≠ 1 := by
  intro h
  apply referenceScalar_ne_inv
  rw [h, inv_one]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
