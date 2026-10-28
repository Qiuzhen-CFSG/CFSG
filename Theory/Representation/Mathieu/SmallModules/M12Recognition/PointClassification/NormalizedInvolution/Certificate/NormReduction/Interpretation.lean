module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Assembly
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Inputs

/-!
# Interpret finite row certificates in the two-sided norm ideal

`SeedGeometry` connects each of the 7620 original seeds to an actual
left-and-right translate of `elevenNorm`. `RowIdentities` is a separate
binary cancellation calculation, using only those original seeds. The
basis and left-action tables are explicitly identified with the published
300 words and marked generators. The resulting column relations feed
`Assembly` and establish its two conclusions once both certificates exist.

The interpretation is a direct linear map on coordinates. It does not
require an enumeration theorem, injectivity of the word table, a group
presentation, or any assumption about the candidate matrix representation.

Source application: Aschbacher–Smith G.7.3(2), printed p.348/PDF p.359.
-/

public section
open scoped BigOperators MonoidAlgebra
open Sporadic.Mathieu
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction
open CertificateData Inputs

/-- The seed entries must be the literal translates of the eleven powers. -/
@[expose] def SeedGeometry : Prop := ∀ (k : Seed) (t : Fin 11),
  indexElement (seedEntry k t) =
    indexElement (translateLeft k) * m11Sylow11Generator ^ t.val *
      indexElement (translateRight k)

/-- Identification with the 300 already-published actual basis words. -/
@[expose] def BasisGeometry : Prop := ∀ j : Fin 300,
  indexElement (basisIndex j) = CertificateData.evalWord (basisWord j)

/-- The target entry is LEFT multiplication, with the published A/B order. -/
@[expose] def LeftGeometry : Prop := ∀ (s : Fin 2) (j : Fin 300),
  indexElement (leftIndex s j) = generator s * CertificateData.evalWord (basisWord j)

/-- A finite binary identity independent of the interpretation in the group. -/
@[expose] def RowIdentities : Prop := ∀ (s : Fin 2) (j : Fin 300),
  columnVector s j = combinationVector s j

private noncomputable def coordinateMap {ι : Type*} [Fintype ι] (f : ι → R) :
    (ι → ZMod 2) →ₗ[ZMod 2] R where
  toFun v := ∑ i, v i • f i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [smul_smul, Finset.smul_sum]

private theorem coordinateMap_apply {ι : Type*} [Fintype ι] (f : ι → R)
    (v : ι → ZMod 2) : coordinateMap f v = ∑ i, v i • f i := rfl

private theorem coordinateMap_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → R) (i : ι) : coordinateMap f (Pi.single i 1) = f i := by
  rw [coordinateMap_apply]
  simp [Pi.single_apply]

/-- Interpret every coordinate in the actual group algebra. Injectivity is not
needed: these are sums of actual words, before taking any quotient. -/
noncomputable def decode : Coordinates →ₗ[ZMod 2] R :=
  coordinateMap (fun i => MonoidAlgebra.single (indexElement i) 1)

theorem decode_apply (v : Coordinates) :
    decode v = ∑ i, v i • MonoidAlgebra.single (indexElement i) 1 :=
  coordinateMap_apply (fun i : Index => MonoidAlgebra.single (indexElement i) 1) v

theorem decode_single (i : Index) :
    decode (Pi.single i 1) = MonoidAlgebra.single (indexElement i) 1 :=
  coordinateMap_single (fun i : Index => MonoidAlgebra.single (indexElement i) 1) i

theorem decode_seed_mem (hg : SeedGeometry) (k : Seed) :
    decode (seedVector k) ∈ elevenIdeal := by
  have he : decode (seedVector k) =
      MonoidAlgebra.single (indexElement (translateLeft k)) 1 * elevenNorm *
        MonoidAlgebra.single (indexElement (translateRight k)) 1 := by
    rw [seedVector, map_sum]
    simp only [decode_single, hg k]
    simp only [elevenNorm, Finset.mul_sum, Finset.sum_mul,
      MonoidAlgebra.single_mul_single, mul_one]
    exact Fin.sum_univ_eq_sum_range (fun t =>
      MonoidAlgebra.single (indexElement (translateLeft k) * m11Sylow11Generator ^ t *
        indexElement (translateRight k)) (1 : ZMod 2)) 11
  rw [he]
  exact norm_translate_mem _ _

theorem decode_combination_mem (hg : SeedGeometry) (s : Fin 2) (j : Fin 300) :
    decode (combinationVector s j) ∈ elevenIdeal := by
  rw [combinationVector, map_sum]
  apply sum_mem
  intro k _
  split_ifs
  · exact decode_seed_mem hg k
  · rw [map_zero]
    exact elevenIdeal.zero_mem

theorem action_single (s : Fin 2) (j : Fin 300) :
    action s (Pi.single j 1) = fun i => actionMatrix s i j := by
  simp only [action, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply']

theorem decode_column (hb : BasisGeometry) (hl : LeftGeometry)
    (s : Fin 2) (j : Fin 300) :
    decode (columnVector s j) =
      MonoidAlgebra.single (generator s) 1 * basisElement j -
        lift (action s (Pi.single j 1)) := by
  simp only [BasisGeometry] at hb
  simp only [LeftGeometry] at hl
  rw [columnVector, map_sub, map_sum]
  simp only [map_smul, decode_single, hb, hl]
  rw [action_single, lift_apply]
  simp only [basisElement, MonoidAlgebra.single_mul_single, mul_one]

/-- Concrete norm geometry and independent binary cancellation suffice for
all 600 relations in the actual two-sided norm ideal. -/
theorem columns_of_certificates (hg : SeedGeometry) (hb : BasisGeometry)
    (hl : LeftGeometry) (hr : RowIdentities) : ColumnRelations := by
  intro s j
  rw [← decode_column hb hl, hr s j]
  exact decode_combination_mem hg s j

/-- Final assembly retains both independent finite certificates as premises. -/
theorem norm_reduction_of_certificates (hg : SeedGeometry) (hb : BasisGeometry)
    (hl : LeftGeometry) (hr : RowIdentities) :
    (∀ x : R, ∃ v : Space, x - lift v ∈ elevenIdeal) ∧
    (∀ (s : Fin 2) (v : Space),
      MonoidAlgebra.single (generator s) 1 * lift v - lift (action s v) ∈ elevenIdeal) := by
  have h := columns_of_certificates hg hb hl hr
  exact ⟨exists_lift_of_columns h, generator_lift_sub_mem_of_columns h⟩

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction
