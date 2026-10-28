module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.Orthogonality

/-!
# The singular cubic span in the binary tensor model

A complementary rotation spans a four-group from each nonzero tensor.
For a singular tensor this span is totally singular and lies in its
polar hyperplane. For a pure tensor it is exactly the image obtained by
varying the complementary factor. These small binary calculations feed
the actual conjugation and commutator identifications in `SingularLines`.

Source: Aschbacher–Smith, 15.3.53(2), 15.3.61(2), pp.1146 and 1150.
-/

@[expose] public section
open Subgroup Matrix
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
namespace SingularLineModel

def spanWord (j : Fin 2) (z : TensorVector) (x : Plane) : TensorVector :=
  z ^ (x.toAdd 0).val * (tensorAction (complementaryRotation j) z) ^ (x.toAdd 1).val

theorem spanWord_mul : ∀ (j : Fin 2) (z : TensorVector) (x y : Plane),
    spanWord j z (x * y) = spanWord j z x * spanWord j z y := by decide +kernel

def spanMap (j : Fin 2) (z : TensorVector) : Plane →* TensorVector where
  toFun := spanWord j z
  map_one' := by simp [spanWord]
  map_mul' := spanWord_mul j z

theorem spanMap_injective : ∀ (j : Fin 2) (z : TensorVector), z ≠ 1 →
    Function.Injective (spanMap j z) := by decide +kernel

theorem line_eq_range (j : Fin 2) (z : TensorVector) :
    tensorCubicLine j z = (spanMap j z).range := by
  apply le_antisymm
  · apply sup_le <;> apply zpowers_le.mpr
    · exact ⟨Multiplicative.ofAdd ![1, 0], by norm_num [spanMap, spanWord, ZMod.val_one_eq_one_mod]⟩
    · exact ⟨Multiplicative.ofAdd ![0, 1], by norm_num [spanMap, spanWord, ZMod.val_one_eq_one_mod]⟩
  · rintro _ ⟨x, rfl⟩
    exact (tensorCubicLine j z).mul_mem
      ((tensorCubicLine j z).pow_mem (mem_sup_left (mem_zpowers z)) _)
      ((tensorCubicLine j z).pow_mem (mem_sup_right (mem_zpowers _)) _)

theorem line_card (j : Fin 2) (z : TensorVector) (hz : z ≠ 1) :
    Nat.card (tensorCubicLine j z) = 4 := by
  rw [line_eq_range, MonoidHom.range_eq_map, card_map_of_injective (spanMap_injective j z hz),
    Nat.card_congr Subgroup.topEquiv.toEquiv]
  norm_num [Plane, Nat.card_eq_fintype_card]

theorem span_singular : ∀ (j : Fin 2) (z : TensorVector) (x : Plane),
    z.toAdd.det = 0 → (spanMap j z x).toAdd.det = 0 := by decide +kernel

theorem span_orthogonal : ∀ (j : Fin 2) (z : TensorVector) (x : Plane),
    z.toAdd.det = 0 → determinantPolar z (spanMap j z x) = 0 := by decide +kernel

theorem line_singular (j : Fin 2) (z : TensorVector) (hz : z.toAdd.det = 0)
    (v : TensorVector) (hv : v ∈ tensorCubicLine j z) : v.toAdd.det = 0 := by
  rw [line_eq_range] at hv
  obtain ⟨x, rfl⟩ := hv
  exact span_singular j z x hz

theorem line_le_hyperplane (j : Fin 2) (z : TensorVector) (hz : z.toAdd.det = 0) :
    tensorCubicLine j z ≤ determinantHyperplane z := by
  rw [line_eq_range]
  rintro _ ⟨x, rfl⟩
  exact span_orthogonal j z x hz

private theorem displacement_span : ∀ (j : Fin 2) (z : TensorVector) (n : Fin 3),
    ∃ x : Plane, spanMap j z x = tensorAction (complementaryRotation j ^ n.val) z / z := by
  decide +kernel

theorem displacement_mem (j : Fin 2) (z : TensorVector) (b : Actor)
    (hb : b ∈ complementaryCubic j) : tensorAction b z / z ∈ tensorCubicLine j z := by
  classical
  have hb' : b ∈ zpowers (complementaryRotation j) := hb
  rw [mem_zpowers_iff_mem_range_orderOf, complementaryRotation_order] at hb'
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb'
  rw [line_eq_range]
  exact displacement_span j z ⟨n, Finset.mem_range.mp hn⟩

theorem displacement_recover : ∀ (j : Fin 2) (z : TensorVector),
    z = (tensorAction (complementaryRotation j) z / z) *
      (tensorAction (complementaryRotation j ^ 2) z / z) := by decide +kernel

theorem rotation_recover : ∀ (j : Fin 2) (z : TensorVector),
    tensorAction (complementaryRotation j) z = z *
      (tensorAction (complementaryRotation j) z / z) := by decide +kernel

def pureUpper (j : Fin 2) (x : Plane) : SumVector :=
  if j = 0 then (x, 1) else (1, x)

def purePair (j : Fin 2) (x y : Plane) : TensorVector :=
  if j = 0 then Multiplicative.ofAdd (Matrix.vecMulVec x.toAdd y.toAdd)
  else Multiplicative.ofAdd (Matrix.vecMulVec y.toAdd x.toAdd)

theorem purePair_mul : ∀ (j : Fin 2) (x y w : Plane),
    purePair j x (y * w) = purePair j x y * purePair j x w := by decide +kernel

def pairMap (j : Fin 2) (x : Plane) : Plane →* TensorVector where
  toFun := purePair j x
  map_one' := by fin_cases j <;> simp [purePair]
  map_mul' := purePair_mul j x

theorem purePair_ne_one : ∀ (j : Fin 2) (x y : Plane),
    x ≠ 1 → y ≠ 1 → purePair j x y ≠ 1 := by decide +kernel

theorem pureUpper_ne_one : ∀ (j : Fin 2) (x : Plane), pureUpper j x = 1 ↔ x = 1 := by
  decide +kernel

theorem exists_pureUpper (j : Fin 2) (v : SumVector) (hv : v ∈ naturalSummand j) :
    ∃ x : Plane, v = pureUpper j x := by
  fin_cases j <;> simp [mem_naturalSummand_iff] at hv
  · exact ⟨v.1, Prod.ext rfl hv⟩
  · exact ⟨v.2, Prod.ext hv rfl⟩

def pairingVector (u v : SumVector) : TensorVector := Multiplicative.ofAdd
  (Matrix.vecMulVec u.1.toAdd v.2.toAdd + Matrix.vecMulVec v.1.toAdd u.2.toAdd)

theorem pairing_pure : ∀ (j : Fin 2) (x : Plane) (v : SumVector),
    pairingVector (pureUpper j x) v = pairMap j x (if j = 0 then v.2 else v.1) := by
  decide +kernel

theorem pairing_cross : ∀ (j k : Fin 2) (x y : Plane), j ≠ k →
    pairingVector (pureUpper j x) (pureUpper k y) = purePair j x y := by decide +kernel

private theorem span_pair : ∀ (j : Fin 2) (x y w : Plane),
    ∃ t : Plane, pairMap j x t = spanMap j (purePair j x y) w := by decide +kernel

private theorem pair_span : ∀ (j : Fin 2) (x y w : Plane), y ≠ 1 →
    ∃ t : Plane, spanMap j (purePair j x y) t = pairMap j x w := by decide +kernel

theorem line_eq_pairRange (j : Fin 2) (x y : Plane) (hy : y ≠ 1) :
    tensorCubicLine j (purePair j x y) = (pairMap j x).range := by
  rw [line_eq_range]
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact span_pair j x y w
  · rintro _ ⟨w, rfl⟩
    exact pair_span j x y w hy

end SingularLineModel
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
