module

public import Stellmacher.Recognition.Parrott.CentralizerCoreCoordinatesData
public import Stellmacher.Recognition.Parrott.CentralizerCoreCoordinates
public import Stellmacher.Recognition.Parrott.CentralizerCoreTripleTensor

/-!
# Reduction of core action rigidity to intrinsic coordinates

Once the literal core has its ordered binary coordinates and its scalar triple
commutator has the specified tensor table, five transported group identities
force the b- and c-images. Involutivity supplies the reverse d-image from the
a-image. This module checks that reduction with the original frame unchanged.

The coordinate construction and tensor evaluation are also discharged in the
unconditional `core_orientation_remaining_images` wrapper below.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.678–681, equations (2), (3), (5), (10)–(15), and (23).
-/

open Subgroup
open Theory.GroupAction.BinaryFourTripleOrientation

namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private theorem binary_exponent_injective (hz : z ≠ 1) (s t : ZMod 2)
    (hst : z ^ s.val = z ^ t.val) : s = t := by
  have hb : ∀ v : ZMod 2, v = 0 ∨ v = 1 := by decide
  rcases hb s with rfl | rfl <;> rcases hb t with rfl | rfl
  · rfl
  · simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one] at hst
    exact (hz hst.symm).elim
  · simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one] at hst
    exact (hz hst).elim
  · rfl

/-- The five actual conjugated triple commutators imply both requested coset
images, provided the coordinates and their intrinsic tensor formula are proved. -/
public theorem ParrottSylowGeneratorData.core_orientation_remaining_images_of_coordinates
    (f : ParrottSylowGeneratorData n) [Finite G]
    (h : ParrottCentralizerHypotheses z) (q : ParrottCore.Coordinates f)
    (htensor : ∀ g k l : ParrottCore.Core z,
      Tits.parrottCommutator (Tits.parrottCommutator (g : G) (k : G)) (l : G) =
        z ^ (tensor (q.toHom g).toAdd (q.toHom k).toAdd (q.toHom l).toAdd).val)
    (r : G) (hrH : r ∈ centralizer ({z} : Set G)) (hr : r ^ 2 = 1)
    (ha : f.d⁻¹ * (r⁻¹ * f.a * r) ∈ ParrottCore.Derived z) :
    (f.d * f.c * f.b)⁻¹ * (r⁻¹ * f.b * r) ∈ ParrottCore.Derived z ∧
      (f.c * f.d * f.a)⁻¹ * (r⁻¹ * f.c * r) ∈ ParrottCore.Derived z := by
  have hz : z ≠ 1 := by
    intro hz
    have hh := h.involution
    rw [hz, orderOf_one] at hh
    omega
  obtain ⟨haK, hbK, hcK, hdK⟩ := f.core_orientation_mem_core
  let a : ParrottCore.Core z := ⟨f.a, haK⟩
  let b : ParrottCore.Core z := ⟨f.b, hbK⟩
  let c : ParrottCore.Core z := ⟨f.c, hcK⟩
  let d : ParrottCore.Core z := ⟨f.d, hdK⟩
  let ar : ParrottCore.Core z := ⟨r⁻¹ * f.a * r, ParrottCore.conjugate_mem r f.a hrH haK⟩
  let br : ParrottCore.Core z := ⟨r⁻¹ * f.b * r, ParrottCore.conjugate_mem r f.b hrH hbK⟩
  let cr : ParrottCore.Core z := ⟨r⁻¹ * f.c * r, ParrottCore.conjugate_mem r f.c hrH hcK⟩
  let dr : ParrottCore.Core z := ⟨r⁻¹ * f.d * r, ParrottCore.conjugate_mem r f.d hrH hdK⟩
  have har : (q.toHom ar).toAdd = ![0,0,0,1] :=
    ((q.eq_iff d ar).mpr ha).symm.trans (q.map_d d rfl)
  have hdr : (q.toHom dr).toAdd = ![1,0,0,0] :=
    ((q.eq_iff a dr).mpr (f.core_orientation_d_image_of_a_image r hrH hr ha)).symm.trans
      (q.map_a a rfl)
  obtain ⟨habc, hacb, hadc, hbcc, hbcd⟩ := f.core_orientation_triple_entries
  have hval (x y w : G) (xr yr wr : ParrottCore.Core z)
      (hx : (xr : G) = r⁻¹ * x * r) (hy : (yr : G) = r⁻¹ * y * r)
      (hw : (wr : G) = r⁻¹ * w * r) (t : ZMod 2)
      (ht : Tits.parrottCommutator (Tits.parrottCommutator x y) w = z ^ t.val) :
      tensor (q.toHom xr).toAdd (q.toHom yr).toAdd (q.toHom wr).toAdd = t := by
    apply binary_exponent_injective hz
    rw [← htensor, hx, hy, hw]
    exact ParrottCore.conjugate_triple r x y w hrH t.val ht
  have h012 : tensor ![0,0,0,1] (q.toHom br).toAdd (q.toHom cr).toAdd = 0 := by
    rw [← har]
    exact hval f.a f.b f.c ar br cr rfl rfl rfl 0 (by simpa using habc)
  have h021 : tensor ![0,0,0,1] (q.toHom cr).toAdd (q.toHom br).toAdd = 0 := by
    rw [← har]
    exact hval f.a f.c f.b ar cr br rfl rfl rfl 0 (by simpa using hacb)
  have h032 : tensor ![0,0,0,1] ![1,0,0,0] (q.toHom cr).toAdd = 0 := by
    rw [← har, ← hdr]
    exact hval f.a f.d f.c ar dr cr rfl rfl rfl 0 (by simpa using hadc)
  have h122 : tensor (q.toHom br).toAdd (q.toHom cr).toAdd (q.toHom cr).toAdd = 1 := by
    exact hval f.b f.c f.c br cr cr rfl rfl rfl 1 (by simpa only [ZMod.val_one, pow_one] using hbcc)
  have h123 : tensor (q.toHom br).toAdd (q.toHom cr).toAdd ![1,0,0,0] = 0 := by
    rw [← hdr]
    exact hval f.b f.c f.d br cr dr rfl rfl rfl 0 (by simpa using hbcd)
  obtain ⟨hb, hc⟩ := remaining_images (q.toHom br).toAdd (q.toHom cr).toAdd
    h012 h021 h032 h122 h123
  constructor
  · apply (q.eq_iff (d * c * b) br).mp
    rw [q.toHom.map_mul, q.toHom.map_mul]
    change (q.toHom d).toAdd + (q.toHom c).toAdd + (q.toHom b).toAdd = _
    rw [q.map_d d rfl, q.map_c c rfl, q.map_b b rfl, hb]
    decide
  · apply (q.eq_iff (c * d * a) cr).mp
    rw [q.toHom.map_mul, q.toHom.map_mul]
    change (q.toHom c).toAdd + (q.toHom d).toAdd + (q.toHom a).toAdd = _
    rw [q.map_c c rfl, q.map_d d rfl, q.map_a a rfl, hc]
    decide

/- The coordinate and tensor constructions are intrinsic to the supplied frame,
so the preceding certificate has an unconditional wrapper for consumers. -/
public theorem ParrottSylowGeneratorData.core_orientation_remaining_images
    (f : ParrottSylowGeneratorData n) [Finite G]
    (h : ParrottCentralizerHypotheses z)
    (r : G) (hrH : r ∈ centralizer ({z} : Set G)) (hr : r ^ 2 = 1)
    (ha : f.d⁻¹ * (r⁻¹ * f.a * r) ∈
      (commutator (pCore 2 (centralizer ({z} : Set G)))).map
        ((centralizer ({z} : Set G)).subtype.comp
          (pCore 2 (centralizer ({z} : Set G))).subtype)) :
    (f.d * f.c * f.b)⁻¹ * (r⁻¹ * f.b * r) ∈
        (commutator (pCore 2 (centralizer ({z} : Set G)))).map
          ((centralizer ({z} : Set G)).subtype.comp
            (pCore 2 (centralizer ({z} : Set G))).subtype) ∧
      (f.c * f.d * f.a)⁻¹ * (r⁻¹ * f.c * r) ∈
        (commutator (pCore 2 (centralizer ({z} : Set G)))).map
          ((centralizer ({z} : Set G)).subtype.comp
            (pCore 2 (centralizer ({z} : Set G))).subtype) := by
  obtain ⟨q⟩ := parrott_core_coordinates h f
  exact f.core_orientation_remaining_images_of_coordinates h q
    (fun g k l => f.core_triple_tensor h q g k l) r hrH hr ha

end Stellmacher.Recognition
