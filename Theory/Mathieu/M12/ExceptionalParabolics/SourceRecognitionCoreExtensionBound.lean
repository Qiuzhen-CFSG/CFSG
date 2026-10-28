module
public import Theory.GroupTheory.ThreeInvolutionFourCommutators.Structure
public import Theory.GroupTheory.DihedralPresentation
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card

/-!
# The order bound for the normalized second M₁₂ endpoint

The three involutions generate a group of order thirty-two. The two extra
actors permute those generators by conjugation, making this core normal.
Modulo the core, the actors satisfy the dihedral presentation of order six.
The generated extension therefore has at most 192 elements.

This supplies the normalized extension calculation used in the identification
following Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.12),
pp.405–406. The concrete realization and recognition are in the companion
`SourceRecognitionCoreExtension` module.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
variable {G : Type*} [Group G]

/-- The normalized extension relations of the second exceptional parabolic. -/
structure CoreExtensionRelations (x y z a b T C : G) : Prop extends
    ThreeInvolutionFourCommutators.Relations x y z a b where
  T_sq : T ^ 2 = a * b
  C_cube : C ^ 3 = 1
  TC_sq : (T * C) ^ 2 = 1
  Tx : T * x * T⁻¹ = x
  Ty : T * y * T⁻¹ = z
  Tz : T * z * T⁻¹ = y
  Cx : C * x * C⁻¹ = y
  Cy : C * y * C⁻¹ = z
  Cz : C * z * C⁻¹ = x

private theorem card_le_of_generates [Finite G] {x y z a b T C : G}
    (r : CoreExtensionRelations x y z a b T C)
    (hgen : closure ({x,y,z,T,C} : Set G) = ⊤) : Nat.card G ≤ 192 := by
  classical
  let Q := closure ({x,y,z} : Set G)
  have hx : x ∈ Q := subset_closure (by simp)
  have hy : y ∈ Q := subset_closure (by simp)
  have hz : z ∈ Q := subset_closure (by simp)
  have ha : a ∈ Q := r.xy ▸ (show ⁅x,y⁆ ∈ Q from
    Q.mul_mem (Q.mul_mem (Q.mul_mem hx hy) (Q.inv_mem hx)) (Q.inv_mem hy))
  have hb : b ∈ Q := r.xz ▸ (show ⁅x,z⁆ ∈ Q from
    Q.mul_mem (Q.mul_mem (Q.mul_mem hx hz) (Q.inv_mem hx)) (Q.inv_mem hz))
  have hT : T ∈ normalizer Q := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton]
    change closure ({T * x * T⁻¹, T * y * T⁻¹, T * z * T⁻¹} : Set G) =
      closure ({x,y,z} : Set G)
    rw [r.Tx, r.Ty, r.Tz]
    apply congrArg (closure : Set G → Subgroup G)
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hC : C ∈ normalizer Q := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton]
    change closure ({C * x * C⁻¹, C * y * C⁻¹, C * z * C⁻¹} : Set G) =
      closure ({x,y,z} : Set G)
    rw [r.Cx, r.Cy, r.Cz]
    apply congrArg (closure : Set G → Subgroup G)
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hN : normalizer (Q : Set G) = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (closure_le _).mpr
    rintro w (rfl | rfl | rfl | rfl | rfl)
    · exact Q.le_normalizer hx
    · exact Q.le_normalizer hy
    · exact Q.le_normalizer hz
    · exact hT
    · exact hC
  let _ : Q.Normal := normalizer_eq_top_iff.mp hN
  let f := QuotientGroup.mk' Q
  have hfx : f x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
  have hfy : f y = 1 := (QuotientGroup.eq_one_iff _).mpr hy
  have hfz : f z = 1 := (QuotientGroup.eq_one_iff _).mpr hz
  have hfa : f a = 1 := (QuotientGroup.eq_one_iff _).mpr ha
  have hfb : f b = 1 := (QuotientGroup.eq_one_iff _).mpr hb
  have hfT : f T ^ 2 = 1 := by rw [← map_pow, r.T_sq, map_mul, hfa, hfb, one_mul]
  have hfTC : f (T * C) ^ 2 = 1 := by rw [← map_pow, r.TC_sq, map_one]
  have hprod : (f T * f (T * C)) ^ 3 = 1 := by
    have hh : f T * f (T * C) = f C := by
      rw [map_mul, ← mul_assoc, ← pow_two, hfT, one_mul]
    rw [hh, ← map_pow, r.C_cube, map_one]
  have hgen' : closure ({f (T * C), f T} : Set (G ⧸ Q)) = ⊤ := by
    apply top_unique
    rw [← Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective Q), ← hgen,
      MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro w ⟨v, hv, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with hx' | hy' | hz' | hT' | hC'
    · rw [hx', hfx]; exact one_mem _
    · rw [hy', hfy]; exact one_mem _
    · rw [hz', hfz]; exact one_mem _
    · rw [hT']; exact subset_closure (by simp)
    · rw [hC']
      have hh : f C = (f T)⁻¹ * f (T * C) := by simp
      rw [hh]
      exact mul_mem (inv_mem (subset_closure (by simp))) (subset_closure (by simp))
  have hcard := (closure_pair_finite_card_le_of_involutions (by decide : 0 < 3)
    (f (T * C)) (f T) hfTC hfT hprod).2
  rw [hgen', card_top] at hcard
  rw [card_eq_card_quotient_mul_card_subgroup Q, r.toRelations.card]
  omega

/-- The order-thirty-two core and its dihedral quotient bound the generated
finite extension by 192. -/
theorem CoreExtensionRelations.card_le [Finite G] {x y z a b T C : G}
    (r : CoreExtensionRelations x y z a b T C) :
    Nat.card (closure ({x,y,z,T,C} : Set G)) ≤ 192 := by
  let H := closure ({x,y,z,T,C} : Set G)
  have hx : x ∈ H := subset_closure (by simp)
  have hy : y ∈ H := subset_closure (by simp)
  have hz : z ∈ H := subset_closure (by simp)
  have ha : a ∈ H := r.xy ▸ (show ⁅x,y⁆ ∈ H from
    H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy))
  have hb : b ∈ H := r.xz ▸ (show ⁅x,z⁆ ∈ H from
    H.mul_mem (H.mul_mem (H.mul_mem hx hz) (H.inv_mem hx)) (H.inv_mem hz))
  let xx : H := ⟨x,hx⟩
  let yy : H := ⟨y,hy⟩
  let zz : H := ⟨z,hz⟩
  let aa : H := ⟨a,ha⟩
  let bb : H := ⟨b,hb⟩
  let tt : H := ⟨T,subset_closure (by simp)⟩
  let cc : H := ⟨C,subset_closure (by simp)⟩
  have rr : CoreExtensionRelations xx yy zz aa bb tt cc := {
    x_sq := Subtype.ext r.x_sq
    y_sq := Subtype.ext r.y_sq
    z_sq := Subtype.ext r.z_sq
    a_order := (orderOf_coe aa).symm.trans r.a_order
    b_order := (orderOf_coe bb).symm.trans r.b_order
    a_ne_b := fun he => r.a_ne_b (congrArg Subtype.val he)
    xy := Subtype.ext r.xy
    xz := Subtype.ext r.xz
    yz := Subtype.ext r.yz
    bx := Subtype.ext r.bx.eq
    by_ := Subtype.ext r.by_.eq
    bz := Subtype.ext r.bz.eq
    T_sq := Subtype.ext r.T_sq
    C_cube := Subtype.ext r.C_cube
    TC_sq := Subtype.ext r.TC_sq
    Tx := Subtype.ext r.Tx
    Ty := Subtype.ext r.Ty
    Tz := Subtype.ext r.Tz
    Cx := Subtype.ext r.Cx
    Cy := Subtype.ext r.Cy
    Cz := Subtype.ext r.Cz }
  apply card_le_of_generates rr
  apply map_injective (f := H.subtype) Subtype.val_injective
  rw [← MonoidHom.range_eq_map, H.range_subtype, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
