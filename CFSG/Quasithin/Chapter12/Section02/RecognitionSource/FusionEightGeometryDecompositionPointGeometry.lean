module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryDecompositionCocycles
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryModuleSupplement
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.Representation.BinaryPermutation.EightPointSylow

/-!
# Marked point-Sylow geometry in the seven-dimensional A₈ core

NoEscape makes L ∩ C_G(v) normal in C_G(v). Restrict the supplied Sylow
there and map it through the literal two-core quotient and A₈ marking.
Surjectivity onto the weight-two stabilizer follows from the intertwining
identity. Its full fixed vectors have even augmentation by EightPointSylow.

The independently proved point-Sylow supplement yields the join inside T.
The last theorem applies both facts to the corrected displacement-cocycle
consumer. The comparison of the L ∩ C_T(v) and C_T(v) fixed spaces remains
explicit; it must account for the outer action on the seven-dimensional core.

Source: Aschbacher--Smith, 12.2.16, printed p.800, corrected point-fixed
supplement argument and the full permutation module of B.3.1.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open BinaryPermutation Representation
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
namespace AlternatingEightFusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable (C : AlternatingEightFusion T L V)

omit [Finite G] in
/-- Fixed vectors for the literal quotient marking are precisely centralized vectors. -/
theorem componentProjection_fixes_iff (l : L) (w : V) :
    alternatingCoreRepresentation (Fin 8) (C.componentProjection l)
      (C.vectorEquiv w).toAdd = (C.vectorEquiv w).toAdd ↔
      (l : G) ∈ centralizer ({(w : G)} : Set G) := by
  have hi := C.intertwines l w
  change ((C.vectorEquiv.symm (Multiplicative.ofAdd
    (alternatingCoreRepresentation (Fin 8) (C.componentProjection l)
      (C.vectorEquiv w).toAdd))) : G) = (l : G) * w * (l : G)⁻¹ at hi
  constructor
  · intro he
    change ((C.vectorEquiv.symm (Multiplicative.ofAdd
      (alternatingCoreRepresentation (Fin 8) (C.componentProjection l)
        (C.vectorEquiv w).toAdd))) : G) = (l : G) * w * (l : G)⁻¹ at hi
    rw [he] at hi
    simp only [ofAdd_toAdd, C.vectorEquiv.symm_apply_apply] at hi
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hi.symm)
  · intro he
    apply Multiplicative.ofAdd.injective
    apply C.vectorEquiv.symm.injective
    apply Subtype.ext
    rw [hi]
    simp only [ofAdd_toAdd, C.vectorEquiv.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp he)

/-- The actual component image is a Sylow of the marked weight-two stabilizer. -/
theorem pointComponentImage_is_sylow (hnone : NoEscape L V) :
    ∃ P : Sylow 2 (EightPointSylow.stabilizer (C.vectorEquiv C.v).toAdd.val),
      (P : Subgroup _).map (EightPointSylow.stabilizer
        (C.vectorEquiv C.v).toAdd.val).subtype = C.pointComponentImage := by
  let K := centralizer ({(C.v : G)} : Set G)
  let E := L.subgroupOf K
  have hv : (C.v : G) ≠ 1 := by
    intro he
    have he' : C.v = 1 := Subtype.ext he
    have hw := C.weight_two
    rw [he', map_one] at hw
    norm_num at hw
  let : E.Normal := normal_subgroupOf_of_le_normalizer
    (hnone C.v C.v.property hv)
  obtain ⟨Q,hQ⟩ := C.sylow.exists_subgroupOf_eq_of_normal E
  let f : E →* L := (K.subtype.comp E.subtype).codRestrict L (fun x => x.property)
  let S := EightPointSylow.stabilizer (C.vectorEquiv C.v).toAdd.val
  have hfix (x : E) : C.componentProjection (f x) ∈ S := by
    change alternatingRepresentation (Fin 8) (C.componentProjection (f x))
      (C.vectorEquiv C.v).toAdd.val = (C.vectorEquiv C.v).toAdd.val
    exact congrArg (fun w : core (Fin 8) => w.val)
      ((C.componentProjection_fixes_iff (f x) C.v).mpr x.val.property)
  let q : E →* S := (C.componentProjection.comp f).codRestrict S hfix
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨l,hl⟩ := C.componentProjection_surjective a.val
    have hfix' : alternatingCoreRepresentation (Fin 8) (C.componentProjection l)
        (C.vectorEquiv C.v).toAdd = (C.vectorEquiv C.v).toAdd := by
      apply Subtype.ext
      rw [hl]
      exact a.property
    have hlK := (C.componentProjection_fixes_iff l C.v).mp hfix'
    refine ⟨⟨⟨l,hlK⟩,l.property⟩, ?_⟩
    exact Subtype.ext hl
  refine ⟨Q.mapSurjective hq, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, hQ]
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨f x, ?_, rfl⟩
    change ((x.val : K) : G) ∈ C.pointSylow
    change _ ∈ (T : Subgroup G) ⊓ centralizer ({(C.v : G)} : Set G)
    rw [← C.sylow_image]
    exact mem_map_of_mem K.subtype hx
  · rintro ⟨l,hl,rfl⟩
    have hl' : (l : G) ∈ C.pointSylow := hl
    have hlK : (l : G) ∈ K := hl'.2
    let x : E := ⟨⟨l,hlK⟩,l.property⟩
    have hx : x ∈ (C.sylow : Subgroup K).subgroupOf E := by
      have hm : (l : G) ∈ (C.sylow : Subgroup K).map K.subtype := C.sylow_image ▸ hl'
      obtain ⟨y,hy,he⟩ := hm
      have he' : y = x.val := Subtype.ext he
      change x.val ∈ (C.sylow : Subgroup K)
      rw [← he']
      exact hy
    exact ⟨x,hx,rfl⟩

/-- All full fixed vectors of the literal component image have even augmentation. -/
theorem pointComponentImage_fixed_le_core (hnone : NoEscape L V) :
    Representation.BinaryOffender.fixedSpace (alternatingRepresentation (Fin 8))
      C.pointComponentImage ≤ core (Fin 8) := by
  obtain ⟨P,hP⟩ := C.pointComponentImage_is_sylow hnone
  rw [← hP]
  exact EightPointSylow.sylow_fixed_le_core _ C.weight_two P

/-- The source supplement gives the join inside the original Sylow. -/
theorem pointSylow_supplement_inside
    {K : GroupClass} (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) :
    (T : Subgroup G) ≤ C.pointSylow ⊔ ((T : Subgroup G) ⊓ L) := by
  have hn : C.pointSylow ≤ normalizer (L : Set G) :=
    inf_le_left.trans (structural G T L h).1
  intro t ht
  have hm : t ∈ (L : Set G) * (C.pointSylow : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L C.pointSylow hn]
    exact C.pointSylow_supplement h D structural ht
  obtain ⟨l,hl,p,hp,he⟩ := hm
  have hlT : l ∈ (T : Subgroup G) := by
    have hmem := (T : Subgroup G).mul_mem ht ((T : Subgroup G).inv_mem hp.1)
    simpa only [← he, mul_inv_cancel_right] using hmem
  rw [← he]
  exact (C.pointSylow ⊔ ((T : Subgroup G) ⊓ L)).mul_mem
    (mem_sup_right ⟨hlT,hl⟩) (mem_sup_left hp)

/-- Discharge augmentation and the supplement in the literal cocycle consumer.
Only the moved bound and the comparison of point fixed spaces remain. -/
theorem pointFixed_conclusions_of_moved_and_fixed_comparison
    {K : GroupClass} (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V) (R : C.PointSpanModule)
    (hm : ⁅C.pointSpan, L⁆ ≤ V)
    (hfixed : V ⊓ centralizer (L ⊓ C.pointSylow : Set G) ≤ C.pointCore) :
    omegaCenterIn C.pointSylow = C.pointCore ⊔ C.pointFixed ∧
      C.pointFixed ≤ centralizer ((T : Subgroup G) : Set G) :=
  C.pointFixed_conclusions_of_moved_and_point_geometry D R hm
    (C.pointComponentImage_fixed_le_core hnone) hfixed
    (C.pointSylow_supplement_inside h D structural)

end AlternatingEightFusion
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
