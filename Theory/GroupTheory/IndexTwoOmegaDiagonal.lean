module
public import Theory.GroupTheory.CharacteristicAbelianIndexTwoNorm
public import Stellmacher.OmegaOneCenterMap
public import Mathlib.GroupTheory.IndexNormal

/-!
# Central involutions from an index-two diagonal

An involution central in an index-two subgroup has a central diagonal
product with its outside conjugate whenever these two involutions commute.
The outside element exchanges the two factors because its square belongs
to the subgroup. This is the elementary source step in C.5.3.
-/

public section
open Subgroup Stellmacher
namespace Subgroup
variable {G : Type*} [Group G]

theorem indexTwo_diagonal_mem_omegaCenter (S T : Subgroup G) (hST : S ≤ T)
    (hi : S.relIndex T = 2) (t : G) (ht : t ∈ T) (htS : t ∉ S)
    (u : G) (hu : u ∈ omegaOneCenterAmbient S)
    (hc : Commute u (t*u*t⁻¹)) : u*(t*u*t⁻¹) ∈ omegaOneCenterAmbient T := by
  obtain ⟨huS,hu2,huC⟩ := (mem_omegaOneCenterAmbient_iff S u).mp hu
  let A := S.subgroupOf T
  let : A.Normal := normal_of_index_eq_two hi
  have hnormal : T ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST).mp inferInstance
  have hSS (s : G) (hs : s ∈ S) : t⁻¹*s*t ∈ S := by
    have he := mem_normalizer_iff.mp (hnormal (T.inv_mem ht)) s
    simpa only [inv_inv] using he.mp hs
  have hvS (s : G) (hs : s ∈ S) : Commute (t*u*t⁻¹) s := by
    have he := huC (t⁻¹*s*t) (hSS s hs)
    apply Eq.symm
    calc
      s*(t*u*t⁻¹) = t*((t⁻¹*s*t)*u)*t⁻¹ := by group
      _ = t*(u*(t⁻¹*s*t))*t⁻¹ := by rw [he]
      _ = (t*u*t⁻¹)*s := by group
  have hvT : t*(t*u*t⁻¹)*t⁻¹ = u := by
    have ht2 : t^2 ∈ S := A.sq_mem_of_index_two hi (⟨t,ht⟩ : T)
    have he := huC (t^2) ht2
    calc
      t*(t*u*t⁻¹)*t⁻¹ = t^2*u*(t^2)⁻¹ := by simp only [pow_two]; group
      _ = u := by rw [he]; group
  have hzT : u*(t*u*t⁻¹) ∈ T := T.mul_mem (hST huS)
    (T.mul_mem (T.mul_mem ht (hST huS)) (T.inv_mem ht))
  have hz : (⟨u*(t*u*t⁻¹),hzT⟩ : T) ∈ center T := by
    apply mem_center_of_commute_index_two A hi (⟨t,ht⟩ : T) htS
    · intro a ha
      apply (show Function.Injective (T.subtype) from T.subtype_injective)
      exact ((show Commute u (a : G) from (huC a ha).symm).mul_left (hvS a ha)).eq
    · apply (show Function.Injective (T.subtype) from T.subtype_injective)
      change u*(t*u*t⁻¹)*t = t*(u*(t*u*t⁻¹))
      have he : t*(u*(t*u*t⁻¹))*t⁻¹ = u*(t*u*t⁻¹) := by
        calc
          t*(u*(t*u*t⁻¹))*t⁻¹ = (t*u*t⁻¹)*(t*(t*u*t⁻¹)*t⁻¹) := by group
          _ = (t*u*t⁻¹)*u := by rw [hvT]
          _ = u*(t*u*t⁻¹) := hc.eq.symm
      exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  apply (mem_omegaOneCenterAmbient_iff T _).mpr
  refine ⟨hzT,?_,?_⟩
  · rw [hc.mul_pow,hu2]
    have hv2 : (t*u*t⁻¹)^2 = 1 := by
      have he := congrArg (MulAut.conj t) hu2
      simpa only [map_pow,map_one,MulAut.conj_apply] using he
    rw [hv2,one_mul]
  · intro s hs
    exact congrArg T.subtype (mem_center_iff.mp hz (⟨s,hs⟩ : T))

end Subgroup
