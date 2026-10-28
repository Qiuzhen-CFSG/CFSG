module
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction
/-!
# The Hall torus extension and every outside normalizing representative

If R≤T, B normalizes R, and T normalizes RB, their generated group is the
set product BT. When S has index two in T and normalizes RD, the group
RDDˣ is independent of the outside representative x. Intersecting with
the odd Hall torus B proves B=DDʸ for every y in N_T(B)−S.

Source: Aschbacher–Smith 2.4.8(5), printed p.530.
-/
public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

theorem torus_extension_set_product (R T B : Subgroup G) (hRT : R ≤ T)
    (hBR : B ≤ normalizer (R : Set G))
    (hTK : T ≤ normalizer ((R ⊔ B : Subgroup G) : Set G)) :
    ((T ⊔ B : Subgroup G) : Set G) = (B : Set G) * (T : Set G) := by
  have hJ : T ⊔ B = (R ⊔ B) ⊔ T := by
    apply le_antisymm (sup_le le_sup_right (le_sup_right.trans le_sup_left))
    exact sup_le (sup_le (hRT.trans le_sup_left) le_sup_right) le_sup_left
  apply Set.Subset.antisymm
  · intro z hz
    rw [hJ,coe_mul_of_right_le_normalizer_left _ _ hTK] at hz
    obtain ⟨k,hk,t,ht,rfl⟩ := hz
    rw [coe_mul_of_right_le_normalizer_left _ _ hBR] at hk
    obtain ⟨r,hr,b,hb,rfl⟩ := hk
    have hr' : b⁻¹*r*b ∈ R := by
      have hh := (mem_normalizer_iff.mp ((normalizer (R : Set G)).inv_mem (hBR hb)) r).mp hr
      simpa only [inv_inv] using hh
    refine ⟨b,hb,(b⁻¹*r*b)*t,T.mul_mem (hRT hr') ht,?_⟩
    group
  · rintro z ⟨b,hb,t,ht,rfl⟩
    exact (T ⊔ B).mul_mem (mem_sup_right hb) (mem_sup_left ht)

variable [Finite G]
theorem odd_joint_torus_pair_for_all
    (S T R D B : Subgroup G) (hST : S ≤ T) (hi : S.relIndex T = 2)
    (hR : IsPGroup 2 R) (hodd : Odd (Nat.card B)) (hDB : D ≤ B)
    (hTR : T ≤ normalizer (R : Set G)) (hBR : B ≤ normalizer (R : Set G))
    (hSA : S ≤ normalizer ((R ⊔ D : Subgroup G) : Set G))
    (x : G) (hxT : x ∈ T) (hxS : x ∉ S)
    (hpair : B = D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom)
    (hBD : B ≤ normalizer (D : Set G)) :
    ∀ y ∈ T, y ∉ S → y ∈ normalizer (B : Set G) →
      B = D ⊔ D.map (MulAut.conj y⁻¹).toMonoidHom := by
  intro y hyT hyS hyB
  have hxi : x⁻¹ ∉ S := fun h => hxS (by simpa only [inv_inv] using S.inv_mem h)
  have hyi : y⁻¹ ∉ S := fun h => hyS (by simpa only [inv_inv] using S.inv_mem h)
  have hh := index_two_conjugate_join_eq S T (R ⊔ D) hST hi hSA x⁻¹ y⁻¹
    (T.inv_mem hxT) hxi (T.inv_mem hyT) hyi
  have hxR : R.map (MulAut.conj x⁻¹).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (hTR (T.inv_mem hxT))
  have hyR : R.map (MulAut.conj y⁻¹).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (hTR (T.inv_mem hyT))
  rw [Subgroup.map_sup,Subgroup.map_sup,hxR,hyR] at hh
  have hxK : (R ⊔ D) ⊔ (R ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom) = R ⊔ B := by
    rw [hpair]
    rw [←sup_assoc,sup_eq_left.mpr (le_sup_left : R ≤ R ⊔ D)]
    simp only [sup_assoc]
  have hyK : (R ⊔ D) ⊔ (R ⊔ D.map (MulAut.conj y⁻¹).toMonoidHom) =
      (R ⊔ D) ⊔ D.map (MulAut.conj y⁻¹).toMonoidHom := by
    rw [←sup_assoc,sup_eq_left.mpr (le_sup_left : R ≤ R ⊔ D)]
  rw [hxK,hyK] at hh
  have hyEB : D.map (MulAut.conj y⁻¹).toMonoidHom ≤ B :=
    (map_mono hDB).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (B : Set G)).inv_mem hyB))
  have hyA : D.map (MulAut.conj y⁻¹).toMonoidHom ≤
      normalizer ((R ⊔ D : Subgroup G) : Set G) :=
    (le_inf (hyEB.trans hBR) (hyEB.trans hBD)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact (OddHall.hall_pair_generation R D (R ⊔ B) B hR hodd hDB le_sup_right
    (sup_le R.le_normalizer hBR) y⁻¹ ((normalizer (B : Set G)).inv_mem hyB)
    hyA hh).1
end Subgroup

