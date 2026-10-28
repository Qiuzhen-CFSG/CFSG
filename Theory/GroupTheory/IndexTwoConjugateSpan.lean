module
public import Theory.GroupTheory.IndexTwoConjugatePair
public import Mathlib.GroupTheory.IndexNormal
/-!
# The conjugate span across an index-two subgroup

An index-two subgroup normalizing L makes the full group normalize the
span of L and its outside conjugate. If an abelian module is normalized
by the index-two subgroup and its outside conjugate fails to commute,
then the centralizer of any overgroup of that module lies in the index-two
subgroup. These statements retain the actual ambient conjugation maps.

Source: the generated-group argument in Aschbacher–Smith 2.4.7, p.541.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- An index-two group normalizes the span of the two conjugate blocks. -/
theorem index_two_normalizes_pair
    (B P L : Subgroup G) (hBP : B ≤ P) (hi : B.relIndex P = 2)
    (x : G) (hx : x ∈ P) (hxB : x ∉ B)
    (hBL : B ≤ normalizer (L : Set G)) :
    P ≤ normalizer ((L ⊔ L.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  let K := L ⊔ L.map (MulAut.conj x⁻¹).toMonoidHom
  have hPB : P ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hBP).mp (normal_of_index_eq_two hi)
  have hBLx := normalizes_conjugate_of_normalizes (hPB (P.inv_mem hx)) hBL
  have hBK : B ≤ normalizer (K : Set G) :=
    (le_inf hBL hBLx).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hs : (x⁻¹)^2 ∈ B := (B.subgroupOf P).sq_mem_of_index_two hi ⟨x⁻¹,P.inv_mem hx⟩
  have hxx : (L.conjBy x⁻¹).conjBy x⁻¹ = L := by
    rw [conjBy_conjBy,←pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp (hBL hs)
  have hxK : x⁻¹ ∈ normalizer (K : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change K.map (MulAut.conj x⁻¹).toMonoidHom = K
    rw [show K = L ⊔ L.map (MulAut.conj x⁻¹).toMonoidHom from rfl,Subgroup.map_sup]
    change L.conjBy x⁻¹ ⊔ (L.conjBy x⁻¹).conjBy x⁻¹ = L ⊔ L.conjBy x⁻¹
    rw [hxx,sup_comm]
  intro a ha
  by_cases haB : a ∈ B
  · exact hBK haB
  · have hax : a*x ∈ B := by
      apply ((B.subgroupOf P).mul_mem_iff_of_index_two hi
        (a := (⟨a,ha⟩:P)) (b := (⟨x,hx⟩:P))).mpr
      change a∈B ↔ x∈B
      simp only [haB,hxB]
    simpa only [mul_inv_cancel_right] using (normalizer (K : Set G)).mul_mem (hBK hax) hxK

/-- A noncommuting module prevents the outside coset from centralizing
any subgroup containing that module. -/
theorem index_two_centralizer_le
    (B P U R : Subgroup G) (hi : B.relIndex P = 2)
    (x : G) (hx : x ∈ P) (hxB : x ∉ B)
    (hBU : B ≤ normalizer (U : Set G)) (hUR : U ≤ R)
    (hU : U ≤ centralizer (U : Set G))
    (hnc : ¬ U.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U : Set G)) :
    P ⊓ centralizer (R : Set G) ≤ B := by
  rintro a ⟨ha,hac⟩
  by_contra haB
  have haU : a ∈ normalizer (U : Set G) :=
    (Subgroup.centralizer_le_normalizer _) (centralizer_le hUR hac)
  have hax : a*x ∈ B := by
    apply ((B.subgroupOf P).mul_mem_iff_of_index_two hi
      (a := (⟨a,ha⟩:P)) (b := (⟨x,hx⟩:P))).mpr
    change a∈B ↔ x∈B
    simp only [haB,hxB]
  have hxU : x ∈ normalizer (U : Set G) := by
    simpa only [inv_mul_cancel_left] using
      (normalizer (U : Set G)).mul_mem ((normalizer (U : Set G)).inv_mem haU) (hBU hax)
  apply hnc
  have he : U.map (MulAut.conj x⁻¹).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (U : Set G)).inv_mem hxU)
  exact he.le.trans hU

/-- Intersecting an index-two extension with a subgroup meeting the
outside coset retains index two. -/
theorem inf_relIndex_eq_two [Finite G]
    (S M P : Subgroup G) (hPM : P ≤ M) (hi : S.relIndex M = 2)
    (x : G) (hx : x ∈ P) (hxS : x ∉ S) :
    (S ⊓ P).relIndex P = 2 := by
  have hle : S.relIndex P ≤ 2 := by
    simpa only [hi] using relIndex_le_of_le_right (H := S) hPM (by omega : S.relIndex M ≠ 0)
  have hne : S.relIndex P ≠ 1 := fun h => hxS (relIndex_eq_one.mp h hx)
  have hn : S.relIndex P ≠ 0 := index_ne_zero_of_finite
  rw [inf_comm,inf_relIndex_left]
  omega
end Theory.GroupTheory
