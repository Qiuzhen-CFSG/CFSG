module
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Fixed centralizers under replacement modulo a normal subgroup

Let U be an abelian normal subgroup contained in N. If a replacement D lies
in AU and AN is contained in DN, then C_U(D)=C_U(D∩N) implies
C_U(A)=C_U(A∩N). The proof decomposes elements of AU and DN, using that U
centralizes each of its own elements. No quadraticity of A is inferred.

This is the replacement transport used for the uniform fixed-space clause of
Aschbacher--Smith 15.1.12(2), and its application in 15.2.9--11.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A replacement inside AU with the same image modulo N transfers the fixed
centralizer identity back to A, provided U is abelian and contained in N. -/
theorem fixed_centralizer_of_replacement (U N A D : Subgroup G)
    [U.Normal] [N.Normal] [IsMulCommutative U]
    (hUN : U ≤ N) (hD : D ≤ A ⊔ U) (hA : A ≤ D ⊔ N)
    (hfix : U ⊓ centralizer (D : Set G) = U ⊓ centralizer (D ⊓ N : Subgroup G)) :
    U ⊓ centralizer (A : Set G) = U ⊓ centralizer (A ⊓ N : Subgroup G) := by
  apply le_antisymm (inf_le_inf_left U (centralizer_le inf_le_left))
  intro v hv
  let C := centralizer ({v} : Set G)
  have hUC : U ≤ C := by
    intro u hu
    rw [mem_centralizer_iff]
    intro w hw
    have hwv : w = v := Set.mem_singleton_iff.mp hw
    subst w
    exact setLike_mul_comm hv.1 hu
  have hBC : A ⊓ N ≤ C := by
    intro b hb
    rw [mem_centralizer_iff]
    intro w hw
    have hwv : w = v := Set.mem_singleton_iff.mp hw
    subst w
    exact (hv.2 b hb).symm
  have hNC : N ⊓ (A ⊔ U) ≤ C := by
    rintro n ⟨hn, hna⟩
    obtain ⟨a, ha, u, hu, rfl⟩ := mem_sup_of_normal_right.mp hna
    have han : a ∈ N := by
      have hh := N.mul_mem hn (N.inv_mem (hUN hu))
      simpa only [mul_inv_cancel_right] using hh
    exact C.mul_mem (hBC ⟨ha, han⟩) (hUC hu)
  have hDC : D ≤ C := by
    have hd : D ⊓ N ≤ C := fun d hd => hNC ⟨hd.2, hD hd.1⟩
    have hvd : v ∈ U ⊓ centralizer (D ⊓ N : Subgroup G) := by
      refine ⟨hv.1, ?_⟩
      intro d hd'
      exact ((hd hd') v (Set.mem_singleton v)).symm
    rw [← hfix] at hvd
    intro d hd'
    rw [mem_centralizer_iff]
    intro w hw
    have hwv : w = v := Set.mem_singleton_iff.mp hw
    subst w
    exact (hvd.2 d hd').symm
  refine ⟨hv.1, ?_⟩
  intro a ha
  obtain ⟨d, hd, n, hn, he⟩ := mem_sup_of_normal_right.mp (hA ha)
  have hna : n ∈ A ⊔ U := by
    have hh : d⁻¹ * a ∈ A ⊔ U :=
      (A ⊔ U).mul_mem ((A ⊔ U).inv_mem (hD hd)) ((le_sup_left : A ≤ A ⊔ U) ha)
    rw [← he, inv_mul_cancel_left] at hh
    exact hh
  have hac : a ∈ C := he ▸ C.mul_mem (hDC hd) (hNC ⟨hn, hna⟩)
  exact (hac v (Set.mem_singleton v)).symm
end Theory.GroupTheory
