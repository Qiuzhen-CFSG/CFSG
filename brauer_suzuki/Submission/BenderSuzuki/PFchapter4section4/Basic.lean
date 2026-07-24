/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.PFchapter4section3.Basic

namespace BenderSuzuki
namespace PFchapter4section4

open PFchapter1section1 PFAppendixIII
open PFchapter4section1
open PFchapter4section2
open PFchapter4section3

/-!
# Basic interfaces for Peterfalvi, Part II, Chapter IV, Section 4
-/

universe u v

public theorem section4LocalQuotient_kernel_le
    {G : Type*} [Group G]
    {P U N : Subgroup G}
    (hN : N = P ⊓ U) :
    N ≤ U := by
  rw [hN]
  exact inf_le_right

public theorem section4LocalQuotient_U_le_centralizer_P
    {G : Type*} [Group G]
    {P U : Subgroup G}
    (hU : U =
      (let C : Subgroup G := Subgroup.centralizer (P : Set G)
       (twoPrimeResidual C).map C.subtype)) :
    U ≤ Subgroup.centralizer (P : Set G) := by
  rw [hU]
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.2

public theorem section4LocalQuotient_normal
    {G : Type*} [Group G]
    {P U N : Subgroup G}
    (hU : U =
      (let C : Subgroup G := Subgroup.centralizer (P : Set G)
       (twoPrimeResidual C).map C.subtype))
    (hN : N = P ⊓ U) :
    (N.subgroupOf U).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (section4LocalQuotient_kernel_le hN)]
  intro n u hn hu
  rw [hN] at hn ⊢
  constructor
  · have huC : u ∈ Subgroup.centralizer (P : Set G) :=
      section4LocalQuotient_U_le_centralizer_P hU hu
    have hcomm : u * n = n * u :=
      ((Subgroup.mem_centralizer_iff.mp huC) n hn.1).symm
    have hconj : u * n * u⁻¹ = n := by
      calc
        u * n * u⁻¹ = n * u * u⁻¹ := by rw [hcomm, mul_assoc]
        _ = n := by simp
    simpa [hconj] using hn.1
  · exact U.mul_mem (U.mul_mem hu hn.2) (U.inv_mem hu)

end PFchapter4section4
end BenderSuzuki
