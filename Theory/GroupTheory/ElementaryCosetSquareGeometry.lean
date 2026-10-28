module

public import Theory.GroupTheory.ElementaryCosetSquareRoots

/-!
# Square geometry is constant on an elementary coset

Multiplying a normalizing element by an element of an abelian subgroup does
not change its centralizer in that subgroup. It also does not change whether
its square belongs to the subgroup. Thus the elementary-coset root counts
extend from one representative to the whole coset.

Source: the coset calculation in D. Parrott, *A characterization of the
Tits' simple group* (1972), printed p.682.
-/

open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

/-- The centralizer inside an abelian subgroup is constant on each coset. -/
public theorem inf_centralizer_singleton_mul_of_mem
    (F : Subgroup G) [IsMulCommutative F] (m q : G) (hq : q ∈ F) :
    F ⊓ centralizer ({m * q} : Set G) = F ⊓ centralizer ({m} : Set G) := by
  ext g
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hg, hc⟩
    have hgq : Commute g q := congrArg F.subtype
      (mul_comm (⟨g, hg⟩ : F) ⟨q, hq⟩)
    refine ⟨hg, mul_right_cancel (b := q) ?_⟩
    calc
      g * m * q = g * (m * q) := mul_assoc _ _ _
      _ = (m * q) * g := hc
      _ = m * g * q := by rw [mul_assoc, hgq.symm.eq, ← mul_assoc]
  · rintro ⟨hg, hc⟩
    have hgq : Commute g q := congrArg F.subtype
      (mul_comm (⟨g, hg⟩ : F) ⟨q, hq⟩)
    exact ⟨hg, ((show Commute g m from hc).mul_right hgq).eq⟩

/-- Square membership in a subgroup is constant on its normalizer cosets. -/
public theorem mul_sq_mem_iff_of_mem_normalizer
    (F : Subgroup G) (m : G) (hm : m ∈ normalizer (F : Set G))
    (q : G) (hq : q ∈ F) : (m * q) ^ 2 ∈ F ↔ m ^ 2 ∈ F := by
  have hh : (m⁻¹ * q * m) * q ∈ F :=
    F.mul_mem ((mem_normalizer_iff''.mp hm q).mp hq) hq
  have heq : (m * q) ^ 2 = m ^ 2 * ((m⁻¹ * q * m) * q) := by
    simp only [pow_two]
    group
  rw [heq]
  exact F.mul_mem_cancel_right hh

end Subgroup
