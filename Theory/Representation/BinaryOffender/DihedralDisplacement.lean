module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Theory.Representation.BinaryOffender.ConjugateMovedDimension
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.QuadraticConstituentStability

/-!
# Dihedral moved spaces and a single displacement

For the dihedral groups of order six or ten, two conjugates of any involution
are enough to generate the group. The conjugate-generation rank bound then
bounds the whole moved space by twice that involution's displacement rank.
Disjoint moved spaces also ensure that the rank of a product dominates the
rank of either component, by inclusion of their fixed kernels.

These estimates implement the transvection step in Aschbacher--Smith,
14.6.13, printed p.1031, independently of the critical-pair setup.
-/

public section

open Subgroup Representation Representation.BinaryOffender

namespace DihedralGroup

private theorem two_conjugates_generate_small {p : ℕ} (hp : p = 3 ∨ p = 5)
    (t : DihedralGroup p) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    Subgroup.closure (Set.range fun i : Fin 2 =>
      (![1, r 1] i) * t * (![1, r 1] i)⁻¹) = ⊤ := by
  have hw : ∀ x : DihedralGroup p, ∃ i : Fin p,
      x = (t * (r 1 * t * (r 1)⁻¹)) ^ (i : ℕ) ∨
      x = (t * (r 1 * t * (r 1)⁻¹)) ^ (i : ℕ) * t := by
    rcases hp with rfl | rfl
    · have h : ∀ t : DihedralGroup 3, t ≠ 1 → t ^ 2 = 1 →
          ∀ x : DihedralGroup 3, ∃ i : Fin 3,
            x = (t * (r 1 * t * (r 1)⁻¹)) ^ (i : ℕ) ∨
            x = (t * (r 1 * t * (r 1)⁻¹)) ^ (i : ℕ) * t := by decide
      exact h t ht ht2
    · have h : ∀ t : DihedralGroup 5, t ≠ 1 → t ^ 2 = 1 →
          ∀ x : DihedralGroup 5, ∃ i : Fin 5,
            x = (t * (r 1 * t * (r 1)⁻¹)) ^ (i : ℕ) ∨
            x = (t * (r 1 * t * (r 1)⁻¹)) ^ (i : ℕ) * t := by decide
      exact h t ht ht2
  let C := Subgroup.closure (Set.range fun i : Fin 2 =>
      (![1, r 1] i) * t * (![1, r 1] i)⁻¹)
  have h0 : t ∈ C := by
    have h := Subgroup.subset_closure (Set.mem_range_self (f := fun i : Fin 2 =>
      (![1, r 1] i) * t * (![1, r 1] i)⁻¹) 0)
    simpa using h
  have h1 : r 1 * t * (r 1)⁻¹ ∈ C := by
    exact Subgroup.subset_closure ⟨1, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨i, hi | hi⟩ := hw x
  · rw [hi]
    exact C.pow_mem (C.mul_mem h0 h1) _
  · rw [hi]
    exact C.mul_mem (C.pow_mem (C.mul_mem h0 h1) _) h0
end DihedralGroup

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

 theorem dihedral_moved_le_twice_displacement (ρ : Representation (ZMod 2) G V)
    {p : ℕ} (hp : p = 3 ∨ p = 5) (A : Subgroup G) (e : A ≃* DihedralGroup p)
    (t : A) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) := by
  rw [subspaceCommutator_top_eq_coinvariants]
  exact finrank_coinvariants_le_mul_displacement_of_equiv_conjugate_generation
    (ρ.comp A.subtype) e t ![1, DihedralGroup.r 1]
    (DihedralGroup.two_conjugates_generate_small hp (e t)
      (fun hh => ht (e.injective (hh.trans (map_one e).symm)))
      (by rw [← map_pow, ht2, map_one]))

 theorem displacement_left_le_of_disjoint_moved (ρ : Representation (ZMod 2) G V)
    (A B : Subgroup G) (hd : Disjoint (subspaceCommutator ρ ⊤ A)
      (subspaceCommutator ρ ⊤ B)) {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (ρ (a*b) - LinearMap.id)) := by
  have hker : LinearMap.ker (ρ (a*b) - LinearMap.id) ≤
      LinearMap.ker (ρ a - LinearMap.id) := by
    intro v hv
    have hv' : ρ a (ρ b v) = v := by
      simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero, map_mul, Module.End.mul_apply] using hv
    have hA : ρ a (ρ b v) - ρ b v ∈ subspaceCommutator ρ ⊤ A :=
      Submodule.subset_span ⟨a, ha, ρ b v, Submodule.mem_top, rfl⟩
    have hB : ρ a (ρ b v) - ρ b v ∈ subspaceCommutator ρ ⊤ B := by
      rw [hv']
      simpa only [neg_sub] using (subspaceCommutator ρ ⊤ B).neg_mem
        (Submodule.subset_span ⟨b, hb, v, Submodule.mem_top, rfl⟩)
    have hz := Submodule.disjoint_def.mp hd _ hA hB
    have hbv : ρ b v = v := by rw [hv'] at hz; exact (sub_eq_zero.mp hz).symm
    rw [hbv] at hv'
    exact sub_eq_zero.mpr hv'
  have hk := Submodule.finrank_mono hker
  have h1 := LinearMap.finrank_range_add_finrank_ker (ρ a - LinearMap.id)
  have h2 := LinearMap.finrank_range_add_finrank_ker (ρ (a*b) - LinearMap.id)
  omega
end Representation.BinaryOffender
