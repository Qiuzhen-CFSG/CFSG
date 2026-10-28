module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.NoncommPiCoprod
/-!
# Centers of products of commuting subgroups

The canonical product homomorphism remembers commutators with a single
factor. Therefore the preimage of the ambient center is contained in the
center of the external product. If the factors generate the group, a common
power identity on their centers holds on the ambient center as well.

This retains intersections between factors; no direct-product hypothesis
is imposed. It is used in the component-product step of Aschbacher–Smith
A.2.12, printed pp.36–37.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] {ι : Type*} [Fintype ι]
variable (H : ι → Subgroup G)
variable (hc : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)

theorem comap_center_noncommPiCoprod_le :
    (center G).comap (noncommPiCoprod hc) ≤ center (∀ i, H i) := by
  classical
  intro x hx
  apply mem_center_iff.mpr
  intro y
  funext i
  have he : ⁅x, Pi.mulSingle i (y i)⁆ = (Pi.mulSingle i (⁅x i, y i⁆ : H i) : ∀ j, H j) := by
    funext j
    by_cases hij : j = i
    · subst j
      simp [commutatorElement_def]
    · simp [commutatorElement_def, Pi.mulSingle_eq_of_ne hij]
  have hz := commutatorElement_eq_one_iff_mul_comm.mpr
    ((mem_center_iff.mp hx (noncommPiCoprod hc (Pi.mulSingle i (y i)))).symm)
  rw [← map_commutatorElement, he, noncommPiCoprod_mulSingle] at hz
  exact (commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext hz)).symm

include hc in
theorem center_pow_eq_one_of_iSup_eq_top (hgen : (⨆ i, H i) = ⊤) (p : ℕ)
    (hp : ∀ i, ∀ z : H i, z ∈ center (H i) → z ^ p = 1)
    (x : G) (hx : x ∈ center G) : x ^ p = 1 := by
  classical
  have hsur : Function.Surjective (noncommPiCoprod hc) := by
    apply MonoidHom.range_eq_top.mp
    rw [noncommPiCoprod_range, hgen]
  obtain ⟨y, rfl⟩ := hsur x
  have hy : y ∈ center (∀ i, H i) := comap_center_noncommPiCoprod_le H hc hx
  have hpw : y ^ p = 1 := by
    funext i
    apply hp i (y i)
    rw [Subgroup.center_pi] at hy
    exact hy i (Set.mem_univ i)
  rw [← map_pow, hpw, map_one]
end Subgroup
