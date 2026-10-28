module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Seven-elements in the two exceptional component models

The seven-cycle and multiplication by two on its letters are even permutations.
In a central extension with kernel of exponent three, cube a lift of the
seven-cycle. Cubing removes the central error in its conjugacy equation and
produces a nonidentity element whose seventh power is one. Thus both A₇ and
its actual central three-cover contain an element conjugate to its square.

This is the group-theoretic input to a symplectic dimension obstruction for the
inspection in Aschbacher–Smith, *The Classification of Quasithin Groups*, E.6.18,
printed p.252; Theorem C and Remark A.2.4, printed p.33.
-/

public section

open Subgroup Equiv Equiv.Perm
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.Symplectic

private def a : alternatingGroup (Fin 7) :=
  ⟨finRotate 7, by rw [mem_alternatingGroup]; decide +kernel⟩
private def b : alternatingGroup (Fin 7) :=
  ⟨(swap 1 2 * swap 2 4) * (swap 3 6 * swap 6 5), by
    simp [mem_alternatingGroup, Equiv.Perm.sign_mul]⟩

private theorem seven_permutations : a ^ 7 = 1 ∧ a ≠ 1 ∧ b * a * b⁻¹ = a ^ 2 := by
  decide +kernel

private theorem central_cube_eq {G : Type*} [Group G] {u v : G}
    (h : u * v⁻¹ ∈ center G) (hc : (u * v⁻¹) ^ 3 = 1) : u ^ 3 = v ^ 3 := by
  have hcomm : Commute (u * v⁻¹) v := (mem_center_iff.mp h v).symm
  have he := hcomm.mul_pow 3
  simpa [hc] using he

theorem square_conjugate_of_central_cubic_kernel {G : Type*} [Group G] (q : G →* alternatingGroup (Fin 7))
    (hq : Function.Surjective q)
    (hk : ∀ z, q z = 1 → z ∈ center G ∧ z ^ 3 = 1) :
    ∃ x y : G, x ^ 7 = 1 ∧ x ≠ 1 ∧ y * x * y⁻¹ = x ^ 2 := by
  obtain ⟨u, hu⟩ := hq a
  obtain ⟨v, hv⟩ := hq b
  have ha7 : a ^ 7 = 1 := seven_permutations.1
  have hab : b * a * b⁻¹ = a ^ 2 := seven_permutations.2.2
  have hu7 : (u ^ 7) ^ 3 = 1 := (hk (u ^ 7) (by simp [hu, ha7])).2
  have he : q ((v * u * v⁻¹) * (u ^ 2)⁻¹) = 1 := by simp [hu, hv, hab]
  have hc := central_cube_eq (hk _ he).1 (hk _ he).2
  refine ⟨u ^ 3, v, ?_, ?_, ?_⟩
  · simpa [← pow_mul, Nat.mul_comm] using hu7
  · intro h
    have ha3 := congrArg q h
    have han : a ^ 3 ≠ 1 := by decide +kernel
    exact han (by simpa [hu] using ha3)
  · simpa only [conj_pow, ← pow_mul, Nat.mul_comm] using hc

/-- The actual component models contain a nontrivial seven-element conjugate
 to its square. The central-cover proof uses its quotient map and center. -/
theorem seven_square_conjugate {G : Type*} [Group G] [Finite G]
    {L : Subgroup G} (hL : IsSeven L) :
    ∃ x y : L, x ^ 7 = 1 ∧ x ≠ 1 ∧ y * x * y⁻¹ = x ^ 2 := by
  rcases hL with ha | hc
  · obtain ⟨e⟩ := ha
    refine ⟨e.symm a, e.symm b, ?_, ?_, ?_⟩
    · rw [← map_pow, seven_permutations.1, map_one]
    · exact fun h => seven_permutations.2.1 (e.symm.map_eq_one_iff.mp h)
    · simpa only [map_mul, map_inv, map_pow] using
        congrArg e.symm seven_permutations.2.2
  · obtain ⟨_, ⟨ez⟩, ⟨e⟩⟩ := hc
    let q : L →* alternatingGroup (Fin 7) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (center L))
    apply square_conjugate_of_central_cubic_kernel q
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
    intro z hz
    have hz' : z ∈ center L := (QuotientGroup.eq_one_iff _).mp
      (e.map_eq_one_iff.mp hz)
    refine ⟨hz', ?_⟩
    have hc : Nat.card (center L) = 3 := by
      rw [Nat.card_congr ez.toEquiv]
      simp [Nat.card_eq_fintype_card]
    have hp : (⟨z, hz'⟩ : center L) ^ 3 = 1 := by
      rw [← hc]
      exact pow_card_eq_one'
    exact congrArg Subtype.val hp

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.Symplectic
