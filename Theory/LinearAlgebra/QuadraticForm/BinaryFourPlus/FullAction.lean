module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Theory.GroupTheory.WreathTwoSylowMaximal
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# A criterion for the full binary plus orthogonal action

A nonabelian two-subgroup of S₃ wr C₂ has order eight and is therefore Sylow.
Sylow two-subgroups are maximal, so adjoining any subgroup whose order is
divisible by three gives the whole group. This retains the common two-subgroup
needed when an involution is moved by another two-element; arbitrary movement
inside an overgroup of S₃ × C₂ would not suffice.

Source: Aschbacher--Smith, 2.4.29, printed p.545, the order-72 action step.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace BinaryFourPlus

private theorem wreath_card : Nat.card Wreath = 72 :=
  (Nat.card_congr isometryEquivWreath.toEquiv).symm.trans card_isometrySubgroup

/-- A Sylow two-subgroup is maximal in the binary plus orthogonal group. -/
theorem sylow_two_isCoatom (S : Sylow 2 Wreath) : IsCoatom (S : Subgroup Wreath) := by
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let e := RegularWreathProduct.congr eSL (MulEquiv.refl C2)
  let P := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hh := (e.mapSubgroup.isCoatom_iff (P : Subgroup _)).mpr (wreath_two_sylow_isCoatom P)
  have he : (P : Subgroup _).map e.toMonoidHom = S := by
    change ((S : Subgroup Wreath).map e.symm.toMonoidHom).map e.toMonoidHom = _
    rw [map_map]
    have hc : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Wreath := by
      apply MonoidHom.ext
      intro x
      exact e.apply_symm_apply x
    rw [hc,map_id]
  rwa [show e.mapSubgroup (P : Subgroup _) = (P : Subgroup _).map e.toMonoidHom from rfl,he] at hh

private theorem sylow_card (S : Sylow 2 Wreath) : Nat.card S = 8 := by
  rw [Sylow.card_eq_multiplicity,wreath_card,show 72=2^3*9 by decide,
    Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣9)]

/-- A cubic together with noncommuting elements in one two-subgroup forces
all of the order-72 orthogonal group. -/
theorem eq_top_of_three_dvd_of_noncommuting_two_subgroup
    (J A : Subgroup Wreath) (hAJ : A ≤ J) (hA : IsPGroup 2 A)
    (h3 : 3 ∣ Nat.card J) (x u : A) (hne : x*u ≠ u*x) : J = ⊤ := by
  obtain ⟨S,hAS⟩ := hA.exists_le_sylow
  have hcS := sylow_card S
  have hd := card_dvd_of_le hAS
  rw [hcS] at hd
  have hcA : Nat.card A = 8 := by
    have hh := Nat.mem_divisors.mpr ⟨hd,by decide⟩
    have he : (8:ℕ).divisors = {1,2,4,8} := by decide
    rw [he] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with h1 | h2 | h4 | h8
    · have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp h1).1
      exact (hne (Subsingleton.elim _ _)).elim
    · let : IsCyclic A := isCyclic_of_prime_card h2
      exact (hne (mul_comm _ _)).elim
    · let : IsMulCommutative A := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p:=2) h4
      exact (hne (mul_comm _ _)).elim
    · exact h8
  have heq : A = (S : Subgroup Wreath) := eq_of_le_of_card_ge hAS (by rw [hcA,hcS])
  have hSJ : (S : Subgroup Wreath) ≤ J := heq ▸ hAJ
  apply (sylow_two_isCoatom S).lt_iff.mp
  refine lt_of_le_of_ne hSJ ?_
  intro he
  rw [← he,hcS] at h3
  norm_num at h3

end BinaryFourPlus
