module
public import Theory.SpecificGroups.SL2.SylowBorelSeparation
public import BenderSuzuki.Converse.PSL2

/-!
# Involutions exchanging binary SL₂ Borel cosets

For a matrix outside the upper Borel, conjugate the Weyl involution by the
upper transvection with parameter a/c. Its product with the matrix is upper
triangular. Sylow conjugacy gives the same coset exchange for every Sylow
normalizer, including the field of order two. No action is replaced by a
permutation-group tag.

The actual graph lift is in DGS85/CommutingTrivial/LocalExchange. Source:
DGS, *Groups and Graphs* (1985), the exchange in 9.2, printed p.142.
-/

open Subgroup Matrix
open scoped MatrixGroups
public section
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [CharP F 2]

private theorem standard_coset_exchange (g : SL(2,F)) :
    ∃ t : SL(2,F), t * t = 1 ∧ t * g ∈ rankOneBorel F := by
  by_cases hg : g ∈ rankOneBorel F
  · exact ⟨1, one_mul _, by simpa using hg⟩
  have hc : g.val 1 0 ≠ 0 := fun he => hg ((mem_rankOneBorel_iff g).mpr he)
  let x := g.val 0 0 / g.val 1 0
  let u := transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one x
  let t := u * BenderSuzuki.Converse.weyl F * u⁻¹
  refine ⟨t, ?_, ?_⟩
  · dsimp [t]
    calc
      _ = u * (BenderSuzuki.Converse.weyl F * BenderSuzuki.Converse.weyl F) * u⁻¹ := by group
      _ = 1 := by rw [BenderSuzuki.Converse.weyl_sq]; group
  · rw [mem_rankOneBorel_iff]
    change (((u.val * (BenderSuzuki.Converse.weyl F).val) * u⁻¹.val) * g.val) 1 0 = 0
    simp [u, x, mul_apply, Fin.sum_univ_two, transvection_coe, adjugate_fin_two,
      BenderSuzuki.Converse.weyl, hc]

/-- Every coset of a binary SL₂ Sylow normalizer contains an element whose
square is one; its left multiplication exchanges that coset with the base. -/
theorem sylow_coset_exchange (S : Sylow 2 SL(2,F)) [Finite F] (g : SL(2,F)) :
    ∃ t : SL(2,F), t * t = 1 ∧ t * g ∈ normalizer (S : Set SL(2,F)) := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq SL(2,F) S (upperUnipotentSylow F 2)
  let c := MulAut.conj a
  have hS : (S : Subgroup SL(2,F)).map c.toMonoidHom = upperUnipotent F := by
    change ((a • S : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) = _
    rw [ha]
    rfl
  have hN : (normalizer (S : Set SL(2,F))).map c.toMonoidHom = rankOneBorel F := by
    calc
      _ = normalizer ((S : Subgroup SL(2,F)).map c.toMonoidHom : Set SL(2,F)) :=
        map_equiv_normalizer_eq (S : Subgroup SL(2,F)) c
      _ = rankOneBorel F := by rw [hS]
  obtain ⟨t, ht, htg⟩ := standard_coset_exchange (c g)
  refine ⟨c.symm t, ?_, ?_⟩
  · rw [← map_mul, ht, map_one]
  · rw [← hN] at htg
    obtain ⟨b, hb, he⟩ := htg
    change c b = t * c g at he
    have hh : b = c.symm t * g := by
      apply c.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using he
    exact hh ▸ hb
end Matrix.SpecialLinearGroup

