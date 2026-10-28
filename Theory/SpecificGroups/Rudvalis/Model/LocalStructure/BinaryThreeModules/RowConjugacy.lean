module

public import Theory.SpecificGroups.Rudvalis.Model.LocalStructure.BinaryThreeModules.ElementarySixtyFour
public import Theory.SpecificGroups.Rudvalis.Model.FivePointBase
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder.Maps

/-!
# Conjugacy of the four native Rudvalis elementary sixty-four rows

The first two generators of the certified Sylow subgroup conjugate row one
onto row zero, row two onto row one, and row three onto row zero. Each
identity is checked on the native five-point base, with a permutation of all
64 displayed generators. Composing the first two transports places every
row in row zero.

This supplies the concrete row transport for the elementary-subgroup
inspection in Aschbacher--Smith 4.4.3, printed pp.622--623; see also
GLS3 Table 5.3r, printed p.279. The finite point-action identities are the
proof; no external conjugacy computation is assumed.
-/

public noncomputable section
set_option Elab.async false
set_option maxRecDepth 30000
namespace Rudvalis.BinaryThreeModules.ElementarySixtyFour

open Rudvalis Subgroup
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder

private def rowOneAction : Fin 64 → Fin 64 := ![0,1,3,2,60,42,48,38,36,10,9,33,12,63,50,15,51,16,21,40,19,62,45,22,25,46,39,28,57,26,31,56,53,43,59,37,41,34,52,55,61,54,32,35,58,44,47,49,23,4,6,18,5,20,17,7,8,30,27,13,29,11,14,24]

private theorem rowOne_conj (c : Fin 64) :
    candidateGenerator 0 * candidateNormalForm (rowIndex 1 c) =
      candidateNormalForm (rowIndex 0 (rowOneAction c)) * candidateGenerator 0 := by
  apply Rudvalis.eq_of_smul_first_five
  intro i
  simp only [mul_smul, generator_smul, normal_smul]
  revert c i
  apply Rudvalis.OrderCertificate.allFin₂
  decide +kernel

private theorem rowOneAction_surjective : Function.Surjective rowOneAction := by
  decide +kernel

private def rowTwoAction : Fin 64 → Fin 64 := ![0,1,2,3,58,63,60,57,10,48,53,9,54,15,12,51,30,27,32,33,47,46,24,29,28,26,20,17,18,23,40,43,36,22,39,16,11,35,13,34,50,55,52,49,56,61,62,59,42,21,8,44,45,14,19,41,31,7,4,37,38,5,6,25]

private theorem rowTwo_conj (c : Fin 64) :
    candidateGenerator 1 * candidateNormalForm (rowIndex 2 c) =
      candidateNormalForm (rowIndex 1 (rowTwoAction c)) * candidateGenerator 1 := by
  apply Rudvalis.eq_of_smul_first_five
  intro i
  simp only [mul_smul, generator_smul, normal_smul]
  revert c i
  apply Rudvalis.OrderCertificate.allFin₂
  decide +kernel

private theorem rowTwoAction_surjective : Function.Surjective rowTwoAction := by
  decide +kernel

private def rowThreeAction : Fin 64 → Fin 64 := ![0,1,2,3,11,14,13,8,10,4,6,9,7,15,12,5,39,35,28,25,26,31,41,45,22,19,37,33,43,47,16,21,61,55,57,51,63,53,59,49,17,20,23,18,27,30,29,24,54,50,52,48,56,60,58,62,32,36,34,38,46,42,44,40]

private theorem rowThree_conj (c : Fin 64) :
    candidateGenerator 1 * candidateNormalForm (rowIndex 3 c) =
      candidateNormalForm (rowIndex 0 (rowThreeAction c)) * candidateGenerator 1 := by
  apply Rudvalis.eq_of_smul_first_five
  intro i
  simp only [mul_smul, generator_smul, normal_smul]
  revert c i
  apply Rudvalis.OrderCertificate.allFin₂
  decide +kernel

private theorem rowThreeAction_surjective : Function.Surjective rowThreeAction := by
  decide +kernel

private theorem map_row_eq (j k : Fin 4) (g : Model) (σ : Fin 64 → Fin 64)
    (hs : Function.Surjective σ)
    (hc : ∀ c, g * candidateNormalForm (rowIndex j c) =
      candidateNormalForm (rowIndex k (σ c)) * g) :
    (row j).map (MulAut.conj g).toMonoidHom = row k := by
  have hconj (c : Fin 64) : (MulAut.conj g).toMonoidHom
      (candidateNormalForm (rowIndex j c)) =
        candidateNormalForm (rowIndex k (σ c)) := by
    change g * candidateNormalForm (rowIndex j c) * g⁻¹ = _
    have hh := congrArg (fun z : Model => z * g⁻¹) (hc c)
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hh
  apply le_antisymm
  · apply (map_le_iff_le_comap).2
    apply (closure_le _).2
    rintro x ⟨c,rfl⟩
    change (MulAut.conj g).toMonoidHom (candidateNormalForm (rowIndex j c)) ∈ row k
    rw [hconj]
    exact subset_closure (Set.mem_range_self _)
  · apply (closure_le _).2
    rintro x ⟨c,rfl⟩
    obtain ⟨d,rfl⟩ := hs c
    change candidateNormalForm (rowIndex k (σ d)) ∈ _
    rw [←hconj]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom
      (subset_closure (Set.mem_range_self d))

private theorem rowOne_map :
    (row 1).map (MulAut.conj (candidateGenerator 0)).toMonoidHom = row 0 :=
  map_row_eq 1 0 _ _ rowOneAction_surjective rowOne_conj

private theorem rowTwo_map :
    (row 2).map (MulAut.conj (candidateGenerator 1)).toMonoidHom = row 1 :=
  map_row_eq 2 1 _ _ rowTwoAction_surjective rowTwo_conj

private theorem rowThree_map :
    (row 3).map (MulAut.conj (candidateGenerator 1)).toMonoidHom = row 0 :=
  map_row_eq 3 0 _ _ rowThreeAction_surjective rowThree_conj

/-- Every certified native elementary sixty-four row is conjugate to row zero.
The witnesses are the identity, the first Sylow generator, the product of
the first two Sylow generators, and the second Sylow generator. -/
public theorem exists_row_conjugate_zero (j : Fin 4) :
    ∃ g : Model, (row j).map (MulAut.conj g).toMonoidHom = row 0 := by
  fin_cases j
  · refine ⟨1, ?_⟩
    have hid : (MulAut.conj (1 : Model)).toMonoidHom = MonoidHom.id Model := by
      ext x
      simp
    rw [hid]
    exact map_id _
  · exact ⟨candidateGenerator 0, rowOne_map⟩
  · refine ⟨candidateGenerator 0 * candidateGenerator 1, ?_⟩
    change (row 2).map
      (MulAut.conj (candidateGenerator 0 * candidateGenerator 1)).toMonoidHom = row 0
    have hmap : (MulAut.conj (candidateGenerator 0 * candidateGenerator 1)).toMonoidHom =
        (MulAut.conj (candidateGenerator 0)).toMonoidHom.comp
          (MulAut.conj (candidateGenerator 1)).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, mul_inv_rev, mul_assoc]
    rw [hmap, ←map_map, rowTwo_map, rowOne_map]
  · exact ⟨candidateGenerator 1, rowThree_map⟩

end Rudvalis.BinaryThreeModules.ElementarySixtyFour
