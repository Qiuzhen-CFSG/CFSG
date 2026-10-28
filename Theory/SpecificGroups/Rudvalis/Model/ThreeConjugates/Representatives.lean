module

public import Theory.SpecificGroups.Rudvalis.Model.FivePointBase
public import Mathlib.Data.Fin.VecNotation

/-!
# Three conjugates of the two marked Rudvalis involutions

For each of `a` and `b²`, its conjugates by `(a*b)⁻¹` and `(a*b)⁻²`
recover the original ATLAS generators. The recovery words have lengths
20, 38 and 34. Their equations are checked on the certified five-point
base of the actual degree-4060 model, then subgroup membership gives generation.

Source: Revin–Zavarnitsine, arXiv:2505.05173v2, Theorem 1, citing
Di Martino–Pellegrini–Zalesskii, Theorem 3.1. The original permutation
attribution and inverse point-action convention are in `Model.PermutationData`.
These marked cases do not by themselves assert coverage of all involutions.
-/

namespace Rudvalis
open Subgroup

namespace ThreeConjugates

private def triple (t : Model) : Fin 3 → Model :=
  ![t, (a * b)⁻¹ * t * (a * b), ((a * b)^2)⁻¹ * t * ((a * b)^2)]

private def word (t : Model) (w : List (Fin 3)) : Model :=
  (w.map (triple t)).prod

private def recoverB : List (Fin 3) :=
  [1, 0, 1, 2, 0, 2, 0, 1, 2, 0, 2, 0, 2, 1, 0, 2, 0, 2, 0, 2]

private def squareRecoverA : List (Fin 3) :=
  [0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 1, 2, 0, 1, 2, 0, 1, 0,
   1, 0, 1, 2, 0, 1, 2, 1, 2, 0, 1, 2, 1, 0, 2, 1, 0, 1, 2]

private def squareRecoverB : List (Fin 3) :=
  [2, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0,
   2, 1, 0, 2, 0, 1, 0, 2, 1, 2, 1, 0, 1, 2, 0, 2, 1]

set_option maxRecDepth 3000 in
private theorem recoverB_eq : word a recoverB = b := by
  apply eq_of_smul_first_five
  decide +kernel

set_option maxRecDepth 3000 in
private theorem squareRecoverA_eq : word (b^2) squareRecoverA = a := by
  apply eq_of_smul_first_five
  decide +kernel

set_option maxRecDepth 3000 in
private theorem squareRecoverB_eq : word (b^2) squareRecoverB = b := by
  apply eq_of_smul_first_five
  decide +kernel

private theorem word_mem (t : Model) (w : List (Fin 3)) :
    word t w ∈ zpowers t ⊔ zpowers ((a*b)⁻¹*t*(a*b)) ⊔
      zpowers (((a*b)^2)⁻¹*t*((a*b)^2)) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  rcases i with ⟨i, hi⟩
  have he : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases he with rfl | rfl | rfl
  · exact mem_sup_left (mem_sup_left (mem_zpowers t))
  · exact mem_sup_left (mem_sup_right (mem_zpowers _))
  · exact mem_sup_right (mem_zpowers _)

end ThreeConjugates

/-- Three explicit conjugates of `a` recover both actual standard generators. -/
public theorem standard_three_generate :
    zpowers a ⊔ zpowers ((a*b)⁻¹*a*(a*b)) ⊔
      zpowers (((a*b)^2)⁻¹*a*((a*b)^2)) = ⊤ := by
  apply eq_top_of_a_mem_of_b_mem
  · exact mem_sup_left (mem_sup_left (mem_zpowers a))
  · have h := ThreeConjugates.word_mem a ThreeConjugates.recoverB
    rwa [ThreeConjugates.recoverB_eq] at h

/-- Three explicit conjugates of `b²` recover both actual standard generators. -/
public theorem square_three_generate :
    zpowers (b^2) ⊔ zpowers ((a*b)⁻¹*(b^2)*(a*b)) ⊔
      zpowers (((a*b)^2)⁻¹*(b^2)*((a*b)^2)) = ⊤ := by
  apply eq_top_of_a_mem_of_b_mem
  · have h := ThreeConjugates.word_mem (b^2) ThreeConjugates.squareRecoverA
    rwa [ThreeConjugates.squareRecoverA_eq] at h
  · have h := ThreeConjugates.word_mem (b^2) ThreeConjugates.squareRecoverB
    rwa [ThreeConjugates.squareRecoverB_eq] at h

end Rudvalis
