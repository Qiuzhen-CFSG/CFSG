module

public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.Representatives
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed

/-!
# Generation by the fifteen nonparabolic Tits representatives

For each representative with index at least three, two explicit words recover
Parrott's reflections `r1` and `r8` from the eight marked Sylow generators,
the representative, and its inverse. The thirty identities are checked on all
1600 points using the certified packed permutations. Transport into the actual
Atlas subgroup then puts both marked parabolics in the generated subgroup;
`ExceptionalParabolics.generate` proves that this subgroup is the whole group.

The words use Lean's left-action multiplication convention. The untrusted
`RepresentativeGeneration/source/check_words.py` reproduces the witness table
from GAP words, reversing their product order. The proof below checks every
identity independently with `decide +kernel`.

Source: Parrott (1972), §5, p.683, transcribed in
`refs/original/n-group-global/parrott-tits-presentation.md`. This is the generation
certificate for the explicit candidates in `Representatives`, used in the
Sylow-local coverage argument for Aschbacher–Smith, Theorem 0.1.2(1), printed
pp.3–4 and 481–482.
-/

namespace Tits.ConverseLocalCoverage

open Subgroup ExceptionalParabolics
open OuterOddSubgroups.OverlapCentralizers

/-- Row `i` concerns representative `i + 3`; the columns recover `r1` and `r8`.
Letters `0,...,7` denote `s1,...,s8`, and `8,9` denote the representative and
its reversed positive word, respectively. -/
private def recoveryWord : Fin 15 → Fin 2 → List (Fin 10) :=
  ![![[6, 8, 6, 9, 0], [7, 9, 1, 8, 7]],
    ![[6, 9, 6, 8, 0], [7, 8, 1, 9, 7]],
    ![[4, 4, 4, 8, 6, 2, 8, 0], [4, 4, 4, 8, 6, 2, 8, 0, 8, 4, 4, 4, 8, 6, 2, 8, 0]],
    ![[8, 5, 8, 7, 8, 7, 8, 5, 8, 7, 1], [7, 8, 5, 8, 7]],
    ![[4, 4, 4, 8, 4, 9, 0], [7, 9, 3, 8, 7]],
    ![[4, 4, 4, 9, 4, 8, 0], [7, 8, 3, 9, 7]],
    ![[0, 8, 4, 4, 4, 6, 6, 6, 8, 6, 0], [0, 8, 4, 4, 4, 6, 6, 6, 8, 6, 0, 8, 1, 8, 3, 8, 1]],
    ![[8, 4, 4, 4, 8, 6, 8, 7, 8, 3, 2, 2, 2, 8, 7, 2], [7, 8, 3, 8, 7]],
    ![[0, 8, 2, 2, 2, 9, 6, 0], [7, 9, 5, 8, 7]],
    ![[0, 9, 2, 2, 2, 8, 6, 0], [7, 8, 5, 9, 7]],
    ![[8, 6, 8, 0, 8, 6, 6, 6, 8], [8, 4, 4, 4, 8, 6, 2, 8, 4, 4]],
    ![[8, 5, 1, 8, 7, 3, 8, 5, 1], [7, 8, 1, 8, 7]],
    ![[6, 6, 6, 8, 0, 8, 6], [7, 8, 7, 8, 7]],
    ![[9, 3, 9, 1, 8, 3, 0], [9, 2, 2, 9, 2, 2, 2, 8, 2, 1]],
    ![[6, 6, 6, 8, 4, 1, 4, 8, 6], [2, 2, 2, 7, 8, 7, 8, 1, 7, 2]]]

/-- Interpret the ten letters without using permutation inverses during the
finite check. All letters in a representative word are involutions. -/
private def input {G : Type*} [Monoid G] (a : ParrottGenerator → G) (i : Fin 18) :
    Fin 10 → G :=
  ![a .s1, a .s2, a .s3, a .s4, a .s5, a .s6, a .s7, a .s8,
    ((doubleCosetWord i).map a).prod, ((doubleCosetWord i).reverse.map a).prod]

private def recover {G : Type*} [Monoid G] (a : ParrottGenerator → G)
    (i : Fin 15) (j : Fin 2) : G :=
  ((recoveryWord i j).map (input a ⟨i.val + 3, by omega⟩)).prod

private def packedAssignment : ParrottGenerator → Equiv.Perm (Fin 1600)
  | .r1 => Packed.perm 0 | .r8 => Packed.perm 1
  | .s1 => Packed.perm 2 | .s2 => Packed.perm 3
  | .s3 => Packed.perm 4 | .s4 => Packed.perm 5
  | .s5 => Packed.perm 6 | .s6 => Packed.perm 7
  | .s7 => Packed.perm 8 | .s8 => Packed.perm 9

private theorem packedAssignment_eq (a : ParrottGenerator) :
    packedAssignment a = Atlas1600ParrottData.permutation a := by
  cases a <;> simp [packedAssignment, Packed.perm_eq, Packed.generator,
    Atlas1600ParrottData.permutation]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
/-- Kernel-checked permutation identities for all thirty recovery words. -/
private theorem recovery_checked (i : Fin 15) (j : Fin 2) :
    recover packedAssignment i j = packedAssignment (![.r1, .r8] j) := by
  have h : ∀ (i : Fin 15) (j : Fin 2) (p : Fin 1600),
      recover packedAssignment i j p = packedAssignment (![.r1, .r8] j) p := by
    apply Atlas1600OrderCertificate.allFin₃
    decide +kernel
  exact Equiv.ext (h i j)

private theorem map_input {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (a : ParrottGenerator → G) (i : Fin 18) (j : Fin 10) :
    f (input a i j) = input (fun k => f (a k)) i j := by
  fin_cases j <;> simp [input, map_list_prod, List.map_map, Function.comp_def]

private theorem map_recover {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (a : ParrottGenerator → G) (i : Fin 15) (j : Fin 2) :
    f (recover a i j) = recover (fun k => f (a k)) i j := by
  simp only [recover, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact map_input f a _ k

/-- Transfer the finite identities through the faithful subtype inclusion. -/
private theorem recovery_eq (i : Fin 15) (j : Fin 2) :
    recover atlas1600ParrottAssignment i j =
      atlas1600ParrottAssignment (![.r1, .r8] j) := by
  apply Subtype.ext
  let f : Atlas1600Group →* Equiv.Perm (Fin 1600) := atlas1600Subgroup.subtype
  change f (recover atlas1600ParrottAssignment i j) = _
  rw [map_recover]
  have h : (fun k => f (atlas1600ParrottAssignment k)) =
      packedAssignment := by
    funext k
    exact (atlas1600ParrottAssignment_val k).trans (packedAssignment_eq k).symm
  rw [h, recovery_checked]
  exact (packedAssignment_eq _).trans (atlas1600ParrottAssignment_val _).symm

private theorem reflection_inv (a : ParrottGenerator)
    (ha : a = .r1 ∨ a = .r8 ∨ a = .s1) :
    (atlas1600ParrottAssignment a)⁻¹ = atlas1600ParrottAssignment a := by
  have h : atlas1600ParrottAssignment a ^ 2 = 1 := by
    rcases ha with rfl | rfl | rfl
    · simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using atlas1600ParrottAssignment_relations .i_r1
    · simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using atlas1600ParrottAssignment_relations .i_r8
    · simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using atlas1600ParrottAssignment_relations .i_s1
  exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)

/-- Reversal computes the inverse because the representative letters are
`r1`, `r8`, and `s1`, all involutions by the certified Parrott relations. -/
private theorem reverse_eq_inv (i : Fin 18) :
    ((doubleCosetWord i).reverse.map atlas1600ParrottAssignment).prod =
      (doubleCosetRep i)⁻¹ := by
  have h1 := reflection_inv .r1 (Or.inl rfl)
  have h8 := reflection_inv .r8 (Or.inr (Or.inl rfl))
  have hs := reflection_inv .s1 (Or.inr (Or.inr rfl))
  fin_cases i <;> simp [doubleCosetRep, doubleCosetWord, mul_inv_rev, h1, h8, hs, mul_assoc]

private theorem sylow_mem (a : ParrottGenerator) (h1 : a ≠ .r1) (h8 : a ≠ .r8) :
    atlas1600ParrottAssignment a ∈ S := by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  apply subset_closure
  cases a <;> simp_all

private theorem input_mem (i : Fin 18) (j : Fin 10) :
    input atlas1600ParrottAssignment i j ∈ S ⊔ closure {doubleCosetRep i} := by
  have hs (a : ParrottGenerator) (h1 : a ≠ .r1) (h8 : a ≠ .r8) :
      atlas1600ParrottAssignment a ∈ S ⊔ closure {doubleCosetRep i} :=
    mem_sup_left (sylow_mem a h1 h8)
  have ht : doubleCosetRep i ∈ S ⊔ closure {doubleCosetRep i} :=
    mem_sup_right (subset_closure (Set.mem_singleton _))
  fin_cases j
  all_goals simp only [input]
  all_goals first
    | exact hs _ (by decide) (by decide)
    | exact ht
    | exact (reverse_eq_inv i).symm ▸ (S ⊔ closure {doubleCosetRep i}).inv_mem ht

private theorem recovery_mem (i : Fin 15) (j : Fin 2) :
    recover atlas1600ParrottAssignment i j ∈
      S ⊔ closure {doubleCosetRep ⟨i.val + 3, by omega⟩} := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
  exact input_mem _ k

/-- Each nonparabolic representative, together with the marked Sylow subgroup,
generates the actual degree-1600 Atlas Tits group. -/
public theorem representative_generates (i : Fin 18) (hi : 3 ≤ i.val) :
    ExceptionalParabolics.S ⊔ Subgroup.closure {doubleCosetRep i} = ⊤ := by
  let k : Fin 15 := ⟨i.val - 3, by omega⟩
  have hk : (⟨k.val + 3, by omega⟩ : Fin 18) = i := by
    apply Fin.ext
    dsimp [k]
    omega
  have hmem (j : Fin 2) : atlas1600ParrottAssignment (![.r1, .r8] j) ∈
      S ⊔ closure {doubleCosetRep i} := by
    have h := recovery_mem k j
    rw [recovery_eq, hk] at h
    exact h
  apply top_unique
  rw [← ExceptionalParabolics.generate]
  apply sup_le <;> apply sup_le le_sup_left <;> apply (closure_le _).mpr
  · rintro x (rfl : x = _)
    exact hmem 0
  · rintro x (rfl : x = _)
    exact hmem 1

end Tits.ConverseLocalCoverage
