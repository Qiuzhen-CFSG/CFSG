module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base
import Mathlib.Tactic.FinCases

/-!
# Nested signed alphabets containing the defining HS generators

Part of the order-divisibility certificate for the exact ATLAS HS carrier.
Source: GLS volume 3, Table 5.3m, printed p.274; ATLAS HSG1-p100B0.
The generator in `OrderBound/source/` supplies witnesses only. Every finite
identity is checked by Lean's kernel.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.OrderCertificate
open Theory.GroupTheory
set_option maxRecDepth 100000
set_option Elab.async false

def gen0 (x : Fin 20) : Equiv.Perm (Fin 100) :=
  match x.val with
  | 0 => p0
  | 1 => p1
  | 2 => p1⁻¹
  | 3 => p2
  | 4 => p3
  | 5 => p3⁻¹
  | 6 => p4
  | 7 => p4⁻¹
  | 8 => p5
  | 9 => p5⁻¹
  | 10 => p6
  | 11 => p6⁻¹
  | 12 => p7
  | 13 => p7⁻¹
  | 14 => p8
  | 15 => p8⁻¹
  | 16 => p9
  | 17 => p9⁻¹
  | 18 => p10
  | _ => p10⁻¹

def inv0 (x : Fin 20) : Fin 20 :=
  match x.val with
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 3
  | 4 => 5
  | 5 => 4
  | 6 => 7
  | 7 => 6
  | 8 => 9
  | 9 => 8
  | 10 => 11
  | 11 => 10
  | 12 => 13
  | 13 => 12
  | 14 => 15
  | 15 => 14
  | 16 => 17
  | 17 => 16
  | 18 => 19
  | _ => 18

theorem inv0_spec (i : Fin 20) : gen0 (inv0 i) = (gen0 i)⁻¹ := by
  fin_cases i <;> rfl

def H0 : Subgroup (Equiv.Perm (Fin 100)) :=
  wordSubgroup gen0 inv0 inv0_spec

def gen1 (x : Fin 17) : Equiv.Perm (Fin 100) :=
  match x.val with
  | 0 => p2
  | 1 => p3
  | 2 => p3⁻¹
  | 3 => p4
  | 4 => p4⁻¹
  | 5 => p5
  | 6 => p5⁻¹
  | 7 => p6
  | 8 => p6⁻¹
  | 9 => p7
  | 10 => p7⁻¹
  | 11 => p8
  | 12 => p8⁻¹
  | 13 => p9
  | 14 => p9⁻¹
  | 15 => p10
  | _ => p10⁻¹

def inv1 (x : Fin 17) : Fin 17 :=
  match x.val with
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 4
  | 4 => 3
  | 5 => 6
  | 6 => 5
  | 7 => 8
  | 8 => 7
  | 9 => 10
  | 10 => 9
  | 11 => 12
  | 12 => 11
  | 13 => 14
  | 14 => 13
  | 15 => 16
  | _ => 15

theorem inv1_spec (i : Fin 17) : gen1 (inv1 i) = (gen1 i)⁻¹ := by
  fin_cases i <;> rfl

def H1 : Subgroup (Equiv.Perm (Fin 100)) :=
  wordSubgroup gen1 inv1 inv1_spec

theorem H1_le : H1 ≤ H0 := by
  apply wordSubgroup_le_of_gen_mem
  intro i
  fin_cases i
  · exact ⟨[3], mul_one _⟩
  · exact ⟨[4], mul_one _⟩
  · exact ⟨[5], mul_one _⟩
  · exact ⟨[6], mul_one _⟩
  · exact ⟨[7], mul_one _⟩
  · exact ⟨[8], mul_one _⟩
  · exact ⟨[9], mul_one _⟩
  · exact ⟨[10], mul_one _⟩
  · exact ⟨[11], mul_one _⟩
  · exact ⟨[12], mul_one _⟩
  · exact ⟨[13], mul_one _⟩
  · exact ⟨[14], mul_one _⟩
  · exact ⟨[15], mul_one _⟩
  · exact ⟨[16], mul_one _⟩
  · exact ⟨[17], mul_one _⟩
  · exact ⟨[18], mul_one _⟩
  · exact ⟨[19], mul_one _⟩

def gen2 (x : Fin 14) : Equiv.Perm (Fin 100) :=
  match x.val with
  | 0 => p4
  | 1 => p4⁻¹
  | 2 => p5
  | 3 => p5⁻¹
  | 4 => p6
  | 5 => p6⁻¹
  | 6 => p7
  | 7 => p7⁻¹
  | 8 => p8
  | 9 => p8⁻¹
  | 10 => p9
  | 11 => p9⁻¹
  | 12 => p10
  | _ => p10⁻¹

def inv2 (x : Fin 14) : Fin 14 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 4
  | 6 => 7
  | 7 => 6
  | 8 => 9
  | 9 => 8
  | 10 => 11
  | 11 => 10
  | 12 => 13
  | _ => 12

theorem inv2_spec (i : Fin 14) : gen2 (inv2 i) = (gen2 i)⁻¹ := by
  fin_cases i <;> rfl

def H2 : Subgroup (Equiv.Perm (Fin 100)) :=
  wordSubgroup gen2 inv2 inv2_spec

theorem H2_le : H2 ≤ H1 := by
  apply wordSubgroup_le_of_gen_mem
  intro i
  fin_cases i
  · exact ⟨[3], mul_one _⟩
  · exact ⟨[4], mul_one _⟩
  · exact ⟨[5], mul_one _⟩
  · exact ⟨[6], mul_one _⟩
  · exact ⟨[7], mul_one _⟩
  · exact ⟨[8], mul_one _⟩
  · exact ⟨[9], mul_one _⟩
  · exact ⟨[10], mul_one _⟩
  · exact ⟨[11], mul_one _⟩
  · exact ⟨[12], mul_one _⟩
  · exact ⟨[13], mul_one _⟩
  · exact ⟨[14], mul_one _⟩
  · exact ⟨[15], mul_one _⟩
  · exact ⟨[16], mul_one _⟩

def gen3 (x : Fin 10) : Equiv.Perm (Fin 100) :=
  match x.val with
  | 0 => p6
  | 1 => p6⁻¹
  | 2 => p7
  | 3 => p7⁻¹
  | 4 => p8
  | 5 => p8⁻¹
  | 6 => p9
  | 7 => p9⁻¹
  | 8 => p10
  | _ => p10⁻¹

def inv3 (x : Fin 10) : Fin 10 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 4
  | 6 => 7
  | 7 => 6
  | 8 => 9
  | _ => 8

theorem inv3_spec (i : Fin 10) : gen3 (inv3 i) = (gen3 i)⁻¹ := by
  fin_cases i <;> rfl

def H3 : Subgroup (Equiv.Perm (Fin 100)) :=
  wordSubgroup gen3 inv3 inv3_spec

theorem H3_le : H3 ≤ H2 := by
  apply wordSubgroup_le_of_gen_mem
  intro i
  fin_cases i
  · exact ⟨[4], mul_one _⟩
  · exact ⟨[5], mul_one _⟩
  · exact ⟨[6], mul_one _⟩
  · exact ⟨[7], mul_one _⟩
  · exact ⟨[8], mul_one _⟩
  · exact ⟨[9], mul_one _⟩
  · exact ⟨[10], mul_one _⟩
  · exact ⟨[11], mul_one _⟩
  · exact ⟨[12], mul_one _⟩
  · exact ⟨[13], mul_one _⟩

def gen4 (x : Fin 6) : Equiv.Perm (Fin 100) :=
  match x.val with
  | 0 => p8
  | 1 => p8⁻¹
  | 2 => p9
  | 3 => p9⁻¹
  | 4 => p10
  | _ => p10⁻¹

def inv4 (x : Fin 6) : Fin 6 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | _ => 4

theorem inv4_spec (i : Fin 6) : gen4 (inv4 i) = (gen4 i)⁻¹ := by
  fin_cases i <;> rfl

def H4 : Subgroup (Equiv.Perm (Fin 100)) :=
  wordSubgroup gen4 inv4 inv4_spec

theorem H4_le : H4 ≤ H3 := by
  apply wordSubgroup_le_of_gen_mem
  intro i
  fin_cases i
  · exact ⟨[4], mul_one _⟩
  · exact ⟨[5], mul_one _⟩
  · exact ⟨[6], mul_one _⟩
  · exact ⟨[7], mul_one _⟩
  · exact ⟨[8], mul_one _⟩
  · exact ⟨[9], mul_one _⟩

def gen5 (x : Fin 2) : Equiv.Perm (Fin 100) :=
  match x.val with
  | 0 => p10
  | _ => p10⁻¹

def inv5 (x : Fin 2) : Fin 2 :=
  match x.val with
  | 0 => 1
  | _ => 0

theorem inv5_spec (i : Fin 2) : gen5 (inv5 i) = (gen5 i)⁻¹ := by
  fin_cases i <;> rfl

def H5 : Subgroup (Equiv.Perm (Fin 100)) :=
  wordSubgroup gen5 inv5 inv5_spec

theorem H5_le : H5 ≤ H4 := by
  apply wordSubgroup_le_of_gen_mem
  intro i
  fin_cases i
  · exact ⟨[4], mul_one _⟩
  · exact ⟨[5], mul_one _⟩

def gen6 : Fin 0 → Equiv.Perm (Fin 100) :=
  Fin.elim0

def inv6 : Fin 0 → Fin 0 :=
  Fin.elim0

theorem inv6_spec (i : Fin 0) : gen6 (inv6 i) = (gen6 i)⁻¹ := Fin.elim0 i

def H6 : Subgroup (Equiv.Perm (Fin 100)) :=
  wordSubgroup gen6 inv6 inv6_spec

theorem H6_le : H6 ≤ H5 := wordSubgroup_le_of_gen_mem (fun i => Fin.elim0 i)

/-- The certified group contains the subgroup of the two published generators. -/
theorem generated_le : generated ≤ H0 := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases Set.mem_insert_iff.mp hg with hg | hg
  · rw [hg, ← a_eq_generator]
    exact ⟨[0], mul_one _⟩
  · rw [Set.mem_singleton_iff.mp hg, ← b_eq_generator]
    exact ⟨[1], mul_one _⟩

end Sporadic.LeechRelated.HS.OrderCertificate
