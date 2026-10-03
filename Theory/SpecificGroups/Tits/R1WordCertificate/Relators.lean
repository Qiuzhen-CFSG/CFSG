module

public import Theory.SpecificGroups.Tits.R1WordCertificate.Context
import Mathlib.Tactic.IntervalCases

/-!
# Matching the local R₁ certificate to Parrott's presentation

The 28 literal words are exactly the 28 relators in `R1Presentation`, including
factor order and signs. Their evaluation follows from the defining relations of
the actual presented group. The only initial subgroup loops are `r1` and `s1`;
acyclic definitions give the remaining representative edges.

Source: Parrott (1972), §5, p. 683;
`refs/original/n-group-global/parrott-tits-presentation.md`.
-/

public section
namespace Tits.R1WordCertificate
open Subgroup.CosetWordCertificate

/-- The original presentation index corresponding to each literal relator. -/
def relatorIndex (i : Fin 28) : ParrottR1RelatorIndex :=
  match i.val with
  | 0 => .i_r1
  | 1 => .i_s1
  | 2 => .i_s2
  | 3 => .i_s4
  | 4 => .i_s6
  | 5 => .i_s8
  | 6 => .i_s3
  | 7 => .i_s5
  | 8 => .i_s7
  | 9 => .ii_s1_s2
  | 10 => .ii_s1_s3
  | 11 => .ii_s1_s5
  | 12 => .iii_s1_s6
  | 13 => .iii_s1_s7
  | 14 => .iii_s1_s8
  | 15 => .iv_s2_s4
  | 16 => .iv_s2_s6
  | 17 => .iv_s2_s8
  | 18 => .iv_s7_s2
  | 19 => .v_s7_s4
  | 20 => .v_s3_s5
  | 21 => .v_s5_s4
  | 22 => .vi_s1_r1
  | 23 => .vii_s2
  | 24 => .vii_s4
  | 25 => .vii_s5
  | 26 => .vii_s3
  | 27 => .vii_r3
  | _ => .i_r1

/-- Each literal word is exactly its presentation relator in the free group. -/
theorem relator_exact (i : Fin 28) :
    FreeGroup.mk (relatorFin i) = parrottR1Relator (relatorIndex i) := by
  rcases i with ⟨n, hn⟩
  interval_cases n <;>
    simp [relatorFin, relatorIndex, parrottR1Relator, parrottR1RelatorInclusion,
      parrottRelator, parrottR1Delete, parrottR3, parrottR5, parrottR7,
      parrottCommutator, FreeGroup.of, FreeGroup.mul_mk, FreeGroup.inv_mk,
      FreeGroup.invRev, FreeGroup.pow_mk]

/-- Every defining equation occurs among the 28 literal relators. -/
theorem relatorIndex_surjective : Function.Surjective relatorIndex := by
  intro i
  cases i with
  | i_r1 => exact ⟨0, rfl⟩
  | i_s1 => exact ⟨1, rfl⟩
  | i_s2 => exact ⟨2, rfl⟩
  | i_s4 => exact ⟨3, rfl⟩
  | i_s6 => exact ⟨4, rfl⟩
  | i_s8 => exact ⟨5, rfl⟩
  | i_s3 => exact ⟨6, rfl⟩
  | i_s5 => exact ⟨7, rfl⟩
  | i_s7 => exact ⟨8, rfl⟩
  | ii_s1_s2 => exact ⟨9, rfl⟩
  | ii_s1_s3 => exact ⟨10, rfl⟩
  | ii_s1_s5 => exact ⟨11, rfl⟩
  | iii_s1_s6 => exact ⟨12, rfl⟩
  | iii_s1_s7 => exact ⟨13, rfl⟩
  | iii_s1_s8 => exact ⟨14, rfl⟩
  | iv_s2_s4 => exact ⟨15, rfl⟩
  | iv_s2_s6 => exact ⟨16, rfl⟩
  | iv_s2_s8 => exact ⟨17, rfl⟩
  | iv_s7_s2 => exact ⟨18, rfl⟩
  | v_s7_s4 => exact ⟨19, rfl⟩
  | v_s3_s5 => exact ⟨20, rfl⟩
  | v_s5_s4 => exact ⟨21, rfl⟩
  | vi_s1_r1 => exact ⟨22, rfl⟩
  | vii_s2 => exact ⟨23, rfl⟩
  | vii_s4 => exact ⟨24, rfl⟩
  | vii_s5 => exact ⟨25, rfl⟩
  | vii_s3 => exact ⟨26, rfl⟩
  | vii_r3 => exact ⟨27, rfl⟩

/-- The literal relators impose precisely the original local presentation. -/
theorem literal_relators_eq_presentation :
    Set.range (fun i : Fin 28 => FreeGroup.mk (relatorFin i)) = parrottR1RelatorSet := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨relatorIndex i, (relator_exact i).symm⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨i, rfl⟩ := relatorIndex_surjective r
    exact ⟨i, relator_exact i⟩

/-- Relator loops hold in the actual local presented group. -/
theorem relator_ok (r : Nat) : eval parrottR1Generator (relatorWords r) = 1 := by
  by_cases h : r < 28
  · simp only [relatorWords, dif_pos h]
    change FreeGroup.lift parrottR1Generator (FreeGroup.mk (relatorFin ⟨r, h⟩)) = 1
    rw [relator_exact]
    exact parrottR1_generators_satisfy_relations _
  · simp [relatorWords, h]

/-- Only the two defining subgroup generators may give initial loops. -/
theorem allowed_ok (a : Letter ParrottR1Generator)
    (h : context.allowed a = true) :
    eval parrottR1Generator [a] ∈ parrottR1DihedralSubgroup := by
  have ha : a = (.r1, true) ∨ a = (.s1, true) := by
    simpa [context] using of_decide_eq_true h
  rcases ha with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- The certificate context is realized in the group defined by the presentation. -/
theorem valid : Valid context parrottR1DihedralSubgroup parrottR1Generator
    (definitions.repr parrottR1Generator) :=
  definitions.valid relatorWords context.allowed allowed_ok relator_ok

end Tits.R1WordCertificate
