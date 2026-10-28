module

public import Theory.Mathieu.M11.Basic
public import Theory.GroupTheory.MinimalSimple

/-!
# M11 is not minimal simple

The stabilizer of point 1 in the degree-eleven Witt-design model is a proper
nonsolvable subgroup. We exhibit two elements `x` and `y` in this stabilizer,
with `x` nonidentity, and certify identities expressing each as a commutator
of words in the pair. Induction then puts both elements in every term of the
stabilizer's derived series, contradicting solvability.

The witnesses are the first ATLAS generator and the permutation
`(0,3,8)(4,7,6)(5,10,9)`. Membership of the latter is certified by a word in
the two ATLAS generators. All permutation identities are checked pointwise
by kernel reduction. No group-order or classification argument is needed.

Source: the concrete degree-eleven ATLAS model documented in
`Theory.Mathieu.M11.Basic`; the exclusion requested in M5 of
`docs/thompson-minimal-simple-roadmap.md`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 800000
open scoped commutatorElement

namespace Sporadic.Mathieu

private def witnessC : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 3, 8] * List.formPerm [4, 7, 6] * List.formPerm [5, 10, 9]

private theorem witnessC_word : witnessC =
    m11GeneratorB * m11GeneratorA * m11GeneratorB * m11GeneratorA *
      m11GeneratorB⁻¹ * m11GeneratorA * m11GeneratorB * m11GeneratorA *
      m11GeneratorB * m11GeneratorB := by
  ext i
  fin_cases i <;> rfl

private theorem witnessC_mem : witnessC ∈ M11 := by
  rw [witnessC_word]
  have hbi := M11.inv_mem m11GeneratorB_mem
  exact M11.mul_mem (M11.mul_mem (M11.mul_mem (M11.mul_mem
    (M11.mul_mem (M11.mul_mem (M11.mul_mem (M11.mul_mem
      (M11.mul_mem m11GeneratorB_mem m11GeneratorA_mem) m11GeneratorB_mem)
      m11GeneratorA_mem) hbi) m11GeneratorA_mem) m11GeneratorB_mem)
      m11GeneratorA_mem) m11GeneratorB_mem) m11GeneratorB_mem

private noncomputable def pointStabilizer : Subgroup M11 := MulAction.stabilizer M11 (1 : Fin 11)

private noncomputable def witnessX : pointStabilizer :=
  ⟨⟨m11GeneratorA, m11GeneratorA_mem⟩, by rfl⟩
private noncomputable def witnessY : pointStabilizer := ⟨⟨witnessC, witnessC_mem⟩, by rfl⟩

private theorem witnessX_commutator :
    witnessX = ⁅witnessY⁻¹ * witnessX * witnessY * witnessX * witnessY,
      witnessY * witnessX * witnessY⁻¹ * witnessX * witnessY⁻¹⁆ := by
  apply Subtype.ext
  apply Subtype.ext
  change m11GeneratorA = ⁅witnessC⁻¹ * m11GeneratorA * witnessC * m11GeneratorA * witnessC,
    witnessC * m11GeneratorA * witnessC⁻¹ * m11GeneratorA * witnessC⁻¹⁆
  ext i
  fin_cases i <;> rfl

private theorem witnessY_commutator :
    witnessY = ⁅witnessX * witnessY⁻¹,
      witnessX * witnessY⁻¹ * witnessX * witnessY * witnessX * witnessY⁆ := by
  apply Subtype.ext
  apply Subtype.ext
  change witnessC = ⁅m11GeneratorA * witnessC⁻¹,
    m11GeneratorA * witnessC⁻¹ * m11GeneratorA * witnessC * m11GeneratorA * witnessC⁆
  ext i
  fin_cases i <;> rfl

private theorem witnesses_mem_derivedSeries (n : ℕ) :
    witnessX ∈ derivedSeries pointStabilizer n ∧
      witnessY ∈ derivedSeries pointStabilizer n := by
  induction n with
  | zero => exact ⟨Subgroup.mem_top _, Subgroup.mem_top _⟩
  | succ n ih =>
    let D := derivedSeries pointStabilizer n
    have hyi : witnessY⁻¹ ∈ D := D.inv_mem ih.2
    constructor
    · rw [witnessX_commutator, derivedSeries_succ]
      exact Subgroup.commutator_mem_commutator
        (D.mul_mem (D.mul_mem (D.mul_mem (D.mul_mem hyi ih.1) ih.2) ih.1) ih.2)
        (D.mul_mem (D.mul_mem (D.mul_mem (D.mul_mem ih.2 ih.1) hyi) ih.1) hyi)
    · rw [witnessY_commutator, derivedSeries_succ]
      exact Subgroup.commutator_mem_commutator (D.mul_mem ih.1 hyi)
        (D.mul_mem (D.mul_mem (D.mul_mem (D.mul_mem (D.mul_mem ih.1 hyi)
          ih.1) ih.2) ih.1) ih.2)

private theorem pointStabilizer_not_isSolvable : ¬ Group.IsSolvable pointStabilizer := by
  rintro ⟨n, hn⟩
  have hx := (witnesses_mem_derivedSeries n).1
  rw [hn, Subgroup.mem_bot] at hx
  have h := congrArg (fun z : pointStabilizer => (z.val.val : Equiv.Perm (Fin 11)) 2) hx
  change (10 : Fin 11) = 2 at h
  exact (by decide : (10 : Fin 11) ≠ 2) h

private theorem pointStabilizer_lt_top : pointStabilizer < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro h
  have hb : (⟨m11GeneratorB, m11GeneratorB_mem⟩ : M11) ∈ pointStabilizer := by
    rw [h]
    exact Subgroup.mem_top _
  change m11GeneratorB (1 : Fin 11) = 1 at hb
  change (4 : Fin 11) = 1 at hb
  exact (by decide : (4 : Fin 11) ≠ 1) hb

/-- M11 has a proper nonsolvable point stabilizer, so it is not minimal simple. -/
public theorem m11_not_isMinimalSimple : ¬ IsMinimalSimple M11 := by
  intro h
  exact pointStabilizer_not_isSolvable (h.solvable_of_lt pointStabilizer pointStabilizer_lt_top)

end Sporadic.Mathieu
