module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd

/-!
# Odd-degree core offenders contain odd permutations

Every best offender on the five- or seven-point binary augmentation core
is conjugate to a nontrivial group of disjoint transpositions. Its first
transposition is odd, as is its conjugate. Thus no such offender lies in
the alternating group. A general offender contains a best offender, so
the same exclusion holds before replacement.

Source: Aschbacher–Smith B.3.2(4), printed p.83; the five-point source
application is 13.2.4(2), printed p.879.
-/

public section
open Subgroup BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Offenders

/-- Every nontrivial disjoint-transposition group contains an odd permutation. -/
theorem CaseAFamily.not_le_alternating {n : ℕ} {A : Subgroup (Equiv.Perm (Fin n))}
    (hA : CaseAFamily n A) : ¬ A ≤ alternatingGroup (Fin n) := by
  obtain ⟨m,hm,hmn,g,rfl⟩ := hA
  have hn : 0 < n / 2 := by omega
  let i : Fin (n / 2) := ⟨0,hn⟩
  have hswap := pairSwap_mem (m := m) i (by exact hm)
  intro hle
  have he := Equiv.Perm.mem_alternatingGroup.mp
    (hle (mem_map_of_mem (MulAut.conj g).toMonoidHom hswap))
  have hne : (⟨2 * i.val,by omega⟩ : Fin n) ≠ ⟨2 * i.val + 1,by omega⟩ := by
    intro hh
    have h := congrArg Fin.val hh
    change 2 * i.val = 2 * i.val + 1 at h
    omega
  change Equiv.Perm.sign (g * pairSwap n i * g⁻¹) = 1 at he
  simp only [map_mul,map_inv,pairSwap,Equiv.Perm.sign_swap hne] at he
  have hodd : Equiv.Perm.sign g * (-1) * (Equiv.Perm.sign g)⁻¹ = -1 := by
    rw [mul_comm (Equiv.Perm.sign g) (-1),mul_assoc,mul_inv_cancel,mul_one]
  rw [hodd] at he
  exact (by decide : (-1 : ℤˣ) ≠ 1) he

/-- An actual offender on an odd core cannot be confined to its alternating subgroup. -/
theorem core_offender_not_le_alternating {n : ℕ} (hn : n = 5 ∨ n = 7)
    {A : Subgroup (Equiv.Perm (Fin n))} (hA : IsOffender (coreRepresentation (Fin n)) A) :
    ¬ A ≤ alternatingGroup (Fin n) := by
  obtain ⟨B,hBA,hB⟩ := hA.exists_bestOffender (coreRepresentation (Fin n))
  exact fun h => ((Odd.isBestOffender_core_iff_caseAFamily hn B).mp hB).not_le_alternating
    (hBA.trans h)

end CFSG.Quasithin.ChapterB.Offenders
