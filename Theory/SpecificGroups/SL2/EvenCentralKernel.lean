module
public import Theory.GroupTheory.PerfectCentralCoverPGroupKernel
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import GorensteinWalter.PSL2FourUniversalCover
public import GorensteinWalter.PSL2SchurMultiplier

/-!
# Two-group kernels of even PSL₂ perfect central covers

The ordinary even-field universal cover has trivial kernel; the field
of four elements has the explicit SL₂(5) double cover. Comparing any
prescribed perfect central cover with these genuine universal covers
shows its kernel is a two-group, including the exceptional field.

Source: Aschbacher–Smith I.1.3 as used in E.2.10(7), printed p.223.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SL2
universe u v
variable {F : Type u} [Field F] [Finite F]
  {E : Type v} [Group E] [Finite E]

theorem perfect_central_kernel_isTwoGroup (m : ℕ) (hm : 2 ≤ m)
    (hcard : Nat.card F = 2 ^ m)
    (c : PerfectCentralCovering.Cover E PSL(2,F)) :
    IsPGroup 2 c.toMonoidHom.ker := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hcard]
    exact (show 2^2 ≤ 2^m from Nat.pow_le_pow_right (by decide) hm)
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (3 < Nat.card (ZMod 5)) := ⟨by norm_num⟩
  let : IsQuasisimple E := c.isQuasisimple
  let d := c.toCovering
  by_cases he : m = 2
  · have hF : Nat.card F = 4 := by simpa [he] using hcard
    exact Covering.ker_isPGroup_of_universal d
      (GorensteinWalter.PSL2Cover.fourCover F hF)
      (GorensteinWalter.PSL2Cover.fourCover_isUniversal F hF)
      ((IsPGroup.of_card (p := 2) (n := 1) (by simp : Nat.card (Multiplicative (ZMod 2)) = 2^1)).of_equiv
        (GorensteinWalter.PSL2Cover.fourKernelEquivTwo F hF).symm)
  · have h8 : 8 ≤ Nat.card F := by
      rw [hcard]
      exact (show 2^3 ≤ 2^m from Nat.pow_le_pow_right (by decide) (by omega))
    have heven : Even (Nat.card F) := by rw [hcard]; exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    apply Covering.ker_isPGroup_of_universal d
      (Covering.id : Covering PSL(2,F) PSL(2,F))
      (GorensteinWalter.PSL2Cover.identity_isUniversal_of_even F heven h8)
    exact IsPGroup.ker_isPGroup_of_injective Function.injective_id
end Theory.SL2
