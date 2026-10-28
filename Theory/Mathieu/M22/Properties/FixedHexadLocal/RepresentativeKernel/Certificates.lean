module
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.RepresentativeKernel.Data
/-!
# Kernel-checked centralizer certificates

The 384 words agree with their permutation tables, have distinct image triples,
and centralize the standard involution. An element outside the pointwise hexad
kernel has an explicit conjugate with which it fails to commute. Fifteen further
words preserve the hexad and give distinct conjugates of the involution.

All checks are reductions of closed propositions in Lean's kernel. Their use in
the characteristic-kernel argument is explained in `Enumeration`.
Source context: Aschbacher--Smith 2.3.9(7)(f), printed pp.525--526.
-/

public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M22RepresentativeKernel
set_option maxRecDepth 100000

theorem row_word_table (i : Fin 384) (x : Fin 22) : wordAction (rowWord i) x = rowTable i x := by
  revert i x
  decide +kernel

theorem row_table_inv (i : Fin 384) (x : Fin 22) : rowTable i (rowInvTable i x) = x := by
  revert i x
  decide +kernel

theorem row_commutes (i : Fin 384) (x : Fin 22) :
    rowTable i (letterTable 0 x) = letterTable 0 (rowTable i x) := by
  revert i x
  decide +kernel

theorem row_key_injective : Function.Injective (fun i : Fin 384 =>
    (rowTable i 0).val * 22 ^ 2 + (rowTable i 1).val * 22 + (rowTable i 2).val) := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

theorem row_outside (i : Fin 384) :
    (∀ x ∈ hexad, rowTable i x = x) ∨
    let j := witnessRow i
    let x := witnessPoint i
    rowTable i (rowTable j (rowTable i (rowInvTable j x))) ≠
      rowTable j (rowTable i (rowInvTable j (rowTable i x))) := by
  revert i
  decide +kernel

theorem conjugator_fixes_hexad (i : Fin 15) (x : Fin 22) (hx : x ∈ hexad) :
    wordAction (conjugatorWord i) x ∈ hexad := by
  revert i x
  decide +kernel

theorem conjugator_word_table (i : Fin 15) (x : Fin 22) :
    wordAction (conjugatorWord i) x = conjugatorTable i x := by
  revert i x
  decide +kernel

theorem conjugator_table_inv (i : Fin 15) (x : Fin 22) :
    conjugatorTable i (conjugatorInvTable i x) = x := by
  revert i x
  decide +kernel

theorem conjugate_point_injective : Function.Injective (fun i : Fin 15 =>
    conjugatorTable i (letterTable 0 (conjugatorInvTable i 0))) := by
  decide +kernel

end Sporadic.Mathieu.M22RepresentativeKernel
