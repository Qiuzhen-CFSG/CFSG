module

public import Theory.Mathieu.M22.Properties.FourNormalizers.FixedSylow.Data

/-!
# Checked Sylow words and conjugacy witnesses

The checks compare degree-22 permutation tables, using no subgroup enumeration
inside Lean. Every square-one element either fixes the standard hexad or has
four distinct conjugates, distinct also from the identity. The mathematical
use of this exhaustive disjunction is in `FixedSylow`.

Source context: Aschbacher–Smith 15.3.43, printed p.1140; GLS3 Table 5.3c.
-/

public section
namespace Sporadic.Mathieu.M22FourNormalizers.FixedSylow
set_option maxRecDepth 100000

theorem row_word_table (i : Fin 128) (x : Fin 22) :
    wordAction (rowWord i) x = rowTable i x := by
  revert i x
  decide +kernel

theorem row_table_inv (i : Fin 128) (x : Fin 22) :
    rowTable i (rowInvTable i x) = x := by
  revert i x
  decide +kernel

theorem row_key_injective : Function.Injective (fun i => permutationKey (rowTable i)) := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

theorem row_cases (i : Fin 128) :
    (∀ x ∈ m22Hexad123, rowTable i x = x) ∨
      rowTable i (rowTable i (squarePoint i)) ≠ squarePoint i ∨
        Function.Injective (fiveKey i) := by
  revert i
  decide +kernel

end Sporadic.Mathieu.M22FourNormalizers.FixedSylow
