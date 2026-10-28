module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.DoubleCosets.Tables
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.DoubleCosets.Slice0
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.DoubleCosets.Slice1
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.DoubleCosets.Slice2
import Mathlib.Tactic.FinCases

/-!
# The three slices and their distinct translated point images

The row checks give strictly increasing keys within each of the three
slices. The 77 translating factors send their respective pivots to distinct
letters. Together these facts distinguish 77 × 5760 group elements.
Source: the retained ATLAS witnesses and the generated slice certificates.
-/

public section
namespace Sporadic.LeechRelated.HS.SmallIndex.DoubleCosetCertificate
set_option maxRecDepth 100000
set_option Elab.async false

private theorem rows_valid (k : Fin 3) (i : Fin 5760) : RowValid k i := by
  fin_cases k
  · exact rows_valid_0 i
  · exact rows_valid_1 i
  · exact rows_valid_2 i

theorem rowMap_pivot (k : Fin 3) (i : Fin 5760) : rowMap k i 1 = pivot k :=
  (rows_valid k i).1

theorem rowKey_strictMono (k : Fin 3) : StrictMono (rowKey k) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have h := (rows_valid k i.castSucc).2
  simp only [Fin.val_castSucc, dif_pos (show i.val + 1 < 5760 by omega)] at h
  change Nat.lt (rowKey k i.castSucc) (rowKey k i.succ)
  exact h

theorem orbitPoint_injective : Function.Injective orbitPoint := by
  apply OrderCertificate.allFin
  decide +kernel

end Sporadic.LeechRelated.HS.SmallIndex.DoubleCosetCertificate
