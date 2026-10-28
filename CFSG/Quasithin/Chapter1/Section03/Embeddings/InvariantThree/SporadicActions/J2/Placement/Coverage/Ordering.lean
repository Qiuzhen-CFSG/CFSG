module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.Coverage.TransversalData
public import Mathlib.Data.List.Chain

/-! A linear adjacent-pair check proves the 4,725 proposed coset keys distinct.
The entries are the binary image codes documented in `TransversalData`. -/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.CoverageCertificate

set_option maxRecDepth 1000000 in
theorem keyTable_size : keyTable.size = 4725 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem keyTable_chain : keyTable.toList.IsChain (· < ·) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem keyTable_strictMono : StrictMono (fun j : Fin 4725 => keyTable[j.val]!) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hi : i.val + 1 < keyTable.toList.length := by
    rw [Array.length_toList, keyTable_size]
    exact i.succ.isLt
  have h := (List.isChain_iff_getElem.mp keyTable_chain) i.val hi
  have h0 : i.val < keyTable.size := by rw [keyTable_size]; omega
  have h1 : i.val + 1 < keyTable.size := by simpa using hi
  simpa only [Fin.val_castSucc, Fin.val_succ, Array.getElem_toList,
    getElem!_pos keyTable i.val h0, getElem!_pos keyTable (i.val + 1) h1] using h

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.CoverageCertificate
