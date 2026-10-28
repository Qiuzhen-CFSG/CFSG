module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.Coverage.KeyChecks

/-!
# Distinctness of the 4,725 J₂ cosets

Membership in the checked list of parameter/key pairs supplies the numerical
key equality at every index. Strict increase of the key table, together with
invariance on cosets, proves that these 4,725 cosets are distinct.

Source: the fixed ATLAS degree-100 witnesses documented in `source/README.md`;
Aschbacher–Smith, printed p.511, and GLS3 Table 5.3g.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.CoverageCertificate
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics

set_option maxRecDepth 100000 in
theorem transversalKey_eq (j : Fin 4725) :
    explicitKey (transversalMap j) = keyTable[j.val]! := by
  have hp : j.val < transversalParams.size := by rw [parameterTable_size]; exact j.isLt
  have hk : j.val < keyTable.size := by rw [keyTable_size]; exact j.isLt
  have hz : j.val < (transversalParams.toList.zip keyTable.toList).length := by
    simp only [List.length_zip, Array.length_toList, lt_min_iff]
    exact ⟨hp, hk⟩
  have hm := List.getElem_mem hz
  have hh := List.all_eq_true.mp entries_valid _ hm
  simp only [entryValid, decide_eq_true_eq, List.getElem_zip, Array.getElem_toList] at hh
  have hmap : transversalMap j = parameterMap transversalParams[j.val]! := rfl
  rw [hmap, getElem!_pos transversalParams j.val hp, getElem!_pos keyTable j.val hk]
  exact hh

set_option maxRecDepth 100000 in
theorem transversal_cosets_injective : Function.Injective
    (fun j : Fin 4725 => (QuotientGroup.mk (transversal j) : Carrier ⧸ Seed.s)) := by
  intro i j h
  apply keyTable_strictMono.injective
  have hk := key_eq_of_coset_eq h
  simpa only [transversal_key, transversalKey_eq] using hk

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.CoverageCertificate
