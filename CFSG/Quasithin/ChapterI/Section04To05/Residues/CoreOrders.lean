module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.CoreJoins
public import Theory.GroupTheory.PrimeCoreJoinAlternative

/-!
# Orders and alternatives for the original pair cores

The literal pair quotient has kernel Qᵢ and lifts the quotient parabolic
two-core. Its order formula and the prime-core join alternative retain the
ambient subgroup inclusions used by the S₆ exception in I.5.7(1).
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G K : Type*} [Group G] [Group K] {D : Diagram} (S : DSystem D G)

theorem pair_core_card [Finite K] (i j : Fin 3)
    (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) :
    Nat.card ((S.pair i j).pCoreIn 2) = Nat.card (S.Q i) *
      Nat.card (pCore 2 ((localParabolic S.family i j).map (S.localQuotientMap i e))) := by
  let : Finite (S.pair i j) := Finite.of_injective
    (inclusion (show S.pair i j ≤ S.family i from inf_le_left)) (inclusion_injective _)
  have h := (S.pairQuotientMap i j e).card_pCore_of_ker_isPGroup
    (S.pairQuotientMap_surjective i j e) (S.pairQuotientMap_ker_isTwoGroup i j e)
  rw [S.pairQuotientMap_ker, Nat.card_congr (subgroupOfEquivOfLe
    (le_inf ((S.family i).pCoreIn_le 2) ((S.Q_le_T i).trans (S.T_le j)))).toEquiv] at h
  have heq : Nat.card ((S.pair i j).pCoreIn 2) = Nat.card (pCore 2 (S.pair i j)) :=
    Nat.card_congr (equivMapOfInjective _ _ (S.pair i j).subtype_injective).symm.toEquiv
  exact heq.trans h

theorem pair_core_join_or_le [Finite K] (i j : Fin 3)
    (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K)
    (hc : (Nat.card (pCore 2
      ((localParabolic S.family i j).map (S.localQuotientMap i e)))).Prime) :
    (S.pair i j).pCoreIn 2 = S.Q i ⊔ S.Q j ∨ S.Q j ≤ S.Q i := by
  let : Finite (S.pair i j) := Finite.of_injective
    (inclusion (show S.pair i j ≤ S.family i from inf_le_left)) (inclusion_injective _)
  have hi : S.Q i ≤ S.pair i j :=
    le_inf ((S.family i).pCoreIn_le 2) ((S.Q_le_T i).trans (S.T_le j))
  have hj : S.Q j ≤ S.pair i j :=
    le_inf ((S.Q_le_T j).trans (S.T_le i)) ((S.family j).pCoreIn_le 2)
  let Q := (S.Q j).subgroupOf (S.pair i j)
  let : Q.Normal := (normal_subgroupOf_iff_le_normalizer hj).mpr
    (inf_le_right.trans (S.family_le_normalizer_Q j))
  have h := (S.pairQuotientMap i j e).pCore_eq_sup_or_le_ker
    (S.pairQuotientMap_surjective i j e) (S.pairQuotientMap_ker_isTwoGroup i j e)
    hc Q (((S.family j).isPGroup_pCoreIn 2).comap_subtype)
  rw [S.pairQuotientMap_ker] at h
  rcases h with hh | hh
  · left
    change (pCore 2 (S.pair i j)).map (S.pair i j).subtype = _
    rw [hh, Subgroup.map_sup, map_subgroupOf_eq_of_le hj,
      map_subgroupOf_eq_of_le hi, sup_comm]
  · right
    intro x hx
    exact hh (show (⟨x, hj hx⟩ : S.pair i j) ∈ Q from hx)

end Quasithin.I5.DSystem
