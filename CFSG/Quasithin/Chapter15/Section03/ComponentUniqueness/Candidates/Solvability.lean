module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Containment
public import Theory.GroupTheory.SolvableNormalSup

/-!
# Solvability of the local supplement

The local quotient `Y₊/O₂(Y₊)` is a three-group. Its two-core and
three-group quotient are solvable, so `Y₊` is solvable. Since
`N_I(Y₊) = M ∩ I` and `S ≤ M ∩ I`, the group `Y₊S` is then a solvable
extension by a two-group. This supplies the solvability input to
15.3.33(1) from the earlier local data.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.7, 15.3.11(1),(4),(5), and 15.3.33(1), printed pp.1122--1124 and 1134.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]

/-- The local quotient shape makes Y₊ solvable, and its extension by S
is solvable because S normalizes Y₊. -/
theorem solvable_yplus_join_of_threeGroup_quotient {Yplus S : Subgroup G}
    (hS : IsPGroup 2 S) (hSY : S ≤ normalizer (Yplus : Set G))
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus)) :
    Group.IsSolvable (Yplus ⊔ S : Subgroup G) := by
  let : Group.IsNilpotent (pCore 2 Yplus) := pCore_isPGroup.isNilpotent
  let := hY.isNilpotent
  let : Group.IsSolvable Yplus :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 Yplus)).mpr
      ⟨inferInstance, inferInstance⟩
  let := hS.isNilpotent
  let J := Yplus ⊔ S
  let N := Yplus.subgroupOf J
  let D := S.subgroupOf J
  have hNJ : Yplus ≤ J := le_sup_left
  have hDJ : S ≤ J := le_sup_right
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hNJ).mpr
    (sup_le Yplus.le_normalizer hSY)
  let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hNJ).toMonoidHom) (subgroupOfEquivOfLe hNJ).injective
  let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hDJ).toMonoidHom) (subgroupOfEquivOfLe hDJ).injective
  apply Group.isSolvable_of_normal_sup_eq_top N D
  rw [← subgroupOf_sup hNJ hDJ]
  exact subgroupOf_self J

/-- 15.3.33(1) with solvability discharged from the local three-group
quotient and 15.3.11(4), rather than supplied as a separate hypothesis. -/
theorem lemma_15_3_33_1_of_threeGroup_quotient
    {Yplus S M I L₁ : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hL : L₁ ≤ I) (hLN : Yplus ⊔ S ≤ normalizer (L₁ : Set G))
    (hF : generalizedFitting L₁ = pCore 2 L₁) : L₁ ≤ M ⊓ I := by
  obtain ⟨P, hP⟩ := hSylow I hI
  have hS : IsPGroup 2 S := hP ▸ P.isPGroup'.map I.subtype
  have hSY : S ≤ normalizer (Yplus : Set G) := by
    have hSMI : S ≤ M ⊓ I := le_inf hSM (le_sup_right.trans hI.1.2)
    rw [← hMI] at hSMI
    exact hSMI.trans inf_le_right
  let := solvable_yplus_join_of_threeGroup_quotient hS hSY hY
  exact lemma_15_3_33_1 hI hSylow h25 hodd hL hLN hF

end CFSG.Quasithin.Chapter15.Section03
