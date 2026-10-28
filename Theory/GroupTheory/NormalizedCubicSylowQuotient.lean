module
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.PerfectSmallNormalizer
public import Theory.GroupTheory.TwoPerfectCubicSylow

/-!
# Sylow overgroups of a normalized cubic lift

Let an ambient Sylow two-subgroup T normalize Y, with |Y/O₂(Y)| = 3.
Its intersection with Y is precisely O₂(Y), so T has index three in YT.
If [Y,T] is not contained in O₂(Y), then T is not normal in YT. The
three-coset action therefore identifies YT/O₂(YT) with S₃.

Normality is relative to YT throughout. In particular, no ambient
normality of Y or of the intrinsic two-core of Y is assumed.

Source application: the cubic overgroups in the reducible Sylow step
of Aschbacher–Smith 14.7.9 and 14.7.15(2), printed pp.1045,1047,
and the quotient premise of 14.5.3, printed p.1013.
-/

open Subgroup
public noncomputable section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- A normalized subgroup with cubic two-core quotient has an S₃ Sylow
overgroup quotient when the Sylow acts nontrivially modulo that core. -/
theorem cubic_sylow_join_symmetricThree
    (T : Sylow 2 G) (Y : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hm : ¬ ⁅Y,(T : Subgroup G)⁆ ≤ Y.pCoreIn 2) :
    Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃*
      Equiv.Perm (Fin 3)) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T Y hn
  have hcore : (T : Subgroup G).subgroupOf Y = pCore 2 Y :=
    hP.symm.trans (P.eq_twoCore_of_cubic_quotient hc)
  let J := Y ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hi : (S : Subgroup J).index = 3 := by
    change (T : Subgroup G).relIndex J = 3
    rw [relIndex_sup_of_normalizes_left Y (T : Subgroup G) hn]
    change ((T : Subgroup G).subgroupOf Y).index = 3
    rw [hcore]
    exact hc
  apply sylow_index_three_core_quotient S hi
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S)
  intro he
  have hSN : ((T : Subgroup G).subgroupOf J).Normal := by
    change (S : Subgroup J).Normal
    rw [←he]
    infer_instance
  have hnorm : J ≤ normalizer (T : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show (T : Subgroup G) ≤ J from le_sup_right)).mp hSN
  apply hm
  have hle : ⁅Y,(T : Subgroup G)⁆ ≤ (T : Subgroup G) ⊓ Y :=
    le_inf (le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hnorm))
      (le_normalizer_iff_commutator_le_left.mp hn)
  have heq : (T : Subgroup G) ⊓ Y = Y.pCoreIn 2 := by
    rw [←subgroupOf_map_subtype,hcore]
    rfl
  exact hle.trans_eq heq
end Subgroup
