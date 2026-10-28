module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CoreOvergroupCenter
public import Theory.GroupTheory.PRadical.NormalComponentImages

/-!
# Reductions for large-center radicals in the native J₄ model

Radical saturation puts the two-core of every containing local in the radical.
Self-centralization then bounds the radical's center by the local core's center.
The certified max2 and max4 bounds exclude those entire local branches, including
any isomorphic overgroup of the full radical normalizer. Separately, maximality
among two-locals identifies a local with the normalizer of its nontrivial core.

These are reductions toward the arbitrary-radical coverage used by An, O'Brien
and Wilson, LMS J. Comput. Math. 6 (2003), Section 4, p.122 and Table 1, p.124;
they do not assert that coverage. Radical saturation is Aschbacher--Smith C.2.1.
-/

public section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals

private theorem center_card_congr {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : Nat.card (center A) = Nat.card (center B) :=
  Nat.card_congr (centerCongr e).toEquiv

private theorem center_bound_of_normalizer_le
    (P M : Subgroup Model) (hP : IsPRadical 2 P)
    (hNM : normalizer (P : Set Model) ≤ M)
    (hC : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :
    Nat.card (center P) ≤ Nat.card (center (pCore 2 M)) := by
  have hPM : P ≤ M := P.le_normalizer.trans hNM
  have hQP : M.pCoreIn 2 ≤ P :=
    le_of_normalizer_le_normalizer_of_pCore_normalizer_le P (M.pCoreIn 2)
      hP.isPGroup (isPGroup_pCoreIn 2 M) hP.2.le
      (hNM.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))
  have hQ : pCore 2 M ≤ P.subgroupOf M := by
    intro x hx
    exact hQP (mem_map_of_mem M.subtype hx)
  have hb := center_card_le_of_centralizer_le (pCore 2 M) (P.subgroupOf M) hQ hC
  let eP : P.subgroupOf M ≃* P := subgroupOfEquivOfLe hPM
  have he := @center_card_congr (P.subgroupOf M) P inferInstance inferInstance eP
  exact he.symm.le.trans hb

/-- The denominator of the native normalizer quotient is the full intrinsic core. -/
theorem radical_core_eq (P : Subgroup Model) (hP : IsPRadical 2 P) :
    pCore 2 (normalizer (P : Set Model)) = P.subgroupOf (normalizer (P : Set Model)) := by
  apply map_injective (normalizer (P : Set Model)).subtype_injective
  rw [map_subgroupOf_eq_of_le P.le_normalizer]
  exact hP.2

private theorem core_center_card_congr {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : Nat.card (center (pCore 2 A)) = Nat.card (center (pCore 2 B)) := by
  let eP : pCore 2 A ≃* pCore 2 B :=
    (e.subgroupMap (pCore 2 A)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  exact Nat.card_congr (centerCongr eP).toEquiv

open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- No local isomorphic to max2 contains a large-center radical's whole normalizer. -/
theorem normalizer_not_le_max2 (P M : Subgroup Model) (hP : IsPRadical 2 P)
    (hlarge : 64 ≤ Nat.card (center P)) (e : M ≃* sourceSubgroup) :
    ¬ normalizer (P : Set Model) ≤ M := by
  intro hNM
  have hC : centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
    (@Theory.Quasithin.centralizer_pCore_le_iff M sourceSubgroup
      M.toGroup sourceSubgroup.toGroup 2 e).mpr max2_twoCore_centralizer_le
  have hb := center_bound_of_normalizer_le P M hP hNM hC
  rw [@core_center_card_congr M sourceSubgroup inferInstance inferInstance e] at hb
  have hs := max2_twoCore_center_card_le_two
  omega

/-- No local isomorphic to max4 contains a large-center radical's whole normalizer. -/
theorem normalizer_not_le_max4 (P M : Subgroup Model) (hP : IsPRadical 2 P)
    (hlarge : 64 ≤ Nat.card (center P)) (e : M ≃* SymmetricLinear.max4Subgroup) :
    ¬ normalizer (P : Set Model) ≤ M := by
  intro hNM
  have hC : centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
    (@Theory.Quasithin.centralizer_pCore_le_iff M SymmetricLinear.max4Subgroup
      M.toGroup SymmetricLinear.max4Subgroup.toGroup 2 e).mpr
        SymmetricLinear.max4_twoCore_centralizer_le
  have hb := center_bound_of_normalizer_le P M hP hNM hC
  rw [@core_center_card_congr M SymmetricLinear.max4Subgroup
    inferInstance inferInstance e] at hb
  have hs := SymmetricLinear.max4_twoCore_center_card_le_eight
  omega

/-- A maximal two-local with large core center is the full normalizer of that
radical core. The center bound transfers to its actual ambient image. -/
theorem maximal_local_core_radical (M : Subgroup Model) (hM : IsMaximalTwoLocal M)
    (hlarge : 64 ≤ Nat.card (center (pCore 2 M))) :
    IsPRadical 2 (M.pCoreIn 2) ∧
      normalizer (M.pCoreIn 2 : Set Model) = M ∧
      64 ≤ Nat.card (center (M.pCoreIn 2)) := by
  let ec : pCore 2 M ≃* M.pCoreIn 2 :=
    (pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective
  have he := @center_card_congr (pCore 2 M) (M.pCoreIn 2) inferInstance inferInstance ec
  have hz : 64 ≤ Nat.card (center (M.pCoreIn 2)) := hlarge.trans_eq he
  have hne : M.pCoreIn 2 ≠ ⊥ := by
    intro hbot
    have hbound := hz.trans (center (M.pCoreIn 2)).card_le_card_group
    rw [hbot, card_bot] at hbound
    omega
  have hn : M ≤ normalizer (M.pCoreIn 2 : Set Model) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hloc : IsTwoLocal (normalizer (M.pCoreIn 2 : Set Model)) :=
    ⟨M.pCoreIn 2, hne, isPGroup_pCoreIn 2 M, rfl⟩
  have hnorm : normalizer (M.pCoreIn 2 : Set Model) = M :=
    le_antisymm (hM.2 hloc hn) hn
  refine ⟨⟨hne, ?_⟩, hnorm, hz⟩
  rw [hnorm]
  rfl

end Janko4.LocalStructure.LargeCenterRadicals
