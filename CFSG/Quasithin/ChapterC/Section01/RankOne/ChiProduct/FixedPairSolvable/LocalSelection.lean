module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Selection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Kernel
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Parabolic
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable
open ChapterB GlaubermanNiles FixedPair
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_baumann_le_control (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) :
    normalizer (baumann (T : Subgroup G) : Set G) ≤ control T D := by
  let := D.second_characteristic
  exact (normalizer_le_normalizer_characteristic_image _ D.second).trans le_sup_right

theorem exists_baumann_minimalParabolic_outside (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (E : Subgroup G) (hB : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G)) E)
    (hout : ¬ E ≤ control T D) :
    ∃ (N : Subgroup G), N ≤ E ∧ ¬ N ≤ control T D ∧
      ∃ S : Sylow 2 N, (S : Subgroup N).map N.subtype = baumann (T : Subgroup G) ∧
        IsMinimalParabolicOver S ⊤ := by
  obtain ⟨R,hR⟩ := hB
  have hn : normalizer (R : Set E) ≤ (control T D).subgroupOf E := by
    have hh := (R : Subgroup E).le_normalizer_map E.subtype
    rw [hR] at hh
    exact map_le_iff_le_comap.mp (hh.trans (normalizer_baumann_le_control T D))
  obtain ⟨P,hPs⟩ : ∃ P : Subgroup E,
      P ∈ nonNormalUniqueMaximalOvergroups (R : Subgroup E) ∧
      ¬ P ≤ (control T D).subgroupOf E := by
    by_contra! hh
    have hz : nonNormalUniqueMaximalClosure (R : Subgroup E) ⊔
        normalizer ((R : Subgroup E) : Set E) ≤ (control T D).subgroupOf E := by
      apply sup_le
      · exact sSup_le hh
      · exact hn
    have hgen := nonNormalUniqueMaximalClosure_sup_normalizer (R : Subgroup E)
    rw [hgen] at hz
    exact hout (subgroupOf_eq_top.mp (top_unique hz))
  have hRP : (R : Subgroup E) ≤ P := hPs.1.1.1.le
  have hP : IsMinimalParabolicOver R P := hPs.1
  let N := P.map E.subtype
  let hPN : P ≃* N := P.equivMapOfInjective E.subtype E.subtype_injective
  let S₀ := R.subtype hRP
  have hP₀ : IsMinimalParabolicOver S₀ ⊤ := by
    apply (isMinimalParabolicOver_top_iff _).mpr
    have hu := Solvable.uniqueMaximalContaining_of_minimalParabolic R P hP
    obtain ⟨A,hA,hRA,huniq⟩ := (uniqueMaximalContaining_top_iff _).mp hu
    refine ⟨⟨A,⟨hA,hRA⟩,fun B hB => huniq B hB.1 hB.2⟩,?_⟩
    intro hh
    exact hP.2 ((normal_subgroupOf_iff_le_normalizer hRP).mp hh)
  let S := S₀.mapSurjective (f := hPN.toMonoidHom) hPN.surjective
  have hS : (S : Subgroup N).map N.subtype = baumann (T : Subgroup G) := by
    change ((S₀ : Subgroup P).map hPN.toMonoidHom).map N.subtype = _
    rw [map_map]
    have hcomp : N.subtype.comp hPN.toMonoidHom = E.subtype.comp P.subtype := by
      ext x
      simp only [MonoidHom.comp_apply]
      change ((hPN x : N) : G) = E.subtype (P.subtype x)
      simpa only [hPN, Subgroup.coe_subtype] using
        P.coe_equivMapOfInjective_apply E.subtype E.subtype_injective x
    rw [hcomp]
    rw [← map_map]
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hRP,hR]
  have hSP : IsMinimalParabolicOver S ⊤ := by
    have hker : hPN.toMonoidHom.ker ≤ minimalParabolicCore S₀ hP₀ := by
      rw [hPN.toMonoidHom.ker_eq_bot hPN.injective]
      exact bot_le
    exact minimalParabolic_map_of_kernel_le_core S₀ hP₀ hPN.toMonoidHom
      hPN.surjective hker
  exact ⟨N,map_subtype_le _,fun hn => hPs.2 (map_le_iff_le_comap.mp hn),S,hS,hSP⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable
