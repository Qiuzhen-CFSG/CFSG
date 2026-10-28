module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.SourceLocal
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Orbits
public import Theory.GroupTheory.CharacteristicNormalizerClosure
public import Stellmacher.BaumannMap
/-!
# The actual outside block from a selected characteristic-pair application

A characteristic subgroup of Baum(T) is characteristic inside T. Hence
normality of either nontrivial pair member in an escaping selected group
contradicts characteristic-normalizer control. C.1.18 therefore produces
its actual residual block. The residual of O²(G) Baum(T) maps to O²(G),
so the source block is retained in the original ambient group.

Source: Aschbacher–Smith C.1.26–28, pp.132–133.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem characteristic_map_equivalence {A H : Type*} [Group A] [Group H]
    (e : A ≃* H) (C : Subgroup A) [C.Characteristic] : (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy,?_⟩
  exact e.apply_symm_apply (a (e y))

omit [Finite G] in
theorem characteristic_baumann_normalizer_le_control (T : Subgroup G)
    (D : Subgroup (baumann T)) [D.Characteristic] (hne : D ≠ ⊥) :
    normalizer (D.map (baumann T).subtype : Set G) ≤ T.characteristicNormalizerClosure := by
  let B := (baumann T).subgroupOf T
  have hB : B = baumann (⊤ : Subgroup T) := by
    apply map_injective T.subtype_injective
    rw [map_subgroupOf_eq_of_le (show baumann T ≤ T from inf_le_left)]
    symm
    change ((⊤ : Subgroup T) ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (⊤ : Subgroup T)) : Set T)).map T.subtype = _
    rw [baumann_map_injective T.subtype T.subtype_injective,
      ←MonoidHom.range_eq_map,range_subtype]
    rfl
  let : B.Characteristic := hB ▸ baumann_characteristic
  let e := (subgroupOfEquivOfLe (show baumann T ≤ T from inf_le_left)).symm
  let E := D.map e.toMonoidHom
  let : E.Characteristic := characteristic_map_equivalence e D
  let C := E.map B.subtype
  let : C.Characteristic := inferInstance
  have hE : E ≠ ⊥ := fun he => hne ((D.map_eq_bot_iff_of_injective e.injective).mp he)
  have hC : C ≠ ⊥ := fun hc => hE ((E.map_eq_bot_iff_of_injective B.subtype_injective).mp hc)
  have hm : C.map T.subtype = D.map (baumann T).subtype := by
    rw [map_map,map_map]
    rfl
  rw [←hm]
  exact normalizer_le_characteristicNormalizerClosure T C hC

theorem blockAlternative_of_selected_outside
    (T : Subgroup G) (N M : Subgroup G) (hBN : baumann T ≤ N)
    (hcpu : T.characteristicNormalizerClosure ≤ M) (hout : ¬ N ≤ M)
    (P : CharacteristicPair (baumann T)) (hP : P.Universal.{u,u})
    (hlocal : InLocalClass (inclusion hBN)) : BlockAlternative N := by
  have kill (D : Subgroup (baumann T)) [D.Characteristic] (hne : D ≠ ⊥)
      (hn : (D.map (inclusion hBN)).Normal) : False := by
    let : (D.map (inclusion hBN)).Normal := hn
    have hN : N ≤ normalizer (D.map (baumann T).subtype : Set G) := by
      have h := (D.map (inclusion hBN)).le_normalizer_map N.subtype
      rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,map_map] at h
      exact h
    exact hout (hN.trans ((characteristic_baumann_normalizer_le_control T D hne).trans hcpu))
  let := P.first_characteristic
  let := P.second_characteristic
  rcases hP N (inclusion hBN) hlocal with hc | hn | hb
  · exact (kill P.first P.first_ne_bot ((hlocal.first_normal_iff_central
      P.first P.first_le_omegaCenter).mpr hc)).elim
  · exact (kill P.second P.second_ne_bot hn).elim
  · exact hb

theorem selected_residual_map (T : Sylow 2 G) :
    (pResidual 2 (pResidual 2 G ⊔ baumann (T : Subgroup G) : Subgroup G)).map
      (pResidual 2 G ⊔ baumann (T : Subgroup G)).subtype = pResidual 2 G := by
  let X := pResidual 2 G
  let B := baumann (T : Subgroup G)
  let N := X ⊔ B
  let A := X.subgroupOf N
  have hpA : IsPPerfect 2 A := (isPPerfect_pResidual 2).of_surjective
    (subgroupOfEquivOfLe (show X ≤ N from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show X ≤ N from le_sup_left)).symm.surjective
  have hs : A ⊔ B.subgroupOf N = ⊤ := by
    apply map_injective N.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show X ≤ N from le_sup_left),
      map_subgroupOf_eq_of_le (show B ≤ N from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  have hres : pResidual 2 N = A := pResidual_eq_of_isPPerfect_sup A (B.subgroupOf N)
    hpA (T.isPGroup'.to_le (show B ≤ T from inf_le_left)).comap_subtype hs
  change (pResidual 2 N).map N.subtype = X
  rw [hres,map_subgroupOf_eq_of_le (show X ≤ N from le_sup_left)]

theorem chi_residual_of_selected_block (T : Sylow 2 G)
    (hb : BlockAlternative (pResidual 2 G ⊔ baumann (T : Subgroup G) : Subgroup G)) :
    IsChiBlockIn (pResidual 2 G) := by
  let N := pResidual 2 G ⊔ baumann (T : Subgroup G)
  let e := ((pResidual 2 N).equivMapOfInjective N.subtype N.subtype_injective).trans
    (MulEquiv.subgroupCongr (selected_residual_map T))
  have hc : IsChiBlock (pResidual 2 N) := by
    rcases hb.2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨3,by decide,h⟩
  exact ⟨⟨inferInstance,RankOne.Solvable.isShort_of_equiv e hb.1.short,
    (inferInstance : (pResidual 2 G).Normal).isSubnormal⟩,chi_of_equiv e hc⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
