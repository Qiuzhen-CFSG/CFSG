module

public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalHypotheses
public import Theory.GroupTheory.CharacteristicNormalizerClosure

/-!
# Characteristic-normalizer control for the original RK

Every normalizer in H of a nontrivial characteristic subgroup of R
contains T_H and is proper. The unique maximal subgroup over T_H
therefore contains all these normalizers. Restricting to the actual
Sylow subgroup of RK supplies the C(RK,R) hypothesis of C.1.29.
This argument does not assert that RK is a minimal parabolic.

Source: Aschbacher–Smith C.5.3, printed pp.154–155, using C.1.26–29.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G]
variable {H M K R T : Subgroup G} (d : OriginalHypotheses H M K R T)
include d

/-- Characteristic two passes to the actual normal subgroup RK of H. -/
theorem OriginalHypotheses.residual_join_fitting :
    generalizedFitting (R ⊔ K : Subgroup G) = pCore 2 (R ⊔ K : Subgroup G) := by
  let J := (R ⊔ K).subgroupOf H
  let : J.Normal := d.residual_join_normal
  have hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    rw [← d.fitting]
    exact centralizer_generalizedFitting_le H
  have hJ := normal_core_selfCentralizing hc J
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    ((Theory.Quasithin.centralizer_pCore_le_iff 2
      (subgroupOfEquivOfLe (sup_le d.R_le_H d.K_le_H))).mp hJ)

/-- Each defining characteristic normalizer is contained in the unique
maximal subgroup of H over T_H. -/
theorem OriginalHypotheses.characteristic_normalizer_le_maximal
    (N : Subgroup H) (hN : (d.sylow : Subgroup H) ≤ N ∧ IsCoatom N)
    (C : Subgroup R) [C.Characteristic] (hC : C ≠ ⊥) :
    (normalizer (C.map R.subtype : Set G)).subgroupOf H ≤ N := by
  have hTC : T ≤ normalizer (C.map R.subtype : Set G) :=
    (d.T_le.trans d.R_normal).trans (normalizer_le_normalizer_characteristic_image R C)
  have hTN : (d.sylow : Subgroup H) ≤
      (normalizer (C.map R.subtype : Set G)).subgroupOf H := by
    intro t ht
    exact hTC (d.sylow_image ▸ mem_map_of_mem H.subtype ht)
  apply d.unique.le_maximal ⟨hN.1,hN.2.covBy_top⟩ hTN
  apply lt_top_iff_ne_top.mpr
  intro he
  have hHC : H ≤ normalizer (C.map R.subtype : Set G) := by
    intro h hh
    exact (show (⟨h,hh⟩ : H) ∈
      (normalizer (C.map R.subtype : Set G)).subgroupOf H from he ▸ mem_top _)
  apply d.characteristic_not_normal C hC
  exact (normal_subgroupOf_iff_le_normalizer
    ((show C.map R.subtype ≤ R from map_subtype_le _).trans le_sup_left)).mpr
    ((sup_le d.R_le_H d.K_le_H).trans hHC)

omit [Finite G] d in
private theorem characteristic_map_equivalence {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
  exact e.apply_symm_apply (a (e y))

/-- The literal original Sylow subgroup of RK has characteristic-normalizer
closure inside the restriction of the unique maximal subgroup of H. -/
theorem OriginalHypotheses.residual_characteristic_control
    (N : Subgroup H) (hN : (d.sylow : Subgroup H) ≤ N ∧ IsCoatom N) :
    (d.residual_sylow : Subgroup (R ⊔ K : Subgroup G)).characteristicNormalizerClosure ≤
      (N.map H.subtype).subgroupOf (R ⊔ K) := by
  let J := R ⊔ K
  let P : Subgroup J := d.residual_sylow
  let e : P ≃* R := (equivMapOfInjective P J.subtype J.subtype_injective).trans
    (MulEquiv.subgroupCongr d.residual_sylow_image)
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro C hC hCne
  let := hC
  let D := C.map e.toMonoidHom
  let : D.Characteristic := characteristic_map_equivalence e C
  have hDne : D ≠ ⊥ := fun he => hCne ((C.map_eq_bot_iff_of_injective e.injective).mp he)
  have himage : (C.map P.subtype).map J.subtype = D.map R.subtype := by
    rw [Subgroup.map_map,Subgroup.map_map]
    rfl
  intro x hx
  have hxC : (x : G) ∈ normalizer (D.map R.subtype : Set G) := by
    rw [←himage]
    exact (C.map P.subtype).le_normalizer_map J.subtype (mem_map_of_mem J.subtype hx)
  have hxH : (x : G) ∈ H := (sup_le d.R_le_H d.K_le_H) x.property
  have hxN := d.characteristic_normalizer_le_maximal N hN D hDne
    (show (⟨(x : G),hxH⟩ : H) ∈
      (normalizer (D.map R.subtype : Set G)).subgroupOf H from hxC)
  exact mem_map_of_mem H.subtype hxN

/-- The controlling subgroup used in C.1.29 is genuinely proper in RK. -/
theorem OriginalHypotheses.residual_maximal_restriction_ne_top
    (N : Subgroup H) (hN : (d.sylow : Subgroup H) ≤ N ∧ IsCoatom N) :
    (N.map H.subtype).subgroupOf (R ⊔ K) ≠ ⊤ := by
  intro he
  have hKN : K ≤ N.map H.subtype := by
    intro k hk
    exact (show (⟨k,(show K ≤ R ⊔ K from le_sup_right) hk⟩ : (R ⊔ K : Subgroup G)) ∈
      (N.map H.subtype).subgroupOf (R ⊔ K) from he ▸ mem_top _)
  have hTN : T ≤ N.map H.subtype := by
    rw [←d.sylow_image]
    exact map_mono hN.1
  have hHN : H ≤ N.map H.subtype := d.residual_sup_sylow.symm.le.trans (sup_le hKN hTN)
  have hNt : N = ⊤ := by
    apply map_injective H.subtype_injective
    rw [←MonoidHom.range_eq_map,H.range_subtype]
    exact le_antisymm (map_subtype_le _) hHN
  exact hN.2.ne_top hNt

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
