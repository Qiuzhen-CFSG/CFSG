module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.FactorOrbit
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import CFSG.Quasithin.ChapterB.Section06To07.OffenderGeneration
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleNormalizer
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
/-!
# Actual quasisimple source residual and SL3 exclusions

A quasisimple generalized Fitting subgroup of the original normal offender
supplement is characteristic. Its embedded Sylow orbit is therefore itself,
and minimal parabolicity identifies it with the original two-residual.
The same B.5.1 moved section and central quotient carry the full normalizer
action. Their natural or repeated-natural SL3 coordinates would give two
proper invariant parabolics, contradicting the source minimal parabolic.

The final theorem applies both exclusions to the actual B.5.1 conclusion
on the original offender action. No source chart, component orbit or extra
residual identity is assumed.
Source: Aschbacher–Smith B.5.1 and B.6.9, pp.99–103 and 115–116.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- The marked quasisimple fitting subgroup is the original two-residual. -/
theorem source_quasisimple_fitting_eq_residual
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y)) :
    (generalizedFitting Y).map Y.subtype = pResidual 2 G ∧
      IsQuasisimple (pResidual 2 G) := by
  let A := generalizedFitting Y
  let L := A.map Y.subtype
  let := hq
  let e := A.equivMapOfInjective Y.subtype Y.subtype_injective
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (A ⧸ center A) := hq.simple
  let : Nontrivial A := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center A))
  let : Nontrivial L := e.toEquiv.symm.nontrivial
  have hn : (⊤ : Subgroup G) ≤ normalizer (L : Set G) := by
    have hh := normalizer_le_normalizer_characteristic_image Y A
    rwa [normalizer_eq_top] at hh
  let : L.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  have hy : Y ≤ normalizer (L : Set G) := le_normalizer_of_normal
  have ho := source_factor_orbit_eq_residual T hP Y L hy hgen
  have he : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm (iSup_le fun t => ?_) (le_componentOrbit L _)
    exact (normal_iff_map_conj_eq.mp (inferInstance : L.Normal) t).le
  have hL : L = pResidual 2 G := he.symm.trans ho
  exact ⟨hL,hL ▸ (inferInstance : IsQuasisimple L)⟩

open QuasisimpleSource
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual repeated-natural SL3 moved row is impossible over every binary field. -/
theorem source_quasisimple_repeated_three_excluded
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (s : MovedSection (ρ.comp Y.subtype) (generalizedFitting Y))
    (F : BinaryField) (r : ℕ) (hr : 0 < r)
    (h : IsRepeatedLinearNatural (s.space.toRepresentation.comp (generalizedFitting Y).subtype) F 3 r) :
    False := by
  have he := (source_quasisimple_fitting_eq_residual T hP Y hgen hq).1
  let L := (generalizedFitting Y).map Y.subtype
  have hL : L = pResidual 2 G := he
  let : L.Normal := hL ▸ (inferInstance : (pResidual 2 G).Normal)
  have hn : normalizer (L : Set G) = ⊤ := normalizer_eq_top L
  let N := normalizer (L : Set G)
  let eg : N ≃* G := (MulEquiv.subgroupCongr hn).trans Subgroup.topEquiv
  let S := T.mapSurjective (f := eg.symm.toMonoidHom) eg.symm.surjective
  let L₀ := L.subgroupOf N
  let τ := (sourceMovedNormalizerSpace ρ Y (generalizedFitting Y) s).toRepresentation
  have hT : (S : Subgroup N) = (T : Subgroup G).map eg.symm.toMonoidHom := rfl
  have hLL : L₀.map eg.toMonoidHom = L := by
    change L₀.map N.subtype = L
    exact map_subgroupOf_eq_of_le L.le_normalizer
  have hgen₀ : L₀ ⊔ (S : Subgroup N) = ⊤ := by
    apply Subgroup.map_injective (f := eg.toMonoidHom) eg.injective
    rw [Subgroup.map_sup,hLL,hT,Subgroup.map_map]
    have hei : eg.toMonoidHom.comp eg.symm.toMonoidHom = MonoidHom.id G := by ext; simp
    rw [hei,Subgroup.map_id,hL,pResidual_sup_sylow_eq_top T]
    exact (map_top_of_surjective _ eg.surjective).symm
  have hp₀ : IsMinimalParabolicOver S ⊤ := by
    exact minimalParabolic_map_of_kernel_le_core T hP eg.symm.toMonoidHom
      eg.symm.surjective (by rw [(eg.symm.toMonoidHom.ker_eq_bot_iff).mpr eg.symm.injective]; exact bot_le)
  exact (not_minimalParabolic_of_repeated_natural_three S L₀ hgen₀ τ F r hr
    (source_moved_normalizer_repeated_natural ρ Y (generalizedFitting Y) s F 3 r h)) hp₀
/-- The actual natural SL3 central-quotient row is impossible over every binary field. -/
theorem source_quasisimple_natural_three_excluded
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (s : MovedSection (ρ.comp Y.subtype) (generalizedFitting Y))
    (F : BinaryField)
    (h : IsLinearNatural (s.action.comp (generalizedFitting Y).subtype) F 3) :
    False := by
  have he := (source_quasisimple_fitting_eq_residual T hP Y hgen hq).1
  let L := (generalizedFitting Y).map Y.subtype
  have hL : L = pResidual 2 G := he
  let : L.Normal := hL ▸ (inferInstance : (pResidual 2 G).Normal)
  have hn : normalizer (L : Set G) = ⊤ := normalizer_eq_top L
  let N := normalizer (L : Set G)
  let eg : N ≃* G := (MulEquiv.subgroupCongr hn).trans Subgroup.topEquiv
  let S := T.mapSurjective (f := eg.symm.toMonoidHom) eg.symm.surjective
  let L₀ := L.subgroupOf N
  let τ := sourceMovedNormalizerRepresentation ρ Y (generalizedFitting Y) s
  have hT : (S : Subgroup N) = (T : Subgroup G).map eg.symm.toMonoidHom := rfl
  have hLL : L₀.map eg.toMonoidHom = L := by
    change L₀.map N.subtype = L
    exact map_subgroupOf_eq_of_le L.le_normalizer
  have hgen₀ : L₀ ⊔ (S : Subgroup N) = ⊤ := by
    apply Subgroup.map_injective (f := eg.toMonoidHom) eg.injective
    rw [Subgroup.map_sup,hLL,hT,Subgroup.map_map]
    have hei : eg.toMonoidHom.comp eg.symm.toMonoidHom = MonoidHom.id G := by ext; simp
    rw [hei,Subgroup.map_id,hL,pResidual_sup_sylow_eq_top T]
    exact (map_top_of_surjective _ eg.surjective).symm
  have hp₀ : IsMinimalParabolicOver S ⊤ := by
    exact minimalParabolic_map_of_kernel_le_core T hP eg.symm.toMonoidHom
      eg.symm.surjective (by rw [(eg.symm.toMonoidHom.ker_eq_bot_iff).mpr eg.symm.injective]; exact bot_le)
  exact (not_minimalParabolic_of_natural_three S L₀ hgen₀ τ F
    (source_moved_normalizer_natural ρ Y (generalizedFitting Y) s F 3 h)) hp₀

/-- The literal offender-group B.5.1 conclusion has neither SL3 action row. -/
theorem source_offender_quasisimple_three_exclusions [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    (∀ F, ¬ IsLinearNatural
      (c.sectionData.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype) F 3) ∧
    (∀ F r, 0 < r → ¬ IsRepeatedLinearNatural
      (c.sectionData.space.toRepresentation.comp (generalizedFitting (offenderSubgroup ρ)).subtype)
      F 3 r) := by
  let := offenderSubgroup_normal ρ
  have hg := (offender_generation T hP ρ hff hcore).2
  exact ⟨fun F h => source_quasisimple_natural_three_excluded ρ T hP _ hg hq c.sectionData F h,
    fun F r hr h => source_quasisimple_repeated_three_excluded ρ T hP _ hg hq c.sectionData F r hr h⟩
end CFSG.Quasithin.ChapterB
