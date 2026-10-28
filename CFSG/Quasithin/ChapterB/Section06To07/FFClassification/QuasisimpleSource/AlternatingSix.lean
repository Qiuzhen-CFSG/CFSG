module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource.Irreducible
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.AlternatingSix.Natural
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
/-!
# The original A6 and binary symplectic rows are excluded

The actual quasisimple fitting subgroup embeds as the ambient two-residual.
The same moved central quotient carries its full normalizer action. Natural
A6 coordinates, and hence every faithful A6 four-space, give a six-letter
image containing A6. Its two Sylow parabolics contradict minimal parabolicity.
The original B.5.1 consumer derives its own faithful irreducible branch.

Source: Aschbacher–Smith B.6.9, printed p.116.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
/-- The natural A6 row cannot occur on the original central quotient. -/
theorem source_quasisimple_natural_six_excluded
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (s : MovedSection (ρ.comp Y.subtype) (generalizedFitting Y))
    (h : ActionEquiv (s.action.comp (generalizedFitting Y).subtype) (alternatingNatural 6)) :
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
  have hp₀ : IsMinimalParabolicOver S ⊤ := by
    exact minimalParabolic_map_of_kernel_le_core T hP eg.symm.toMonoidHom
      eg.symm.surjective (by rw [(eg.symm.toMonoidHom.ker_eq_bot_iff).mpr eg.symm.injective]; exact bot_le)
  let b := sourceMovedNormalizerActionEquiv ρ Y (generalizedFitting Y) s
  let c : ActionEquiv (τ.comp L₀.subtype) (alternatingNatural 6) := {
    groupEquiv := b.groupEquiv.trans h.groupEquiv
    linearEquiv := b.linearEquiv.trans h.linearEquiv
    intertwines := fun l v => (congrArg h.linearEquiv (b.intertwines l v)).trans (h.intertwines _ _) }
  exact not_minimalParabolic_of_natural_alternatingSix S L₀ τ c hp₀

/-- Every faithful A6 four-space on that quotient has the same obstruction. -/
theorem source_quasisimple_fourSpace_six_excluded [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (s : MovedSection (ρ.comp Y.subtype) (generalizedFitting Y))
    (e : generalizedFitting Y ≃* alternatingGroup (Fin 6))
    (hf : Function.Injective s.action)
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) :
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
  have hp₀ : IsMinimalParabolicOver S ⊤ := by
    exact minimalParabolic_map_of_kernel_le_core T hP eg.symm.toMonoidHom
      eg.symm.surjective (by rw [(eg.symm.toMonoidHom.ker_eq_bot_iff).mpr eg.symm.injective]; exact bot_le)
  let b := sourceMovedNormalizerActionEquiv ρ Y (generalizedFitting Y) s
  have hi : Function.Injective (τ.comp L₀.subtype) := by
    intro x y heq
    apply b.groupEquiv.injective
    apply (hf.comp (generalizedFitting Y).subtype_injective)
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := b.linearEquiv.surjective v
    exact (b.intertwines x w).symm.trans
      ((congrArg b.linearEquiv (LinearMap.congr_fun heq w)).trans (b.intertwines y w))
  exact not_minimalParabolic_of_alternatingSix_fourSpace S L₀ τ (b.groupEquiv.trans e) hi hd hp₀

/-- The literal binary derived symplectic marking yields the forbidden A6 four-space. -/
theorem source_quasisimple_symplecticTwo_excluded [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (s : MovedSection (ρ.comp Y.subtype) (generalizedFitting Y))
    (hf : Function.Injective s.action) (H : Subgroup Y)
    (e : MarkedActionEquiv s.action H (generalizedFitting Y)
      (symplecticNatural (k := ZMod 2) 2) (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) : False := by
  let eg := e.subgroupEquiv.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (F := ZMod 2) (by simp))
  have hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4 := by
    rw [e.action.linearEquiv.finrank_eq]
    simp
  exact source_quasisimple_fourSpace_six_excluded ρ T hP Y hgen hq s eg hf hd

/-- Both A6 and binary symplectic B.4.2 rows are excluded in the original section. -/
theorem source_offender_quasisimple_six_exclusions [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    ¬ Nonempty (ActionEquiv
      (c.sectionData.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype)
      (alternatingNatural 6)) ∧
    ¬ Nonempty (MarkedActionEquiv c.sectionData.action (offenderSubgroup c.sectionData.action)
      (generalizedFitting (offenderSubgroup ρ)) (symplecticNatural (k := ZMod 2) 2)
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) := by
  let := offenderSubgroup_normal ρ
  have hg := (offender_generation T hP ρ hff hcore).2
  have hf := (source_offender_quasisimple_irreducible ρ T hP hff hcore hq c).2.1
  exact ⟨fun ⟨e⟩ => source_quasisimple_natural_six_excluded ρ T hP _ hg hq c.sectionData e,
    fun ⟨e⟩ => source_quasisimple_symplecticTwo_excluded ρ T hP _ hg hq c.sectionData hf _ e⟩
end CFSG.Quasithin.ChapterB
