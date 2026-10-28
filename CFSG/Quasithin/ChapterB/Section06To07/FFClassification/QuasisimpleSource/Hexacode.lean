module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource.Irreducible
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.AlternatingSix.Hexacode
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.HexacodeEven
public import Theory.Alternating.OddCentralCovers
public import Theory.Representation.Quotient
/-!
# Excluding the original triple-A6 quasisimple row

The marked center and quotient identify the source component with the actual
even hexacode cover. Its faithful irreducible six-space has the established
even hexacode coordinates. Extend the original moved central-quotient action
to its full normalizer and apply the six-letter image obstruction. The
original B.5.1 consumer supplies faithfulness and irreducibility internally.

Source: Aschbacher–Smith B.6.9 and K.1.3, printed pp.116 and 453.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Atlas.Codes
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
/-- The actual even-hexacode mark contradicts the original source minimal parabolic. -/
theorem source_quasisimple_even_hexacode_excluded
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (s : MovedSection (ρ.comp Y.subtype) (generalizedFitting Y))
    (h : ActionEquiv (s.action.comp (generalizedFitting Y).subtype) (Hexacode.evenAction)) :
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
  let c : ActionEquiv (τ.comp L₀.subtype) (Hexacode.evenAction) := {
    groupEquiv := b.groupEquiv.trans h.groupEquiv
    linearEquiv := b.linearEquiv.trans h.linearEquiv
    intertwines := fun l v => (congrArg h.linearEquiv (b.intertwines l v)).trans (h.intertwines _ _) }
  exact not_minimalParabolic_of_even_hexacode S L₀ τ c hp₀

/-- The source triple-cover row constructs its own hexacode mark before exclusion. -/
theorem source_quasisimple_tripleSix_excluded [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (s : MovedSection (ρ.comp Y.subtype) (generalizedFitting Y))
    (hf : Function.Injective s.action)
    (hi : IsIrreducible (s.action.comp (generalizedFitting Y).subtype))
    (a : SourceInduction.ProjectiveLine.TripleSixAction s.action (generalizedFitting Y)) : False := by
  let := hq
  have hc : Nat.card (center (generalizedFitting Y)) = 3 := by
    rw [Nat.card_congr a.centerEquiv.toEquiv]
    simp
  obtain ⟨q⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode a.quotientEquiv hc
  let τ := (s.action.comp (generalizedFitting Y).subtype).comp q.symm.toMonoidHom
  have ht : Function.Injective τ :=
    (hf.comp (generalizedFitting Y).subtype_injective).comp q.symm.injective
  have hir : IsIrreducible τ :=
    (irreducible_comp_surjective_iff q.symm.toMonoidHom q.symm.surjective _).mpr hi
  obtain ⟨e⟩ := ChapterK.Alternating.EvenRecognition.exists_actionEquiv τ ht hir a.dimension
  let c : ActionEquiv (s.action.comp (generalizedFitting Y).subtype) Hexacode.evenAction := {
    groupEquiv := q.trans e.groupEquiv
    linearEquiv := e.linearEquiv
    intertwines := by
      intro l v
      have he := e.intertwines (q l) v
      simpa only [τ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
        q.symm_apply_apply,MulEquiv.trans_apply] using he }
  exact source_quasisimple_even_hexacode_excluded ρ T hP Y hgen hq s c

/-- The literal original B.5.1 section cannot have the triple-six action row. -/
theorem source_offender_quasisimple_tripleSix_excluded [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    ¬ Nonempty (SourceInduction.ProjectiveLine.TripleSixAction c.sectionData.action
      (generalizedFitting (offenderSubgroup ρ))) := by
  let := offenderSubgroup_normal ρ
  have hg := (offender_generation T hP ρ hff hcore).2
  have hi := source_offender_quasisimple_irreducible ρ T hP hff hcore hq c
  rintro ⟨a⟩
  exact source_quasisimple_tripleSix_excluded ρ T hP _ hg hq c.sectionData hi.2.1 hi.2.2.1 a
end CFSG.Quasithin.ChapterB
