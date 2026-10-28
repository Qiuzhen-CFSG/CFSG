module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SymplecticFour.Coordinates
/-!
# Excluding the original quasisimple symplectic row

The generalized Fitting subgroup of the actual offender supplement is the
ambient two-residual. Its original B.5.1 central quotient retains the full
normalizer action. A natural Sp4 mark therefore supplies two proper invariant
parabolics and contradicts the original minimal-parabolic hypothesis.
The final theorem applies this directly to the source B.5.1 conclusion.

Source: Aschbacher–Smith B.6.9 and E.2.3, printed pp.116 and 216–217.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
/-- The original quasisimple central quotient cannot be natural Sp4 over a nonbinary field. -/
theorem source_quasisimple_symplectic_excluded
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (s : MovedSection (ρ.comp Y.subtype) (generalizedFitting Y))
    (F : BinaryField) (hF : 1 < F.degree)
    (h : ActionEquiv (s.action.comp (generalizedFitting Y).subtype) (binarySymplectic F)) :
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
  let b := sourceMovedNormalizerActionEquiv ρ Y (generalizedFitting Y) s
  let e := b.groupEquiv.trans h.groupEquiv
  let f := b.linearEquiv.trans h.linearEquiv
  have hi (l : L₀) (v : s.space.toSubmodule ⧸ s.central.toSubmodule) :
      f (τ l v) = symplecticNatural 2 (e l) (f v) := by
    exact (congrArg h.linearEquiv (b.intertwines l v)).trans (h.intertwines _ _)
  have hc : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact (show 2^1 < 2^F.degree from Nat.pow_lt_pow_right (by decide) hF)
  exact (not_minimalParabolic_of_symplectic_coordinates S L₀ hgen₀ τ e f hi hc) hp₀

/-- The literal offender B.5.1 conclusion cannot have the nonbinary natural Sp4 row. -/
theorem source_offender_quasisimple_symplectic_exclusion [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ)))
    (F : BinaryField) (hF : 1 < F.degree) :
    ¬ Nonempty (ActionEquiv
      (c.sectionData.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype)
      (binarySymplectic F)) := by
  let := offenderSubgroup_normal ρ
  have hg := (offender_generation T hP ρ hff hcore).2
  rintro ⟨e⟩
  exact source_quasisimple_symplectic_excluded ρ T hP _ hg hq c.sectionData F hF e
end CFSG.Quasithin.ChapterB
