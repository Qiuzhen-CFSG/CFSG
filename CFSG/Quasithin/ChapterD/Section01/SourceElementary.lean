module
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceThompson
public import Theory.Representation.BinaryOffender.ConjugateSpan

/-!
# Genuine elementary and parabolic qrc reductions

If the original module is not FF and lies in the second two-core, every
conjugate lies in the first local group. The actual conjugate-pair theorem
makes its span elementary. Thompson heredity and the common-normal condition
then exclude J(R) from the second two-core, so the original unique maximal
overgroup makes the second group a minimal parabolic. All actions and cores
are the literal ones from QRCConfiguration, without a rank certificate.
Source: Aschbacher–Smith, D.1.2(1–4), printed pp.172–173.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}
theorem source_elementary_span_of_notFF
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hnf : letI := d.module_elementary
      ¬ Representation.BinaryOffender.IsFFModule (imageRepresentation G₁ V d.module_normalized)) :
    IsElementaryAbelian 2 (conjugateSpan G₂ V) := by
  let := d.finite_left
  let := d.module_elementary
  let : Finite V := Finite.of_injective (inclusion d.module_le) (inclusion_injective d.module_le)
  let f := actionHom G₁ V d.module_normalized
  let : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  rw [conjugateSpan_eq]
  apply Representation.BinaryOffender.conjugateSpan_elementary_of_notFF G₁ G₂ V
    f.rangeRestrict (imageRepresentation G₁ V d.module_normalized)
      (by rw [MonoidHom.ker_rangeRestrict,actionHom_ker]) (fun _ _ => rfl) ?_ hnf
  intro g hg
  have hc : (twoCoreIn G₂).map (MulAut.conj g).toMonoidHom = twoCoreIn G₂ :=
    mem_normalizer_iff_map_conj_eq.mp (twoCore_normalized G₂ hg)
  exact ((map_mono hV).trans_eq hc).trans ((right_core_le_sylow d).trans (sylow_le_left d))
end CFSG.Quasithin.ChapterD.UniqueFactor

namespace CFSG.Quasithin.ChapterD.UniqueFactor
open Stellmacher
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}
theorem source_thompson_core_not_le_right_core_of_notFF
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥)
    (hnf : letI := d.module_elementary
      ¬ Representation.BinaryOffender.IsFFModule (imageRepresentation G₁ V d.module_normalized)) :
    ¬ elementaryAbelianMaxJ (twoCoreIn G₁) ≤ twoCoreIn G₂ := by
  let := d.finite_left
  let R := twoCoreIn G₁
  let : Finite R := Finite.of_injective (inclusion (twoCore_le G₁))
    (inclusion_injective (twoCore_le G₁))
  let : Finite T := Finite.of_injective (inclusion (sylow_le_left d))
    (inclusion_injective (sylow_le_left d))
  have hJR : elementaryAbelianMaxJ R ≤ R := sSup_le fun _ hA => hA.1
  have hRne : R ≠ ⊥ := fun he => hne (bot_unique (d.module_le_core.trans he.le))
  intro hJ₂
  have he := source_thompson_eq_of_notFF d hnf
  have hJJ : elementaryAbelianMaxJ (twoCoreIn G₂) = elementaryAbelianMaxJ R := by
    rw [← he]
    exact elementaryAbelianMaxJ_eq_of_intermediate_finite T (twoCoreIn G₂)
      (he ▸ hJ₂) (right_core_le_sylow d)
  have hn₁ : G₁ ≤ normalizer (elementaryAbelianMaxJ R : Set G) :=
    (twoCore_normalized G₁).trans (normalizer_le_normalizer_elementaryAbelianMaxJ R)
  have hn₂ : G₂ ≤ normalizer (elementaryAbelianMaxJ R : Set G) := by
    rw [← hJJ]
    exact (twoCore_normalized G₂).trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  exact elementaryAbelianMaxJ_ne_bot_of_finite_pGroup R (isPGroup_pCoreIn 2 G₁) hRne
    (d.eq_bot_of_normalized hJR hn₁ hn₂)

theorem source_intrinsic_minimalParabolic_of_notFF
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥)
    (hnf : letI := d.module_elementary
      ¬ Representation.BinaryOffender.IsFFModule (imageRepresentation G₁ V d.module_normalized))
    (S : Sylow 2 G₂) (hS : (S : Subgroup G₂).map G₂.subtype = T) :
    ChapterB.IsMinimalParabolicOver S ⊤ := by
  apply (ChapterB.isMinimalParabolicOver_top_iff S).mpr
  refine ⟨?_, ?_⟩
  · obtain ⟨M,⟨hMc,hTM⟩,hu⟩ := d.unique_maximal
    have hSM : (S : Subgroup G₂) ≤ M := by
      intro s hs
      obtain ⟨m,hm,he⟩ := hTM (hS ▸ mem_map_of_mem G₂.subtype hs)
      exact G₂.subtype_injective he ▸ hm
    refine ⟨M,⟨hMc,hSM⟩,?_⟩
    intro N hN
    apply hu N
    refine ⟨hN.1,?_⟩
    rw [← hS]
    exact map_mono hN.2
  · intro hn
    have hSc : (S : Subgroup G₂) ≤ pCore 2 G₂ := le_sSup ⟨hn,S.isPGroup'⟩
    have hTc : T ≤ twoCoreIn G₂ := by rw [← hS]; exact map_mono hSc
    exact source_thompson_core_not_le_right_core_of_notFF d hne hnf
      ((sSup_le fun _ hA => hA.1).trans ((left_core_le_sylow d).trans hTc))
end CFSG.Quasithin.ChapterD.UniqueFactor
