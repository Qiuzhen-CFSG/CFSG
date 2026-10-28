module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.Action
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.Contracts
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.ResidualAction

/-!
# Projection and residual assembly for the normalizer escape in 14.7.70

Assume Y lies in M = N_G(L), and restrict a genuine marked M-projection
onto L/O₂(L) to the original YT. If the projected residual normalized the
point residual, normalizer lifting would make Y normalize the original L₁.
Its actual plus image would then normalize L₁⁺, contradicting the already
proved core consequences. The independent finite parabolic calculation
therefore identifies the projected Y with the displayed L₂ image and
shows that T ∩ L acts nontrivially on E. The residual action theorem gives
Y = [Y,T ∩ L] ≤ L, and the original span contradicts Z_alpha ≰ V.
The resulting escape is applied to the existing Thompson reduction.

This module gives the conditional reduction. The extension
`ProjectionEscape.Source` discharges both local premises using
`NormalizerStructure.OriginalFlag` and `ModelImage`: the projection is
constructed from the original natural-module setup, and the finite model
theorem is proved without additional inputs. Genuine earlier universal
source setup and Thompson normality retain the Chapter 1/12 and
qt-14-03-prelim owners. The larger theorem's assembly remains with
ThompsonWitness's owner.

No identification M = LT is used. The parabolic image is the residual A₄,
not the whole S₄ parabolic. All maps retain their original subgroup domains.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Lemma 14.7.70, printed p.1074 (PDF p.1091).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape
open Representation Chapter12.Section08 Stellmacher
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {d : Data T L V F W} {c : CriticalPath (L := L) F}

omit [Finite G] in
private theorem map_subgroupOf_inclusion (A H K : Subgroup G)
    (hAH : A ≤ H) (hHK : H ≤ K) :
    (A.subgroupOf H).map (inclusion hHK) = A.subgroupOf K := by
  apply map_injective K.subtype_injective
  rw [map_map, show K.subtype.comp (inclusion hHK) = H.subtype from rfl,
    map_subgroupOf_eq_of_le hAH, map_subgroupOf_eq_of_le (hAH.trans hHK)]

/-- Apply the independent model theorem to the actual YT action and to the
restriction of the actual M-projection. The residual image is exactly the
image of L₂, and T ∩ L must act nontrivially on E. -/
theorem projection_and_noncentral_action
    (p : NormalizerProjection T L V F) (model : ParabolicImageTheorem.{u})
    (h : Geometry d c) (k : CoreFacts c)
    (hYM : Y c ≤ normalizer (L : Set G)) :
    ((Y c).subgroupOf (normalizer (L : Set G))).map p.project =
      ((F.Li L 2).subgroupOf (normalizer (L : Set G))).map p.project ∧
      ¬ (T : Subgroup G) ⊓ L ≤ centralizer (E c : Set G) := by
  let M := normalizer (L : Set G)
  have hYTM : YT c ≤ M := sup_le hYM p.sylow_le
  let π := p.project.comp (inclusion hYTM)
  let := h.E_isKleinFour
  let e := IsKleinFour.autEquivPermThree (E c)
  let f := e.toMonoidHom.comp h.rightAction
  have hf : Function.Surjective f := e.surjective.comp h.rightAction_surjective
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact h.rightAction_ker_two
  have hy : (pResidual 2 (YT c)).map (YT c).subtype = Y c :=
    embedded_pResidual_join_pGroup (Y c) (T : Subgroup G)
      (isPPerfect_embedded_pResidual 2 (YE c)) T.isPGroup' h.T_normalizes_Y
  have hyr : (pResidual 2 (YT c)).map (inclusion hYTM) = (Y c).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_map, show M.subtype.comp (inclusion hYTM) = (YT c).subtype from rfl,
      hy, map_subgroupOf_eq_of_le hYM]
  have hyπ : (pResidual 2 (YT c)).map π = ((Y c).subgroupOf M).map p.project := by
    rw [← map_map, hyr]
  have hn : ¬ (pResidual 2 (YT c)).map π ≤
      normalizer (Matrix.PSL3Two.MarkedAutomorphisms.pointA : Set Matrix.PSL3Two.SL) := by
    intro hn
    rw [hyπ] at hn
    have hYN : Y c ≤ normalizer (F.Li L 1 : Set G) := by
      intro y hy
      exact p.lift_point_normalizer
        (hn (mem_map_of_mem p.project
          (show (⟨y, hYM hy⟩ : M) ∈ (Y c).subgroupOf M from hy)))
    have hrel : (Y c).subgroupOf (I c) ≤
        normalizer ((F.Li L 1).subgroupOf (I c) : Set (I c)) := by
      rw [← subgroupOf_normalizer_eq (L₁_le_I c)]
      exact subgroupOf_mono _ hYN
    apply (core_consequences d c h k).2.2
    exact (map_mono (f := plusMap c) hrel).trans (le_normalizer_map _)
  let A := ((T : Subgroup G) ⊓ L).subgroupOf (YT c)
  have hAT : (T : Subgroup G) ⊓ L ≤ YT c := inf_le_left.trans le_sup_right
  have hAπ : A.map π = Matrix.PSL3Two.borelSL := by
    rw [← map_map, map_subgroupOf_inclusion _ _ _ hAT hYTM]
    exact p.inner_sylow_image
  obtain ⟨hline, hnot⟩ := model (YT c) f hf hk π A hAπ hn
  refine ⟨hyπ.symm.trans (hline.trans p.line_image.symm), ?_⟩
  intro hc
  apply hnot
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, h.rightAction_ker]
  exact subgroupOf_mono _ hc

/-- Conditional assembly of the source normalizer escape. Both projection
construction obligations remain explicit here and must be supplied. -/
theorem normalizer_escape_of_projection
    (p : NormalizerProjection T L V F) (model : ParabolicImageTheorem.{u})
    (h : Geometry d c) (k : CoreFacts c) :
    ¬ Y c ≤ normalizer (L : Set G) := by
  intro hYM
  exact (projection_and_noncentral_action p model h k hYM).2
    (normalizer_containment_forces_central_action h hYM)

/-- The actual Thompson consumer, retaining the genuine earlier universal
setup and 14.3.9(2) inputs and the original uniqueness over LT. -/
theorem thompson_escape_of_projection
    (p : NormalizerProjection T L V F) (model : ParabolicImageTheorem.{u})
    (h : Geometry d c) (k : CoreFacts c)
    (earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (thompson : EarlierThompsonNormality.{u}) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (I c).pCoreIn 2 :=
  thompson_not_le_core_of_escape d c earlier thompson
    (normalizer_escape_of_projection p model h k)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape
