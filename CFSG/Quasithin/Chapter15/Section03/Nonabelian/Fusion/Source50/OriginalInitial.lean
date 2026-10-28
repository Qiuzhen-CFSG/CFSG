module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Initial
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Image
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianBranch
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion.Assembly
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.HypothesisVerification.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49.Original
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Reduction

/-!
# The original-source reductions at the involution centralizer

The original ambient hypotheses supply the literal F.9 setup at Mc=C_G(Z),
the conjugate-centralization bound and the ordinary residual kernel. A
nonabelian V-span then forces nonabelian U, after lifting Y=[Y,U] through
its own two-core and applying the source 15.3.52 transvection argument.

Source: Aschbacher–Smith, 15.3.51–52, printed pp.1145–1146.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open FusionCore.CosetSetup ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
  (hempty : MainForward.faithfulLocalComponents d.T = ∅)
  (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
  (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
  (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
  (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
include hG hempty hM hu hmany hfixed

theorem original_hypothesis : (localSetup d (centralizerH d.Z)).Hypothesis := by
  have hpartner := OriginalSource.source_partner_eq hG d hempty hM hu hmany
  have hMc : d.Mc ∈ maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) :=
    hu ▸ Set.mem_singleton _
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have hTH : (d.T : Subgroup G) ≤ centralizerH d.Z :=
    le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow d.T)
  have hout : ¬ centralizerH d.Z ≤ d.M := by
    intro he
    exact hne (hMc.1.eq_of_le hM.1.1.1 (hpartner.le.trans he))
  exact OriginalSource.source_hypothesis hG d hempty hM hu hmany hfixed
    (centralizerH d.Z) hTH hpartner.ge hout
    (fun _ => inf_le_right.trans (centralizer_le (le_conjugateSpanBy d.Z d.M)))

omit hempty hu hmany in
theorem original_conjugates_centralize :
    ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G) := by
  let := d.action.elementary
  exact (FusionCore.OriginalCoordinates.fusion_bounds d.action
    (OriginalSource.source_fusion_inputs hG d hM hfixed)).1

theorem original_residual_commutator
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z))) :
    d.Y = ⁅d.Y,closureU d.Z d.ZS⁆ := by
  have h := original_hypothesis hG d hempty hM hu hmany hfixed
  have hf := original_conjugates_centralize hG d hM hfixed
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have h7 := source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  have ho := Source49.ordinary_from_original hG d hempty hM hu hmany hfixed
  apply residual_commutator_of_image d (centralizerH d.Z) h h7.2.2.2.1.le ho.1.symm
  have him : d.action.image d.Y = pResidual 2 OrthogonalActor := by
    rw [show d.action.image d.Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)
      from h7.1,Core.twoResidualAmbient_eq_pResidual]
    exact map_pResidual 2 Subgroup.topEquiv
  rw [him]
  exact wreath_residual_commutator (d.action.sylowImage d.T d.sylow_le)
    (d.action.image (closureU d.Z d.ZS))
    (span_image_le_sylow d (centralizerH d.Z) h)
    (sylow_normalizes_span_image d (centralizerH d.Z) h)
    (span_action_ne_bot d (centralizerH d.Z) h hf hnon)

theorem original_U_nonabelian
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z))) :
    ¬ IsMulCommutative (closureU d.Z d.ZS) := by
  have h := original_hypothesis hG d hempty hM hu hmany hfixed
  have hf := original_conjugates_centralize hG d hM hfixed
  exact AbelianExclusion.U_not_commutative_of_source51 hG d hempty hM hu hmany h
    (Source49.ordinary_from_original hG d hempty hM hu hmany hfixed)
    (module_actor_image_ne_bot d (centralizerH d.Z) h hf hnon)
    (abelian_alternative d (centralizerH d.Z) h hf hnon)
    (original_residual_commutator hG d hempty hM hu hmany hfixed hnon)
    (Source49.normalizer_three_prime_from_original hG d hempty hM hu hmany hfixed)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
