module
public import CFSG.Quasithin.Chapter10.SourceParabolicAction
public import CFSG.Quasithin.Chapter3.Section02.QrcInput
public import CFSG.Quasithin.Chapter3.Section02.ReducedOrbit
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalNormalReduction
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.ActionQuotient
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.CentralizerNormalizer
/-!
# Actual numerical inputs for the original module selection

Both source module bounds use the literal centralizer quotients: the
local module under L₀T, and the full module under M. For the latter set
N=N_M(C_T(V_M)). The Frattini argument preserves the full action, the
original local centralizer equality puts L₀T in N, and O₂(N)=C_T(V_M).
Thus both modules supply genuine qrc configurations for the same H*.

The proved source numerical reduction leaves the local outside-core and
dual-FF alternatives. Normality of V_M in M removes its outside-core
alternative, leaving only dual-FF for that original full action. These
are precise remaining numerical source branches, not unconditional bounds.
The post-2.1.1 outside-maximal guard is retained explicitly.

Source: Aschbacher--Smith 3.1.6--8 and 3.2.5--6, printed pp.573--581;
these are the numerical inputs to the A5 module reselection in 10.1.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
theorem source_module_nonsolvable_uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal

theorem source_full_module_reduced :
    IsPReduced 2 (D.fullModule.subgroupOf D.maximalLocal) := D.fullModule_reduced (source_module_nonsolvable_uniqueness D)

/-- The desired local q-hat bound, as a proposition on the original quotient action. -/
@[expose] def SourceLocalModuleCubicBound : Prop :=
  let U := D.moduleSubgroup.subgroupOf (localJoin T L)
  letI := (source_parabolic_module_reduced D).normal
  letI := (source_parabolic_module_reduced D).elementary
  cubicRatio (Representation.NormalElementaryQuotient.representation U
    (QuotientGroup.mk' (centralizer (U : Set (localJoin T L))))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2

/-- The desired full q-hat bound, as a proposition on the original M quotient action. -/
@[expose] def SourceFullModuleCubicBound : Prop :=
  let U := D.fullModule.subgroupOf D.maximalLocal
  letI := (source_full_module_reduced D).normal
  letI := (source_full_module_reduced D).elementary
  cubicRatio (Representation.NormalElementaryQuotient.representation U
    (QuotientGroup.mk' (centralizer (U : Set D.maximalLocal)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2

abbrev sourceFullModuleNormalizer : Subgroup G :=
  centralizerSylowNormalizer T D.maximalLocal D.fullModule

theorem source_localJoin_le_fullModuleNormalizer :
    localJoin T L ≤ sourceFullModuleNormalizer D := by
  let J := localJoin T L
  let R := (T : Subgroup G) ⊓ centralizer (D.fullModule : Set G)
  have hJM : J ≤ D.maximalLocal := (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.1
  have hVM : D.moduleSubgroup ≤ D.fullModule := le_componentOrbit _ _
  have he : R = J.pCoreIn 2 ⊓ centralizer (D.fullModule : Set G) := by
    rw [←D.sylow_centralizer_module (source_module_nonsolvable_uniqueness D)]
    apply le_antisymm
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans (centralizer_le hVM))) inf_le_right
    · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hJcore : J ≤ normalizer (J.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 J).le_normalizer_map J.subtype
  refine le_inf hJM ?_
  change J ≤ normalizer (R : Set G)
  rw [he]
  exact (le_inf hJcore ((hJM.trans D.maximalLocal_normalizes_fullModule).trans
    (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

theorem source_fullModuleNormalizer_unique {N : Subgroup G}
    (hN : IsMaximalTwoLocal N) (hle : sourceFullModuleNormalizer D ≤ N) : N = D.maximalLocal :=
  (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.2 N hN
    ((source_localJoin_le_fullModuleNormalizer D).trans hle)

/-- The full normalizer and M induce exactly the same subgroup of Aut(V_M). -/
theorem source_fullModuleNormalizer_actionImage_eq :
    internalActionImage (sourceFullModuleNormalizer D) D.fullModule
      (inf_le_left.trans D.maximalLocal_normalizes_fullModule) =
    internalActionImage D.maximalLocal D.fullModule D.maximalLocal_normalizes_fullModule :=
  centralizerSylowNormalizer_actionImage_eq T _ _
    (le_sup_right.trans (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.1)
    D.maximalLocal_normalizes_fullModule

theorem source_fullModule_qrcHypotheses {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    Chapter3.QrcHypotheses T D.maximalLocal (sourceFullModuleNormalizer D) H D.fullModule := by
  have hTM : (T : Subgroup G) ≤ D.maximalLocal :=
    le_sup_right.trans (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.1
  have hn := D.maximalLocal_normalizes_fullModule
  have hTN := sylow_le_centralizerSylowNormalizer T D.maximalLocal D.fullModule hTM hn
  have hred : pCore 2 (internalActionImage D.maximalLocal D.fullModule hn) = ⊥ :=
    internalActionImage_core_of_reduced _ _
      (D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer) hn (source_full_module_reduced D)
  exact ⟨hTN,inf_le_left,hH,(D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)).trans hTN,
    inf_le_left.trans hn,D.fullModule_elementary (source_module_nonsolvable_uniqueness D),
    centralizerSylowNormalizer_image_reduced T _ _ hTM hn hred,
    centralizerSylowNormalizer_core T _ _ hTM hn hred,
    Or.inr (inf_le_right.trans hn)⟩

theorem source_localModule_cubic_bound_of_image
    (hq : letI := D.module_elementary
      cubicRatio (imageRepresentation (localJoin T L) D.moduleSubgroup D.join_normalizes_module) ≤ 2) :
    SourceLocalModuleCubicBound D := by
  let := D.module_elementary
  let := (source_parabolic_module_reduced D).normal
  let := (source_parabolic_module_reduced D).elementary
  exact cubicRatio_quotient_le_nat_of_image _ _
    (D.module_le_core.trans (pCoreIn_le 2 _)) D.join_normalizes_module
    _ (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) 2 hq

theorem source_fullModule_cubic_bound_of_image
    (hq : letI := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
      cubicRatio (imageRepresentation (sourceFullModuleNormalizer D) D.fullModule
        (inf_le_left.trans D.maximalLocal_normalizes_fullModule)) ≤ 2) :
    SourceFullModuleCubicBound D := by
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let N := sourceFullModuleNormalizer D
  let hn : N ≤ normalizer (D.fullModule : Set G) := inf_le_left.trans D.maximalLocal_normalizes_fullModule
  have hi : internalActionImage N D.fullModule hn ≤
      internalActionImage D.maximalLocal D.fullModule D.maximalLocal_normalizes_fullModule := by
    rintro a ⟨n,rfl⟩
    exact ⟨⟨n,n.property.1⟩,rfl⟩
  have hqM := cubicRatio_le_nat_of_equivariant
    (imageRepresentation N D.fullModule hn)
    (imageRepresentation D.maximalLocal D.fullModule D.maximalLocal_normalizes_fullModule)
    (inclusion hi) (inclusion_injective hi)
    (LinearEquiv.refl (ZMod 2) (Additive D.fullModule)) (fun _ _ => rfl) 2 hq
  exact cubicRatio_quotient_le_nat_of_image _ _
    (D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer) D.maximalLocal_normalizes_fullModule
    _ (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) 2 hqM

@[expose] def SourceLocalModuleDualFF : Prop :=
  letI := D.module_elementary
  IsFFModule (imageRepresentation (localJoin T L) D.moduleSubgroup D.join_normalizes_module).dual

@[expose] def SourceFullModuleDualFF : Prop :=
  letI := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  IsFFModule (imageRepresentation (sourceFullModuleNormalizer D) D.fullModule
    (inf_le_left.trans D.maximalLocal_normalizes_fullModule)).dual

/-- All source numerical branches except local E.2.13 and dual-FF B.5.13 are discharged. -/
theorem source_module_cubic_bounds_or_source_branches
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    ∃ H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
      (SourceLocalModuleCubicBound D ∨ ¬ D.moduleSubgroup ≤ H.pCoreIn 2 ∨
        SourceLocalModuleDualFF D) ∧
      (SourceFullModuleCubicBound D ∨ SourceFullModuleDualFF D) := by
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  refine ⟨H,hH,?_,?_⟩
  · rcases (D.qrcHypotheses (source_module_nonsolvable_uniqueness D) hH).cubicRatio_le_two_or_source_branch
      D.simpleQTKE (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1
      (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.2 D.module_ne_bot with hq | ho | hd
    · exact Or.inl (source_localModule_cubic_bound_of_image D hq)
    · exact Or.inr (Or.inl ho)
    · exact Or.inr (Or.inr hd)
  · have hne : D.fullModule ≠ ⊥ := fun he => D.module_ne_bot
      (bot_unique ((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans he.le))
    rcases (source_fullModule_qrcHypotheses D hH).cubicRatio_le_two_or_dualFF_of_intersection_normalizes
      D.simpleQTKE (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1
      (fun N hN hle => source_fullModuleNormalizer_unique D hN hle) hne
      (inf_le_right.trans D.maximalLocal_normalizes_fullModule) with hq | hd
    · exact Or.inl (source_fullModule_cubic_bound_of_image D hq)
    · exact Or.inr hd
end CFSG.Quasithin.Chapter10
