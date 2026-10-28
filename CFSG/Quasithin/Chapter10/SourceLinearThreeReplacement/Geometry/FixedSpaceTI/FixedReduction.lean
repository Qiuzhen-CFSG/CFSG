module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Pair
public import CFSG.Quasithin.Chapter10.SourceBaumannFixedCenter
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.WeakClosure
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# The weak-closure contradiction for the original fixed-space branch

A nonzero fixed part of V meets Ω₁Z(T) nontrivially. Source uniqueness then
puts the centralizer of U = ⟨Ω₁Z(T)^H⟩ in M for every actual H*. The zeroth
weak closure cannot centralize U: Frattini in C_H(U), followed by weak-closure
invariance, would put H in M. The general second-module parameter argument
therefore contradicts a(H/C_H(I),I) ≤ 1 < s(G,V) on any actual
H-invariant submodule I moved by W₀.

The imported Chapter 12 weak-closure module contains the general E.3.6
argument only, with no Chapter 12 classification premises. The numerical
bounds for the actual two modules remain separate source obligations.
Source: Aschbacher--Smith 10.3.1, pp.755--756, and E.3.15--18, p.234.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem uniqueness (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The original local module in the fixed-space contradiction. -/
def omegaModule (T : Sylow 2 G) (H : Subgroup G) : Subgroup G :=
  conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H

/-- The original full-module fixed part yields a nonzero fixed Sylow-center seed. -/
theorem fixed_center_ne_bot
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥ := by
  let F := D.fullModule ⊓ centralizer (localOrbit T L : Set G)
  let := D.fullModule_elementary (uniqueness D)
  have hTF : (T : Subgroup G) ≤ normalizer (F : Set G) :=
    (le_inf ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule)
      ((le_normalizer_componentOrbit L T).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hp : IsPGroup 2 F := (IsElementaryAbelian.isPGroup 2 D.fullModule).to_le inf_le_left
  have hn := inf_centralizer_ne_bot_of_pGroups (T : Subgroup G) F T.isPGroup' hp hTF hfix
  intro he
  apply hn
  apply bot_unique
  rw [← he]
  intro x hx
  refine ⟨(mem_omegaOneCenterAmbient_iff _ _).mpr ⟨?_,?_,hx.2⟩,hx.1.2⟩
  · exact D.fullModule_le_sylow (uniqueness D) hx.1.1
  · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx.1.1

/-- The actual omega-center span is elementary, by the original qrc construction. -/
theorem omegaModule_elementary {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    IsElementaryAbelian 2 (omegaModule T H) := by
  have hr := (D.qrcHypotheses (uniqueness D) hH).sylowOmega_reduced
    (D.simpleQTKE.evenCharacteristic T)
  let : IsElementaryAbelian 2 ((omegaModule T H).subgroupOf H) := hr.elementary
  have hUH : omegaModule T H ≤ H := by
    apply conjugateSpanBy_le_self
    intro z hz
    exact hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  exact IsElementaryAbelian.of_surjective
    (subgroupOfEquivOfLe hUH).toMonoidHom (subgroupOfEquivOfLe hUH).surjective

/-- In the nonzero-fixed branch the whole ambient omega-module centralizer lies in M. -/
theorem omegaModule_centralizer_le
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (H : Subgroup G) : centralizer (omegaModule T H : Set G) ≤ D.maximalLocal :=
  (centralizer_le (inf_le_left.trans (le_conjugateSpanBy _ _))).trans
    (source_fixed_center_centralizer_le D (fixed_center_ne_bot D hfix))

/-- The original zeroth weak closure must move each actual H* omega-module.
Frattini supplies the needed factorization, without assuming that its kernel
has trivial odd part. -/
theorem weakClosure_not_centralizes_omegaModule
    (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ¬ indexedWeakClosure D.fullModule (T : Subgroup G) 0 ≤
      centralizer (omegaModule T H : Set G) := by
  intro hW
  let C := H ⊓ centralizer (omegaModule T H : Set G)
  let R := (T : Subgroup G) ⊓ C
  have hHC : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer
      ((le_normalizer_conjugateSpanBy _ _).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hn : (C.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHC
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (show Chapter1.IsSylowIn 2 (T : Subgroup G) H from
      ⟨T.subtype hH.1.1.2,map_subgroupOf_eq_of_le hH.1.1.2⟩)
    (show C ≤ H from inf_le_left) hn.isSubnormal
  have hWR : indexedWeakClosure D.fullModule (T : Subgroup G) 0 ≤ R :=
    le_inf (indexedWeakClosure_le _ _ _)
      (le_inf ((indexedWeakClosure_le _ _ _).trans hH.1.1.2) hW)
  have hNR : normalizer (R : Set G) ≤
      normalizer (indexedWeakClosure D.fullModule (T : Subgroup G) 0 : Set G) := by
    have hh := normalizer_le_weakClosure_normalizer_of_two_overgroup
      D.fullModule H (T.subtype hH.1.1.2) R 0 (T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans hH.1.1.2)
    have hmap : ((T.subtype hH.1.1.2 : Subgroup H).map H.subtype) = T :=
      map_subgroupOf_eq_of_le hH.1.1.2
    rw [hmap] at hh
    exact hh hWR
  have hw : 0 < globalW D.fullModule (T : Subgroup G) := by rw [s.weakClosure]; norm_num
  have hF := le_normalizer_sylow_sup C H inf_le_left hHC P
  rw [hP] at hF
  exact hH.1.2 (hF.trans (sup_le (hNR.trans (source_weakClosure_zero_normalizer D hw))
    (inf_le_right.trans (omegaModule_centralizer_le D hfix H))))

/-- E.3.18 can be applied to a single actual H-invariant module moved by W₀.
This is the constituent form used in the source; it does not require a bound
for the entire omega-center orbit. -/
theorem false_of_moved_parameter_bounds
    (s : SourceLinearThreeSurvivor T D)
    {H I : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    [IsElementaryAbelian 2 I] (hHI : H ≤ normalizer (I : Set G))
    (hmove : ¬ indexedWeakClosure D.fullModule (T : Subgroup G) 0 ≤
      centralizer (I : Set G))
    (ha : moduleA ((automizerRepresentation I).comp (inducedAutomizer I H).subtype) ≤ 1)
    (hs : letI : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
      1 < globalS D.fullModule) : False := by
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  apply hmove
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g,rfl,hg⟩ := (mem_gamma_zero_iff D.fullModule (T : Subgroup G) A).mp hA
  exact Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.conjugate_centralizes_of_parameter_bound
    D.fullModule I H hHI ha hs g (hg.trans hTH)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI
