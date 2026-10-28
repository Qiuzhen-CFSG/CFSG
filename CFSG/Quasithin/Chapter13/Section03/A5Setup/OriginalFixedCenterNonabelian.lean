module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterNonabelian

/-!
# The original nonabelian fixed-center Sylow quotient under 13.3.1

The positive fixed-center branch and escaping Baumann normalizer construct
an actual H-star overgroup. Its original center-orbit W is reduced, and the
image of the prescribed Sylow subgroup in H/C_H(W) is nonabelian and has
order greater than two. Thus the single S₃ row is unavailable in the source
comparison, with no supplied factors, coordinates or nonabelian-action premise.
Source: Aschbacher–Smith 10.2.1 and 13.3.2(2), printed pp.743 and 884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal original source supplies an H-star quotient with nonabelian
prescribed Sylow image. -/
theorem exists_original_fixed_center_nonabelian_sylow
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G)) :
    ∃ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (localOrbit T L : Set G)) ∧
      H ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      (let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
       W ≤ omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)) ∧
       ∃ hred : IsPReduced 2 (W.subgroupOf H),
         letI := hred.normal
         let A := ((T : Subgroup G).subgroupOf H).map
           (QuotientGroup.mk' (centralizer (W.subgroupOf H : Set H)))
         ¬ IsMulCommutative A ∧ 2 < Nat.card A) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  obtain ⟨H,hH,hHN,hWE,hred,_,_⟩ := Chapter10.source_baumann_HStar_fixed_center_setup D hne hout
  exact ⟨H,hH,hHN,hWE,hred,
    Chapter10.source_a5_fixed_center_sylow_image_nonabelian D e hn hne hout H hH hWE hred,
    Chapter10.source_a5_fixed_center_sylow_image_card_gt_two D e hn hne hout H hH hWE hred⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
