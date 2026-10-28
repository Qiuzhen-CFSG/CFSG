module
public import CFSG.Quasithin.Chapter10.SourceBaumannFixedCenter
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import Theory.GroupTheory.SylowNormalizerFrattini
/-!
# Nontrivial original orbit action in the fixed-center case

Suppose H lies outside M and normalizes W, while C_H(W) lies in M.
If T∩L₀ centralized W, its containment in R=C_T(W) would put N_G(R)
in M by the common-normal bound. Since R is Sylow in C_H(W), Frattini
would force H≤N_G(R)C_H(W)≤M, a contradiction.

For the original fixed-center module W=⟨Ω₁(Z(T))^H⟩, the established
centralizer bound supplies every premise. This gives the nontrivial
T∩L₀ action used to retain transvections on W in10.2.1.
Source: Aschbacher–Smith,10.2.1,printedp.743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

theorem source_a5_orbit_intersection_not_centralizes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H W : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hHW : H ≤ normalizer (W : Set G))
    (hCH : H ⊓ centralizer (W : Set G) ≤ D.maximalLocal)
    (hHM : ¬ H ≤ D.maximalLocal) :
    ¬ (T : Subgroup G) ⊓ localOrbit T L ≤ centralizer (W : Set G) := by
  let C := H ⊓ centralizer (W : Set G)
  let R := (T : Subgroup G) ⊓ C
  have hHC : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer (hHW.trans (normalizer_le_normalizer_centralizer W))).trans
      inf_normalizer_le_normalizer_inf
  have hnormal : (C.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHC
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer (hTH.trans hHC)).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (show Chapter1.IsSylowIn 2 (T : Subgroup G) H from
      ⟨T.subtype hTH,map_subgroupOf_eq_of_le hTH⟩)
    (show C ≤ H from inf_le_left) hnormal.isSubnormal
  intro hT0
  have hT0R : (T : Subgroup G) ⊓ localOrbit T L ≤ R :=
    le_inf inf_le_left (le_inf (inf_le_left.trans hTH) hT0)
  have hNR := source_a5_normalizer_le_of_orbit_intersection_le D e hn R inf_le_left hTR hT0R
  have hF := le_normalizer_sylow_sup C H inf_le_left hHC P
  rw [hP] at hF
  exact hHM (hF.trans (sup_le hNR hCH))

theorem source_a5_fixed_center_orbit_action
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ¬ (T : Subgroup G) ⊓ localOrbit T L ≤ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H : Set G) := by
  apply source_a5_orbit_intersection_not_centralizes D e hn H _ hH.1.1.2
    (le_normalizer_conjugateSpanBy _ _)
  · exact inf_le_right.trans ((centralizer_le
      (inf_le_left.trans (le_conjugateSpanBy _ _))).trans
      (source_fixed_center_centralizer_le D hne))
  · exact hH.1.2
end CFSG.Quasithin.Chapter10
