module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness.Components
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation
public import Theory.GroupTheory.ReducedNormal.Defs

/-!
# Solvable-residual centralization from the original empty faithful family

Every C-component of an actual overgroup H of the fixed Sylow subgroup
has trivial intrinsic signalizer module when L_f(G,T) is empty. The proved
A.4.8 comparison makes it centralize Ω₁(Z(O₂(H))). Genuine Theorems A and C
supply the component generation theorem, so the entire solvable residual
centralizes this omega subgroup, hence every member of R₂(H).

This proves source 14.1.3 and the centralization assertion of 14.1.6(1).
It also supplies solvability of the actual quotient H/C_H(U), without a
solvable-action certificate or a centre–Frattini equality. All universal
earlier hypotheses are the full Theorems A and C on the full known-simple
catalogue; their assembly remains with the Chapter A source owner.

Source: Aschbacher–Smith 14.1.3 and 14.1.6, printed pp.976–977, using
1.2.1(1) and A.4.8; the original setup for Theorem 15.3.1, pp.1120–1121.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
open Chapter1.Section02
open FusionCore.CosetSetup.FittingFaithfulness

universe u
variable {G : Type u} [Group G] [Finite G]
variable
  (hA : ∀ (X : Type u) [Group X] [Finite X],
    ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
  (hC : ∀ (X : Type u) [Group X] [Finite X],
    ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
  (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
  (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
include hA hC hG hempty

/-- The stronger omega-core version of 14.1.3, for the original local group. -/
theorem residual_le_centralizer_omegaCore {H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (T : Set G)) :
    solvableResidual H ≤ centralizer (omegaOneCenterAmbient (pCore 2 H) : Set H) := by
  have hc := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH)
  have hQ : pCore 2 H ≠ ⊥ := by
    intro he
    apply hH.1
    change (pCore 2 H).map H.subtype = ⊥
    rw [he, Subgroup.map_bot]
  have hgen : cComponentLayer H = solvableResidual H :=
    proposition_1_2_1_one_of_A_3_9
      (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation hA
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC hC) hX hO)
      (uniqueness_local_quotient_sqtk hG hH.1)
  rw [← hgen]
  exact sSup_le fun L hL =>
    cComponent_centralizes_omegaCore_of_intrinsicModule_eq_bot L hL
      (intrinsicModule_eq_bot_of_emptyLf T H hH.2 hQ hc hempty L hL)

/-- Source 14.1.3: the solvable residual fixes every actual reduced normal
elementary abelian subgroup. The source R₂ is not a rank-two condition. -/
theorem residual_le_centralizer_reduced {H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (T : Set G)) (U : Subgroup H)
    (hU : IsPReduced 2 U) : solvableResidual H ≤ centralizer (U : Set H) := by
  have hUomega : U ≤ omegaOneCenterAmbient (pCore 2 H) := by
    let := hU.elementary
    intro x hx
    exact (mem_omegaOneCenterAmbient_iff _ x).mpr
      ⟨hU.le_pCore hx, elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx,
        hU.le_centralizer_pCore hx⟩
  exact (residual_le_centralizer_omegaCore hA hC hG T hempty hH).trans
    (centralizer_le hUomega)

/-- The original faithful action quotient on a reduced module is solvable. -/
theorem reduced_action_isSolvable {H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (T : Set G)) (U : Subgroup H)
    (hU : IsPReduced 2 U) :
    letI := hU.normal
    Group.IsSolvable (H ⧸ centralizer (U : Set H)) := by
  let := hU.normal
  let N := centralizer (U : Set H)
  let q := QuotientGroup.mk' N
  have hres : solvableResidual (H ⧸ N) = ⊥ := by
    rw [← map_solvableResidual_eq q (QuotientGroup.mk'_surjective N)]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q, N, QuotientGroup.ker_mk'] using
      residual_le_centralizer_reduced hA hC hG T hempty hH U hU
  obtain ⟨n, hn⟩ := exists_derivedSeries_eq_solvableResidual (G := H ⧸ N)
  exact ⟨n, hn.trans hres⟩

end CFSG.Quasithin.Chapter15.Section03.InitialSource
