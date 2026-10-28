module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.Setup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.SylowBridge
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.LinearObstruction

/-!
# Conditional assembly of the A₆ further-enlargement argument

The nonidentity intersection A₁ = A ∩ Uᵍ follows from the corank-three bound
and E.6.17. Once the normal containing component and its actual L₄(2)/L₅(2)
action have been constructed, the two-central subspace B gives a Sylow
subgroup of that component centralized by V. This contradicts the outer
action of A, which centralizes no Sylow subgroup.

The Sylow bridge uses only the local residual statement for C_M(B). It
does not assume the printed containment for O^{2′}(C_G(B)). The three
outstanding contracts remain genuine dependencies: this conditional assembly
does not establish `SixOrbitContainment` until they have been proved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.254
(PDF p.265), the further-enlargement paragraph in E.6.23.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- The normal component's two-central witness contradicts its outer Sylow action.
No placement of the original Sylow witness in M is assumed. -/
theorem false_of_twoCentralGeometry [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hm : 2 < localM V) {U A X Y : Subgroup G} {g : G}
    (hAV : A ≤ V) (hY : NormalComponentExtension U A X g Y)
    (ha : TwoCentralGeometry V (intersection A U g) A Y) : False := by
  obtain ⟨B, h1B, hBV, hc, _, P, hPB⟩ := ha.subspace
  obtain ⟨P', hP'⟩ := exists_sylow_centralized_by_V h h1B hBV (by omega)
    hY.component.1 hY.normal P hPB
  exact ha.no_fixed_sylow P' (hP'.trans (Subgroup.centralizer_le hAV))

/-- Final orbit containment conditional on the three outstanding mathematical
constructions. E.6.13 is the exact earlier nonnormality input to E.6.17. -/
theorem sixOrbitContainment_of_enlargement_analysis [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V)
    (h13 : ∀ B ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (B : Set G))
    (hlift : FurtherLift M V) (hmodel : ModelIdentification M V)
    (haction : LinearActionAnalysis M V) : SixOrbitContainment M V := by
  intro U hU hUh L hL he A hA hAU hc X hX g hg
  by_contra hescape
  let d : EscapeConfiguration M V U A L X g :=
    ⟨hU, hUh, hL, he, hA, hAU, hc, hX, hg, hescape⟩
  have hCM : ¬ centralizer (U : Set G) ≤ M := fun hh => he (hL.1.trans hh)
  have hne := intersection_ne_bot h h15 h13 hUh hCM hc g hg
  have hm := (lemma_E_6_16_1 h h15 hUh hCM).2.1
  obtain ⟨Y, hY⟩ := hlift U A L X g d hne
  exact false_of_twoCentralGeometry h hm hA.1 hY
    (haction U A L X g d hne Y hY (hmodel U A L X g d hne Y hY))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
