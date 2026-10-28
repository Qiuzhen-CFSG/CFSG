module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Detection
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction.Preparation
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction.QuotientComponent
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction.OrdinaryLift
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction.ActionCentralizer
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# Component extraction and ordinary lifting in E.6.19

Failure of odd-core containment across A ≤ U ≤ V yields a component D of the
actual quotient C_G(A)/(O(C_G(A)) A), with both displayed full commutators.
Its canonical residual lift is an ordinary component of C_G(A), by the
source inversion and characteristic-two centralizer argument. Transporting
this lift into G preserves its quotient image and V-normalization.

The normality/orbit clause of 1.2.1(3) is retained as an explicit earlier-source
input. Its applicability is proved: the nontrivial central two-subgroup A
lies in O₂(C_G(A)), so C_G(A) belongs to the source collection H. Together
with the proved full-automizer descent, this supplies the nontrivial odd core
in the actual action centralizer. All six fields of `DetectedComponent` are
assembled below, under E.6.1 for the full known-simple catalogue.

The earlier local facts and 1.2.1(3) remain inputs for the source assembly
owner to discharge. This result ends at detection; classification of the
component and the final odd-core balance assertion belong to the parent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.19,
printed p.252 (PDF p.263), and 1.2.1(3), p.504 (PDF p.521);
Aschbacher, Finite Group Theory, second edition, 31.14(1), 31.18,
printed pp.159–161 (PDF pp.169–171).
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V A U : Subgroup G}

/-- The component detected by failure of odd-core containment in E.6.19.
`earlierOrbits` is precisely the normality/orbit consequence of 1.2.1(3),
quantified over the source collection H and its C-components. No component
or action obstruction is supplied as an input. The proof applies in
particular when A has corank two in V and [U : A] = 2; these numerical
restrictions and Hypothesis E.6.15 are not needed for detection itself. -/
theorem exists_detectedComponent
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (earlier : EarlierLocalFacts T)
    (earlierOrbits : ∀ H ∈ Chapter1.H G, ∀ J : Subgroup H, J.IsCComponent →
      J.Normal ∨ (normalizer (J : Set H)).index = 2)
    (hA : A ∈ obstructionFamily M V)
    (hAU : A ≤ U) (hUV : U ≤ V)
    (hfail : ¬ oddCentralizer U ≤ oddCentralizer A) :
    ∃ L : Subgroup G, DetectedComponent A U V L := by
  let _ := h.elementary
  obtain ⟨D, hD, hDU, hDR, hVN⟩ := exists_quotient_component h hA hAU hUV hfail
  let _ := hD.2
  let H := centralizer (A : Set G)
  let L := (componentLift A D).map H.subtype
  have hLH : L ≤ H := map_subtype_le _
  have hLsub : L.subgroupOf H = componentLift A D :=
    comap_map_eq_self_of_injective H.subtype_injective _
  have hL : CentralizerComponent A L := ⟨hLH, by
    change IsComponent H (L.subgroupOf H)
    rw [hLsub]
    exact componentLift_isComponent h earlier hA hD⟩
  have himage : quotientImage A L = D := by
    change (L.subgroupOf H).map (quotientMap A) = D
    rw [hLsub, componentLift_image]
  have hnorm : V ≤ normalizer (L : Set G) := by
    have hv := componentLift_normalized h earlier hA hD hVN
    have hVH : V ≤ H := subspace_le_centralizer hA.1 le_rfl
    have hvmap := map_mono (f := H.subtype) hv
    rw [map_subgroupOf_eq_of_le hVH] at hvmap
    exact hvmap.trans ((componentLift A D).le_normalizer_map H.subtype)
  have hLQ : IsComponent (CentralizerQuotient A) (quotientImage A L) := himage.symm ▸ hD
  have hcomm : ⁅quotientImage A L, oddCentralizer (quotientImage A U)⁆ = quotientImage A L := by
    rwa [himage]
  have hAcore : A ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 V).to_le hA.1)
    (subspace_le_centralizer hA.1 hA.1) (Subgroup.centralizer_le_normalizer _)
  have hHH : H ∈ Chapter1.H G := by
    intro he
    exact hA.2.1 (le_bot_iff.mp (he ▸ hAcore))
  have horbit := earlierOrbits H hHH _ hL.2.isCComponent
  exact ⟨L, hL, hLQ, by rwa [himage], hcomm, hnorm,
    actionCentralizer_oddCore_ne_bot h earlier hA hAU hUV hL hLQ hcomm hnorm horbit⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction
