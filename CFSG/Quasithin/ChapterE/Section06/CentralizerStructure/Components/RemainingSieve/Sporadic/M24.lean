module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Sporadic.CentralPlacement
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.BlockObstruction.NativeCoordinates
public import Theory.Mathieu.M24.LocalGeometry.Stabilizers
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms

/-!
# The original M₂₄ exclusion in E.6.8

Choose the actual octad and sextet stabilizers containing the prescribed
model Sylow subgroup. Every automorphism preserving that Sylow subgroup
preserves both locals. The native A₈ quotient and sextet subnormal orders
exclude all chi-zero blocks in their full component-orbit lifts. E.6.7
places both lifts in M. Since the native pair generates M₂₄ and both lifts
retain the complete two-kernel, their join is the original component L,
contradicting E.6.6(1). No involution-centralizer containment or fixed-space
identity is added to the original source assumptions.

Source: Aschbacher–Smith E.6.8, printed p.248 (PDF p.259), GLS3 Table 5.3e.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.Sporadic
open _root_.Sporadic.Mathieu _root_.Sporadic.Mathieu.M24LocalGeometry
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V U L : Subgroup G} {K : GroupClass}

theorem m24_excluded (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (e : (L ⧸ pCore 2 L) ≃* M24) : False := by
  obtain ⟨S,hS⟩ := component_sylow_intersection h hU hL
  let R := S.mapSurjective (f := modelMap e) (modelMap_surjective e)
  obtain ⟨P,Q,hP,hQ,hRP,hRQ,hPc,hQc,hgen⟩ := Stabilizers.exists_pair_over_sylow R
  have place (A : Subgroup M24) (hA : IsGeometryLocal A) (hRA : (R : Subgroup M24) ≤ A)
      (hc : centralizer (pCore 2 A : Set A) ≤ pCore 2 A) : seedLift e A ≤ M := by
    apply seedLift_le_M_of_central_coordinates h67 hU hL e
      M24InvolutionCentralizers.center_eq_bot S hS A
      (Stabilizers.automorphism_preserves_overgroup R A hRA) hc
    intro B _ hB n q hqc hqs
    exact Chapter2.ComponentRefinement.M24Exclusion.no_chiZero_of_geometry_central_coordinates
      hB A hA q hqc hqs
  have hp := place P hP hRP hPc
  have hq := place Q hQ hRQ hQc
  have he : seedLift e P ⊔ seedLift e Q = L := by
    unfold seedLift
    rw [← Subgroup.map_sup, comap_sup_eq (modelMap e) P Q (modelMap_surjective e), hgen,
      comap_top, ← MonoidHom.range_eq_map, L.range_subtype]
  exact component_not_le h earlier hU hL (he ▸ sup_le hp hq)
end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.Sporadic
