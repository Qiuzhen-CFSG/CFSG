module
public import CFSG.Quasithin.Chapter10.SourceA5PointRudvalisSupplement
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.LocalA5Shape

/-!
# Excluding the Rudvalis point row from the original local hypotheses

The original full point-centralizer Sylow normalizes the actual image of L
in I/Z(I). Native max6 placement and its two-residual force this image's
two-core center to have order at most two. The original moved module gives
at least sixteen. This proves the contradiction with no independently
supplied core order or embedding.

Source: Aschbacher–Smith A.3.14(12) and 10.2.9, pp.48–49 and 750–751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L I : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- A full Sylow normalizing the literal central image excludes the Ru carrier. -/
theorem source_a5_not_rudvalis_normalized_image
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (hLI : L ≤ I)
    (eI : (I ⧸ center I) ≃* Rudvalis.Model)
    (S : Sylow 2 (I ⧸ center I))
    (hS : (S : Subgroup (I ⧸ center I)) ≤ normalizer
      ((L.subgroupOf I).map (QuotientGroup.mk' (center I)) : Set (I ⧸ center I))) :
    False := by
  let A := (L.subgroupOf I).map (QuotientGroup.mk' (center I))
  let B := A.map eI.toMonoidHom
  let P := S.mapSurjective (f := eI.toMonoidHom) eI.surjective
  have hnB : (P : Subgroup Rudvalis.Model) ≤ normalizer (B : Set Rudvalis.Model) :=
    (map_mono hS).trans (le_normalizer_map eI.toMonoidHom)
  let g : A ≃* B := A.equivMapOfInjective eI.toMonoidHom eI.injective
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr (pCore 2 A) (pCore 2 B) g (pCore_map_iso 2 g)).symm.trans
      (source_a5_containing_center_image_quotient e hLI)
  have hlow := source_a5_marked_core_center_card D e hLI g
  have hsmall := MainConverse.SporadicLocal.RuEven.normalized_a5_core_center_card_le_two
    P B hnB eB
  omega

/-- The original point-component hypotheses exclude Rudvalis without a
separate core-order or model-placement premise. -/
theorem source_a5_point_not_rudvalis_of_local
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (eI : (I ⧸ center I) ≃* Rudvalis.Model) : False := by
  obtain ⟨S,_,hnS,_⟩ :=
    source_point_containing_component_local_sylow D hn hvL hv0 hs hLI hIX hI
  let q := QuotientGroup.mk' (center I)
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  have hnorm : (Sbar : Subgroup (I ⧸ center I)) ≤
      normalizer ((L.subgroupOf I).map q : Set (I ⧸ center I)) :=
    (map_mono hnS).trans (le_normalizer_map q)
  exact source_a5_not_rudvalis_normalized_image D e hLI eI Sbar hnorm

end CFSG.Quasithin.Chapter10
