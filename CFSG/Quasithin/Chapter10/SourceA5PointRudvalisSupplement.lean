module
public import CFSG.Quasithin.Chapter10.SourceA5PointLocalEmbedding
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.LocalA5Supplement

/-!
# The actual Rudvalis supplement of the original point component

The original full point-centralizer Sylow restricts to the containing component
and normalizes L. Its literal central-quotient image and the marked image of L
therefore satisfy the native max6 supplement theorem. Nontriviality of the
image's two-core follows from the original moved module's center bound.
No order of that core is assumed. The theorem retains the exact quotient,
Sylow, ambient automorphism and normal subgroup used in the source application.

Source: Aschbacher–Smith A.3.14(12) and 10.2.9, pp.48–49 and 750–751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The original local A₅ point geometry has the actual max6 Sylow supplement
in a Rudvalis central quotient, without an independent core-order premise. -/
theorem source_a5_point_rudvalis_supplement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (eI : (I ⧸ center I) ≃* Rudvalis.Model) :
    ∃ S : Sylow 2 I,
      (S : Subgroup I).map I.subtype =
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ⊓ I ∧
      let f := eI.toMonoidHom.comp (QuotientGroup.mk' (center I))
      let B := (L.subgroupOf I).map f
      ∃ a : Rudvalis.Model ≃* Rudvalis.Model,
        (B ⊔ (S : Subgroup I).map f).map a.toMonoidHom = Rudvalis.SylowOvergroups.max6 ∧
        ((B.map a.toMonoidHom).subgroupOf Rudvalis.SylowOvergroups.max6).Normal := by
  obtain ⟨S,hSm,hSn,_⟩ :=
    source_point_containing_component_local_sylow D hn hvL hv0 hs hLI hIX hI
  refine ⟨S,hSm,?_⟩
  let q := QuotientGroup.mk' (center I)
  let f := eI.toMonoidHom.comp q
  let A := (L.subgroupOf I).map q
  let B := (L.subgroupOf I).map f
  have hf : Function.Surjective f := eI.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := S.mapSurjective hf
  have hnB : (P : Subgroup Rudvalis.Model) ≤ normalizer (B : Set Rudvalis.Model) :=
    (map_mono hSn).trans (le_normalizer_map f)
  have hB : B = A.map eI.toMonoidHom := by rw [map_map]
  let g : A ≃* B := (A.equivMapOfInjective eI.toMonoidHom eI.injective).trans
    (MulEquiv.subgroupCongr hB.symm)
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr (pCore 2 A) (pCore 2 B) g (pCore_map_iso 2 g)).symm.trans
      (source_a5_containing_center_image_quotient e hLI)
  have hlow := source_a5_marked_core_center_card D e hLI g
  have hc : pCore 2 B ≠ ⊥ := by
    intro hb
    have hle := hlow.trans (center (pCore 2 B)).card_le_card_group
    rw [hb,card_bot] at hle
    omega
  exact Rudvalis.SylowOvergroups.normalized_a5_max6_placement P B hnB hc eB

end CFSG.Quasithin.Chapter10
