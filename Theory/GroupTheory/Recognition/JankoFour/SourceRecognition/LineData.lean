module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.PlaneOverlaps
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.PointLine

/-!
# Compatible line data from the original three-space and point subgroup

The point subgroup has its actual Todd splitting and cubic hexad overlap.
Its elementary subgroup is the Thompson subgroup of the same common Sylow,
contains the original three-space and has its marked alternating-four image.
The original point-plane index fifteen places the line pair inside that exact
hexad. The already proved normalizer factorization, special two-core and
point-line quotient then construct every field of LineData, with the literal
ambient images of K and S retained.

The original marked Mathieu application in MathieuJ4RecognitionApplication.LocalData
constructs and aligns these inputs, including the Todd splitting; this theorem
adds no assumed LineData or incidence geometry. The earlier hypotheses here
are explicit so that the construction also applies to the native comparison.

Source: Aschbacher--Segev, The uniqueness of groups of type J4, Invent.
Math. 105 (1991), (4.4)--(4.8) and the start of section 5, pp.597--599,
DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup Stellmacher
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
open LocalGeometry LocalGeometry.LocalSubgroups
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (P : PointData z) {X : Sylow 3 (CubicLift.subgroup P.cubic)}
  (d : ThreeSpaceData z P.cubic X)
attribute [local instance] R_normal_in_S_intrinsic

/-- Construct the compatible line subgroup, preserving its original two factors. -/
theorem exists_lineData (h : IsTypeJ4 z) (U : Sylow 2 G)
    (hPM : P.M = normalizer (P.E : Set G))
    (hE : P.E = elementaryAbelianMaxJ (U : Subgroup G))
    (hR : d.R ≤ (U : Subgroup G)) (hZE : d.space ≤ P.E)
    (hES : P.E ≤ d.S) (hK : d.K ≤ P.M)
    (A : Sylow 2 (alternatingGroup (Fin 5)))
    (hA : d.symmetricImage h P.E = AlternatingSylowNormalizer.image A)
    (hi : (normalizer (d.space : Set G)).relIndex (P.M ⊓ centralizer z) = 15) :
    ∃ L : LineData z P,
      L.G₂ = normalizer (d.space : Set G) ∧
      L.K.map L.G₂.subtype = d.K ∧ L.S.map L.G₂.subtype = d.S := by
  let := P.E_elementary
  have hc : Nat.card P.E = 2048 := P.E_card
  have hKN : d.K ≤ normalizer (P.E : Set G) := hK.trans_eq hPM
  have hEc : Nat.card (P.E ⊓ d.R : Subgroup G) = 512 :=
    (d.elementary_eleven_symmetric_image h P.E hc hZE hES hKN).2.2.1
  have hAS : elementaryAbelianMaxJ (U : Subgroup G) ≤ d.S := hE ▸ hES
  have hKN' : d.K ≤ normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) := hE ▸ hKN
  have hA' : d.symmetricImage h (elementaryAbelianMaxJ (U : Subgroup G)) =
      AlternatingSylowNormalizer.image A := hE ▸ hA
  have hB : P.M ⊓ normalizer (d.space : Set G) = d.pointLineGroup (U : Subgroup G) := by
    rw [pointLineGroup, ← hE, ← hPM, inf_comm]
  obtain ⟨pair,hpair,_,hpre⟩ := d.planeLine_pair h
  have hsub : pair ⊆ P.hexad := by
    apply aut_pair_subset_hexad_of_index P.hexad_mem hpair
    have hh : ((normalizer (d.space : Set G)).subgroupOf (centralizer z)).relIndex
        (P.M.subgroupOf (centralizer z)) = 15 := by
      change ((normalizer (d.space : Set G)).comap (centralizer z).subtype).relIndex _ = _
      rw [relIndex_comap, subgroupOf_map_subtype]
      exact hi
    rw [hpre, P.overlap, relIndex_comap,
      map_comap_eq_self_of_surjective (CubicLift.projection_surjective P.cubic)] at hh
    exact hh
  obtain ⟨linear⟩ := d.normalizer_K_quotient_PSL h
  obtain ⟨pointLine⟩ := d.pointLineGroup_core_quotient h _ hR hAS hKN' A hA'
  let L : LineData z P := {
    G₂ := normalizer (d.space : Set G)
    K := d.K.subgroupOf (normalizer (d.space : Set G))
    S := d.S.subgroupOf (normalizer (d.space : Set G))
    factorization := d.normalizer_factors_product h
    intersection := d.normalizer_factors_inf h
    core_card := d.normalizer_core_card h
    core_commutator := d.normalizer_core_derived_eq_center h
    core_frattini := d.normalizer_core_frattini_eq_center h
    center_elementary := d.normalizer_core_center_elementary h
    center_card := d.normalizer_core_center_card h
    linearQuotient := linear
    symmetricQuotient := d.normalizerSQuotientEquiv h
    pair := pair
    pair_card := hpair
    pair_le_hexad := hsub
    plane_overlap := hpre
    point_line_core := by
      rw [hB, d.normalizer_twoCore h, map_subgroupOf_eq_of_le d.R_le_normalizer, hE]
      exact d.pointLineGroup_twoCore_ambient h U hR hAS hKN' (hE ▸ hc) (hE ▸ hEc) A hA'
    point_line_core_card := by
      rw [hB]
      exact d.pointLineGroup_twoCore_card h _ hR hAS hKN' A hA'
    linear_le_point_line := by
      rw [d.normalizer_K_image]
      exact le_inf hK d.K_le_normalizer
    linear_normal_point_line := by
      rw [d.normalizer_K_image, hB]
      exact d.K_normal_in_pointLineGroup _
    pointLineQuotient := (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hB)
      (pCore_map_iso 2 (MulEquiv.subgroupCongr hB))).trans pointLine }
  exact ⟨L, rfl, d.normalizer_K_image, d.normalizer_S_image⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
