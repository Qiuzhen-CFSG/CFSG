module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.PointLine
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# The literal triple-intersection orders and indices

K lies in the point-line overlap and induces every automorphism of the
original three-space. This overlap is therefore transitive on its seven
nonidentity points. Its stabilizer of the original marker is precisely
its intersection with the original plane group C_G(z), so has index seven
and order 18874368. Counting in the full point-plane and plane-line groups
then gives the source flag indices fifteen and five. The point-plane
index 77 is coprime to the normal cubic lift, which must therefore lie
inside this overlap. Its image through the original cubic projection has
order 11520 and has the exact original overlap as its preimage. This
does not yet identify that image with a particular hexad stabilizer.

The original-input application in MathieuJ4RecognitionApplication.MarkedOverlaps
constructs the full point-plane order from its actual cocode quotient and
discharges every hypothesis below. The argument uses the original embedded
groups; no split extension or LocalData witness is assumed.

Source: Aschbacher--Segev, The uniqueness of groups of type J4, Invent.
Math. 105 (1991), the flag preceding (4.6), (4.7) and section 5,
printed pp.598--600, DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup Stellmacher
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)

/-- The point-line overlap is transitive on the seven nonidentity points of Z. -/
theorem pointLine_marker_index (h : IsTypeJ4 z) (U : Subgroup G)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G)) :
    (centralizer z).relIndex (d.pointLineGroup U) = 7 := by
  classical
  let B := d.pointLineGroup U
  let ρ := d.normalizerAction.comp (inclusion (show B ≤ normalizer (d.space : Set G) from inf_le_left))
  let : MulAction B d.space := MulAction.compHom d.space ρ
  let z₀ : d.space := ⟨z,by rw [space,d.generated]; exact subset_closure (by simp)⟩
  have hz₀ : z₀ ≠ 1 := by
    intro he
    have hz : z = 1 := congrArg Subtype.val he
    have hh := h.involution
    simp [hz] at hh
  have horbit : MulAction.orbit B z₀ = {t : d.space | t ≠ 1} := by
    ext t
    constructor
    · rintro ⟨b,hb⟩ he
      apply hz₀
      apply (ρ b).injective
      exact hb.trans (he.trans (ρ b).map_one.symm)
    · intro ht
      obtain ⟨n,hn,he⟩ := d.normalizer_transitive t.val t.property (fun he => ht (Subtype.ext he))
      obtain ⟨k,hk⟩ := d.KAction_surjective h (d.normalizerAction ⟨n,hn⟩)
      refine ⟨⟨k.val,d.K_le_pointLineGroup U hK k.property⟩,?_⟩
      change d.KAction k z₀ = t
      rw [hk]
      exact Subtype.ext he
  have hstab : MulAction.stabilizer B z₀ = (centralizer z).subgroupOf B := by
    ext b
    change ρ b z₀ = z₀ ↔ (b : G) ∈ centralizer z
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hh
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)
    · intro hh
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr hh)
  change ((centralizer z).subgroupOf B).index = 7
  rw [←hstab,MulAction.index_stabilizer,horbit,←Nat.card_coe_set_eq]
  let := Fintype.ofFinite d.space
  change Nat.card {t : d.space // t ≠ 1} = 7
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp only [Fintype.card_unique,←Nat.card_eq_fintype_card,show Nat.card d.space=8 from d.card]

/-- The actual triple intersection has order 2^21 times nine. -/
theorem pointLine_plane_card (h : IsTypeJ4 z) (U : Subgroup G)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G))
    (hc : Nat.card (d.pointLineGroup U) = 132120576) :
    Nat.card (centralizer z ⊓ d.pointLineGroup U : Subgroup G) = 18874368 := by
  have hh := ((centralizer z).subgroupOf (d.pointLineGroup U)).card_mul_index
  change Nat.card ((centralizer z).subgroupOf (d.pointLineGroup U)) *
    (centralizer z).relIndex (d.pointLineGroup U) = _ at hh
  rw [d.pointLine_marker_index h U hK,hc,←card_map_of_injective (d.pointLineGroup U).subtype_injective,
    subgroupOf_map_subtype] at hh
  omega

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData

namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)

/-- The exact index fifteen required for the point-plane flag. -/
theorem pointPlane_line_index (h : IsTypeJ4 z) (U : Subgroup G)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G))
    (hc : Nat.card (d.pointLineGroup U) = 132120576)
    (hplane : Nat.card (normalizer (elementaryAbelianMaxJ U : Set G) ⊓ centralizer z : Subgroup G) =
      283115520) :
    (normalizer (d.space : Set G)).relIndex
      (normalizer (elementaryAbelianMaxJ U : Set G) ⊓ centralizer z) = 15 := by
  let C := normalizer (elementaryAbelianMaxJ U : Set G) ⊓ centralizer z
  have hh := ((normalizer (d.space : Set G)).subgroupOf C).card_mul_index
  rw [←card_map_of_injective C.subtype_injective,subgroupOf_map_subtype] at hh
  have he : normalizer (d.space : Set G) ⊓ C = centralizer z ⊓ d.pointLineGroup U := by
    dsimp only [C,pointLineGroup]
    ac_rfl
  rw [he,d.pointLine_plane_card h U hK hc] at hh
  change 18874368 * (normalizer (d.space : Set G)).relIndex C = Nat.card C at hh
  rw [show Nat.card C = 283115520 from hplane] at hh
  change (normalizer (d.space : Set G)).relIndex C = 15
  omega

/-- The other flag index retains the whole original plane-line intersection. -/
theorem planeLine_point_index (h : IsTypeJ4 z) (U : Subgroup G)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G))
    (hc : Nat.card (d.pointLineGroup U) = 132120576) :
    (normalizer (elementaryAbelianMaxJ U : Set G)).relIndex
      (centralizer z ⊓ normalizer (d.space : Set G)) = 5 := by
  let C := centralizer z ⊓ normalizer (d.space : Set G)
  have hh := ((normalizer (elementaryAbelianMaxJ U : Set G)).subgroupOf C).card_mul_index
  rw [←card_map_of_injective C.subtype_injective,subgroupOf_map_subtype] at hh
  have he : normalizer (elementaryAbelianMaxJ U : Set G) ⊓ C = centralizer z ⊓ d.pointLineGroup U := by
    dsimp only [C,pointLineGroup]
    ac_rfl
  rw [he,d.pointLine_plane_card h U hK hc] at hh
  change 18874368 * (normalizer (elementaryAbelianMaxJ U : Set G)).relIndex C = Nat.card C at hh
  rw [show Nat.card C = 94371840 from d.point_normalizer_card h] at hh
  change (normalizer (elementaryAbelianMaxJ U : Set G)).relIndex C = 5
  omega

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData

namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The actual point-plane overlap has index 77 in the original plane group. -/
theorem marked_pointPlane_plane_index (h : IsTypeJ4 z) (M : Subgroup G)
    (hM : Nat.card (M ⊓ centralizer z : Subgroup G) = 283115520) :
    (M.subgroupOf (centralizer z)).index = 77 := by
  have hh := (M.subgroupOf (centralizer z)).card_mul_index
  rw [←card_map_of_injective (centralizer z).subtype_injective,subgroupOf_map_subtype,
    hM,ThreeSpaceData.centralizer_card h] at hh
  omega

/-- Coprimality of the source index forces the whole cubic lift into the overlap. -/
theorem marked_pointPlane_contains_cubic (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z)) (M : Subgroup G)
    (hM : Nat.card (M ⊓ centralizer z : Subgroup G) = 283115520) :
    CubicLift.subgroup e ≤ M.subgroupOf (centralizer z) := by
  let N := CubicLift.subgroup e
  let A := M.subgroupOf (centralizer z)
  have hi : A.index = 77 := marked_pointPlane_plane_index h M hM
  have hc : Nat.card N = 24576 := CubicLift.subgroup_card e h
  have hcop : Nat.Coprime (Nat.card N) A.index := by rw [hi,hc]; decide
  have hd : A.relIndex N ∣ A.index := by
    rw [←relIndex_sup_of_normalizes N A le_normalizer_of_normal]
    exact relIndex_dvd_index_of_le le_sup_right
  exact relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop (relIndex_dvd_card A N) hd)

/-- The image through the ORIGINAL full cubic projection has the hexad-stabilizer
order, and its inverse image is exactly the original overlap. Hexad recognition
is a separate assertion. -/
theorem marked_pointPlane_cubic_image (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z)) (M : Subgroup G)
    (hM : Nat.card (M ⊓ centralizer z : Subgroup G) = 283115520) :
    Nat.card ((M.subgroupOf (centralizer z)).map (CubicLift.projection e)) = 11520 ∧
      ((M.subgroupOf (centralizer z)).map (CubicLift.projection e)).comap
        (CubicLift.projection e) = M.subgroupOf (centralizer z) := by
  let A := M.subgroupOf (centralizer z)
  let N := CubicLift.subgroup e
  have hn : N ≤ A := marked_pointPlane_contains_cubic h e M hM
  have hh := (N.subgroupOf A).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hn).toEquiv,CubicLift.subgroup_card e h] at hh
  have hAc : Nat.card A = 283115520 := by
    rw [←card_map_of_injective (centralizer z).subtype_injective,subgroupOf_map_subtype]
    exact hM
  change (3 * 2^13) * N.relIndex A = Nat.card A at hh
  change (3 * 2^13) * (CubicLift.projection e).ker.relIndex A = Nat.card A at hh
  rw [relIndex_ker,hAc] at hh
  refine ⟨?_,comap_map_eq_self hn⟩
  change Nat.card (A.map (CubicLift.projection e)) = 11520
  omega

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
