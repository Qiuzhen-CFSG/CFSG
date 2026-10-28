module
public import Theory.SpecificGroups.OrthogonalFourBinary.MarkedNinePlanes
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceNineComponents
/-!
# The two original planes in the Nine Case-I branch

The faithful orthogonal coordinates identify the order-three image of the
literal centralizer residual. Its fixed and moved binary planes have dimension
two and are complementary. The fixed-space and displacement transport uses the
actual conjugation map, giving order-four subgroups of the original V, trivial
intersection, join V, and containment of the prescribed marked line in the
fixed plane.

The chosen-component consumer retains exactly the same marked vector as the
component construction. It discharges the finite plane geometry without adding
any new source premise; the genuine earlier residual centralization remains
explicit with its existing source owner.

Source: Aschbacher--Smith, Notation 15.1.16(b) and the Nine-row geometry in
15.1.24(1,4) and 15.1.25, printed pp.1092, 1101--1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06 Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The actual image residual has complementary binary planes, for every
selected vector and point stabilizer of the source Nine construction. -/
theorem source_nine_image_planes
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (h9 : SourceCases.Nine (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict))
    (v : Additive V) (K : Subgroup (internalActionImage M V hn))
    (hv : v ≠ 0) (hK : ∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v)
    (hc : Nat.card K = 6) :
    let R := (pResidual 2 K).map K.subtype
    Nat.card R = 3 ∧
      Module.finrank (ZMod 2) (fixedSpace (imageRepresentation M V hn) R) = 2 ∧
      Module.finrank (ZMod 2) (subspaceCommutator (imageRepresentation M V hn) ⊤ R) = 2 ∧
      IsCompl (fixedSpace (imageRepresentation M V hn) R)
        (subspaceCommutator (imageRepresentation M V hn) ⊤ R) ∧
      v ∈ fixedSpace (imageRepresentation M V hn) R := by
  let ρ := imageRepresentation M V hn
  obtain ⟨l, _, _, _, _, _, _, x, φ, hφ, hcoord⟩ := h9
  let σ := OrthogonalFourBinary.naturalRepresentation.comp φ
  let z := x v
  have hz : z ≠ 0 := by exact fun he => hv (x.injective (he.trans (map_zero x).symm))
  have hK' : K = OrthogonalFourBinary.MarkedNine.pointStabilizer φ z := by
    ext d
    rw [hK]
    change ρ d v = v ↔ (φ d).val (x v) = x v
    rw [←hcoord d v]
    exact x.injective.eq_iff.symm
  have hcard : Nat.card (OrthogonalFourBinary.MarkedNine.pointStabilizer φ z) = 6 := hK' ▸ hc
  have hp := OrthogonalFourBinary.MarkedNine.pointStabilizer_residual_planes φ hφ z hz hcard
  rw [←hK'] at hp
  let R := (pResidual 2 K).map K.subtype
  have hcoord' : ∀ d w, x (ρ d w) = σ d (x w) := hcoord
  have hfixed : (fixedSpace ρ R).map x.toLinearMap = fixedSpace σ R := by
    simpa only [Subgroup.map_id] using
      fixedSpace_map_equivariant ρ σ (MonoidHom.id _) x hcoord' R
  have hmoved : (subspaceCommutator ρ ⊤ R).map x.toLinearMap =
      subspaceCommutator σ ⊤ R := by
    have hh := subspaceCommutator_map_embedding σ ρ (MonoidHom.id _) x.toLinearMap
      (fun d w => (hcoord' d w).symm) R ⊤
    simpa only [Subgroup.map_id,Submodule.map_top,LinearEquiv.range] using hh.symm
  refine ⟨hp.1,?_,?_,?_,?_⟩
  · have hh := x.finrank_map_eq (fixedSpace ρ R)
    rw [hfixed] at hh
    exact hh.symm.trans hp.2.1
  · have hh := x.finrank_map_eq (subspaceCommutator ρ ⊤ R)
    rw [hmoved] at hh
    exact hh.symm.trans hp.2.2.1

  · apply ((Submodule.orderIsoMapComap x).isCompl_iff).mpr
    change IsCompl ((fixedSpace ρ R).map x.toLinearMap)
      ((subspaceCommutator ρ ⊤ R).map x.toLinearMap)
    rw [hfixed,hmoved]
    exact hp.2.2.2.1
  · have hmem : x v ∈ (fixedSpace ρ R).map x.toLinearMap := by
      rw [hfixed]
      exact hp.2.2.2.2.1
    rcases hmem with ⟨w,hw,he⟩
    exact x.injective he ▸ hw

/-- The fixed plane uses the literal centralizer residual in the ambient group. -/
theorem marked_residual_fixed_image
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (v : Additive V) (K : Subgroup (internalActionImage M V hn))
    (hK : ∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v) :
    let C := M ⊓ centralizer (zpowers (v.toMul : G) : Set G)
    let R := (pResidual 2 C).map C.subtype
    (V ⊓ centralizer (R : Set G)).subgroupOf V = binarySubgroup
      (fixedSpace (imageRepresentation M V hn) ((pResidual 2 K).map K.subtype)) := by
  intro C R
  let hRM : R ≤ M := (map_subtype_le _).trans inf_le_left
  let a : R →* internalActionImage M V hn :=
    (actionHom M V hn).rangeRestrict.comp (inclusion hRM)
  have he : a.range = (pResidual 2 K).map K.subtype :=
    marked_residual_action_image M V hn v K hK
  rw [←he]
  ext w
  constructor
  · intro hw
    rintro ⟨d,⟨r,rfl⟩⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change (r : G) * (w : G) * (r : G)⁻¹ = w
    have hh : (r : G) * (w : G) = (w : G) * r := hw.2 r r.property
    rw [hh,mul_inv_cancel_right]
  · intro hw
    refine ⟨w.property,?_⟩
    intro r hr
    have hh := hw ⟨a ⟨r,hr⟩,⟨⟨r,hr⟩,rfl⟩⟩
    have hh' := congrArg (fun u : Additive V => (u.toMul : G)) hh
    change r * (w : G) * r⁻¹ = w at hh'
    exact mul_inv_eq_iff_eq_mul.mp hh'

/-- Original fixed and moved planes for any prescribed source Nine marker. -/
theorem source_nine_planes
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (h9 : SourceCases.Nine (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict))
    (v : Additive V) (K : Subgroup (internalActionImage M V hn))
    (hv : v ≠ 0) (hK : ∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v)
    (hc : Nat.card K = 6) :
    let Z1 := zpowers (v.toMul : G)
    let C := M ⊓ centralizer (Z1 : Set G)
    let R := (pResidual 2 C).map C.subtype
    let V1 := V ⊓ centralizer (R : Set G)
    let V2 := ⁅V,R⁆
    Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧
      V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧ Z1 ≤ V1 := by
  intro Z1 C R V1 V2
  let ρ := imageRepresentation M V hn
  let Rbar := (pResidual 2 K).map K.subtype
  let W1 := fixedSpace ρ Rbar
  let W2 := subspaceCommutator ρ ⊤ Rbar
  obtain ⟨hR,hW1,hW2,hcompl,hvW⟩ := source_nine_image_planes T hn h9 v K hv hK hc
  have hfixed : V1.subgroupOf V = binarySubgroup W1 :=
    marked_residual_fixed_image M V hn v K hK
  have hmoved : V2.subgroupOf V = binarySubgroup W2 :=
    marked_residual_commutator_image M V hn v K hK
  have hV1 : V1 ≤ V := inf_le_left
  have hV2 : V2 ≤ V := (marked_residual_movement hn Z1).1
  have hcard (U : Subgroup G) (hU : U ≤ V) (W : Submodule (ZMod 2) (Additive V))
      (he : U.subgroupOf V = binarySubgroup W) (hd : Module.finrank (ZMod 2) W = 2) :
      Nat.card U = 4 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hU).toEquiv,he,binarySubgroup_card,
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)),hd,Nat.card_zmod]
    norm_num
  refine ⟨hcard V1 hV1 W1 hfixed hW1,hcard V2 hV2 W2 hmoved hW2,?_,?_,?_⟩
  · apply le_antisymm (sup_le hV1 hV2)
    intro w hw
    have htop : Additive.ofMul (⟨w,hw⟩ : V) ∈ W1 ⊔ W2 := by
      rw [hcompl.sup_eq_top]
      trivial
    obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp htop
    have hx' : (x.toMul : G) ∈ V1 := by
      change x.toMul ∈ V1.subgroupOf V
      rw [hfixed]
      exact hx
    have hy' : (y.toMul : G) ∈ V2 := by
      change y.toMul ∈ V2.subgroupOf V
      rw [hmoved]
      exact hy
    have he := congrArg (fun u : Additive V => (u.toMul : G)) hxy
    change (x.toMul : G) * y.toMul = w at he
    exact he ▸ (V1 ⊔ V2).mul_mem ((show V1 ≤ V1 ⊔ V2 from le_sup_left) hx') ((show V2 ≤ V1 ⊔ V2 from le_sup_right) hy')
  · apply bot_unique
    intro w hw
    let u : V := ⟨w,hV1 hw.1⟩
    have hu1 : Additive.ofMul u ∈ W1 := by
      change u ∈ binarySubgroup W1
      rw [←hfixed]
      exact hw.1
    have hu2 : Additive.ofMul u ∈ W2 := by
      change u ∈ binarySubgroup W2
      rw [←hmoved]
      exact hw.2
    have he := Submodule.disjoint_def.mp hcompl.disjoint _ hu1 hu2
    exact congrArg (fun u : Additive V => (u.toMul : G)) he
  · apply zpowers_le.mpr
    change v.toMul ∈ V1.subgroupOf V
    rw [hfixed]
    exact hvW

/-- The source choice supplies an actual component with both original planes.
The marked subgroup and all component data refer to this same selected vector. -/
theorem PreparedChosenModule.source_caseI_nine_component_planes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      pPrimeCore 2 d.G1 = ⊥ ∧ IsQuasisimple (d.L ⧸ pCore 2 d.L) ∧
      d.L ∈ Chapter1.L G d.S ∧ Chapter1.IsSylowIn 2 d.SL d.L ∧
      let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
      let V1 := V ⊓ centralizer (R : Set G)
      let V2 := ⁅V,R⁆
      V2 ≤ V ∧ R ⊔ V2 ≤ normalizer (d.L : Set G) ∧ ⁅d.L,V2⁆ ≠ ⊥ ∧
      Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧
        V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧ d.Z1 ≤ V1 := by
  let := h.elementary
  obtain ⟨v,K,hv,hfixed,hK,hgen,hcard,hSyl,hbound⟩ :=
    chosen_nine_marked_image_with_movement T hM.1.2 h.normalized h9
  obtain ⟨d,hdZ,hdrow,hdcard,hodd,hq,hL,hSL,hV2,hn,hmove⟩ :=
    h.caseI_component_of_marked_image hG T hempty hM hmany hJ hu hne hfull h9 hres
      v K hv hfixed hK hgen hcard hSyl hbound
  refine ⟨d,hdrow,hdcard,hodd,hq,hL,hSL,hV2,?_,hmove,?_⟩
  · have he : normalizer (d.Z1 : Set G) = centralizer (d.Z1 : Set G) :=
      le_antisymm (normalizer_le_centralizer_of_card_two d.Z1 hdcard)
        (Subgroup.centralizer_le_normalizer _)
    rw [he] at hn
    exact hn
  · let P (Z : Subgroup G) : Prop :=
      let C := M ⊓ centralizer (Z : Set G)
      let R := (pResidual 2 C).map C.subtype
      let V1 := V ⊓ centralizer (R : Set G)
      let V2 := ⁅V,R⁆
      Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧
        V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧ Z ≤ V1
    have hp : P (zpowers (v.toMul : G)) :=
      source_nine_planes T h.normalized h9 v K hv hK hcard
    exact (congrArg P hdZ).mpr hp

end CFSG.Quasithin.Chapter15.Section01
