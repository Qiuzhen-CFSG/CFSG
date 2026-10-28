module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.Controls
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.Geometry

/-!
# Constructing the marker from its finite-image selection

The noncentral cubic fixed space supplies Z₁. Faithful residual transport
gives every field of the original marker, including its quotient order and
relative Sylow normality. The fixed/moved decomposition supplies the central
seed bound and the orders four and sixteen. The existence of the compatible
finite-image selection remains a separate source input.

Source: Aschbacher--Smith 15.1.16(c)--18, printed pp.1092--1093.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Construct the complete marker and its planes, conditionally on the
finite-image selection. No component or odd-core premise is used. -/
theorem ImageMarking.to_marker
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hex : SourceCases.Extraspecial (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict))
    (c : ImageMarking T M V hn) :
    ∃ m : CaseIPreExclusionMarker T M V hn,
      m.Z1 = fixedSubgroup M V hn c.X ∧ m.row = .seven ∧ m.prime = 3 ∧
      Nat.card m.Z1 = 4 ∧ m.fixedPlane = m.Z1 ∧ Nat.card m.movingPlane = 16 ∧
      m.Z1 ⊔ m.movingPlane = V ∧ m.Z1 ⊓ m.movingPlane = ⊥ := by
  let ρ := imageRepresentation M V hn
  let P := pResidual 2 (internalActionImage M V hn)
  let A := c.X.map P.subtype
  let W := fixedSpace ρ A
  let B := subspaceCommutator ρ ⊤ A
  let K := subspaceKernel ρ W ⊤
  let Z := (binarySubgroup W).map V.subtype
  let C := M ⊓ centralizer (Z : Set G)
  let R := (pResidual 2 C).map C.subtype
  let V2 := ⁅V,R⁆
  obtain ⟨hW,hB,hcompl⟩ := source_image_planes T hn hex c.X c.card_X c.noncentral
  have hZV : Z ≤ V := map_subtype_le _
  have hZcard : Nat.card Z = 4 := by
    rw [show Nat.card Z = Nat.card (binarySubgroup W) from
      (Nat.card_congr ((binarySubgroup W).equivMapOfInjective V.subtype
        V.subtype_injective).toEquiv).symm,binarySubgroup_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hW]
    norm_num
  have hV2 : V2 ≤ V := (marked_residual_movement hn Z).1
  obtain ⟨hfixed,hmoved⟩ := residual_spaces M V hn W
  rw [c.residual] at hfixed hmoved
  have hfixeq : V ⊓ centralizer (R : Set G) = Z := by
    have hh := congrArg (Subgroup.map V.subtype) hfixed
    rw [map_subgroupOf_eq_of_le inf_le_left] at hh
    exact hh
  have hmoveeq : V2.subgroupOf V = binarySubgroup B := hmoved
  have hZeq : Z.subgroupOf V = binarySubgroup W :=
    comap_map_eq_self_of_injective V.subtype_injective _
  have hV2card : Nat.card V2 = 16 := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe hV2).toEquiv,hmoveeq,binarySubgroup_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hB]
    norm_num
  have hsup : Z ⊔ V2 = V := by
    apply le_antisymm (sup_le hZV hV2)
    intro w hw
    have htop : Additive.ofMul (⟨w,hw⟩ : V) ∈ W ⊔ B := by
      rw [hcompl.sup_eq_top]
      trivial
    obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp htop
    have hx' : (x.toMul : G) ∈ Z := mem_map_of_mem V.subtype hx
    have hy' : (y.toMul : G) ∈ V2 := by
      change y.toMul ∈ V2.subgroupOf V
      rw [hmoveeq]
      exact hy
    have he := congrArg (fun u : Additive V => (u.toMul : G)) hxy
    change (x.toMul : G) * y.toMul = w at he
    exact he ▸ (Z ⊔ V2).mul_mem ((show Z ≤ Z ⊔ V2 from le_sup_left) hx')
      ((show V2 ≤ Z ⊔ V2 from le_sup_right) hy')
  have hinf : Z ⊓ V2 = ⊥ := by
    apply bot_unique
    intro w hw
    let u : V := ⟨w,hZV hw.1⟩
    have hu1 : Additive.ofMul u ∈ W := by
      change u ∈ binarySubgroup W
      rw [←hZeq]
      exact hw.1
    have hu2 : Additive.ofMul u ∈ B := by
      change u ∈ binarySubgroup B
      rw [←hmoveeq]
      exact hw.2
    exact congrArg (fun u : Additive V => (u.toMul : G))
      (Submodule.disjoint_def.mp hcompl.disjoint _ hu1 hu2)
  obtain ⟨hZfixed,hgen⟩ := fixed_and_generation T hTM hn W c.fixed_thompson c.generates
  have hrescard : Nat.card (pResidual 2 K) = 3 := by
    calc
      Nat.card (pResidual 2 K) = Nat.card ((pResidual 2 K).map K.subtype) :=
        Nat.card_congr ((pResidual 2 K).equivMapOfInjective K.subtype K.subtype_injective).toEquiv
      _ = Nat.card (c.X.map P.subtype) :=
        Nat.card_congr (MulEquiv.subgroupCongr c.residual).toEquiv
      _ = Nat.card c.X :=
        (Nat.card_congr (c.X.equivMapOfInjective P.subtype P.subtype_injective).toEquiv).symm
      _ = 3 := c.card_X
  let m : CaseIPreExclusionMarker T M V hn := {
    row := .seven
    Z1 := Z
    prime := 3
    prime_prime := Nat.prime_three
    marked_fixed := hZfixed
    marked_nontrivial := by intro he; rw [he,card_bot] at hZcard; omega
    generates := hgen
    local_sylow := local_sylow T hTM hn W c.sylow
    sylow_normal := ExtraspecialMarker.sylow_normal T hTM hn W c.sylow_normal
    residual_card := (residual_card M V hn W).trans hrescard
    seed_bound := inf_le_right.trans hsup.ge }
  exact ⟨m,rfl,rfl,rfl,hZcard,hfixeq,hV2card,hsup,hinf⟩

end CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
