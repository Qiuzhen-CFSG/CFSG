module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.BarQuotients.NaturalCoordinates
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.PlaneGeometry

/-!
# Generation of the original module from the source flag

Images under the actual natural map retain the original subgroup V. Faithfulness
from C_V(L)=1 computes their orders and identifies every subgroup with its
coordinate preimage. Thus an order-four subgroup gives the original plane and
V₃.relIndex V=2 gives a hyperplane, with no coordinates on U_H/V₁ involved.

The image of the literal embedded residual L₂ is the residual of the actual
plane stabilizer in the permutation image. The proved fixed-point-free cubic
actor in that residual generates the natural space from any hyperplane.
Lifting its orbit through the injective natural map gives V=⟨V₃^{L₂}⟩.

Source: Aschbacher–Smith, Notation 13.2.1, the original module and flag on
printed pp.915–916, and the proof of 13.8.6(3),(4), printed p.948. The source
flag index is supplied by FourLocalFactors.source_flag_index in its application.
-/

@[expose] public section

open Subgroup
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.BarQuotients
open ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
variable {G : Type*} [Group G] [Finite G] {L T V V₁ : Subgroup G}

noncomputable def imageSylow (n : NaturalSetup L T V V₁) : Sylow 2 n.permutation.range :=
  n.sylow.mapSurjective n.permutation.rangeRestrict_surjective

theorem imageSylow_map (n : NaturalSetup L T V V₁) :
    (imageSylow n : Subgroup n.permutation.range).map n.permutation.range.subtype =
      (T.subgroupOf (L ⊔ T)).map n.permutation := by
  rw [imageSylow, Sylow.coe_mapSurjective, map_map, n.sylow_eq]
  rfl

theorem imageSylow_stable (n : NaturalSetup L T V V₁)
    (X : Subgroup G) (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hX : X = sourceLinePreimage n.naturalMap W)
    (hTX : T ≤ normalizer (X : Set G)) :
    (imageSylow n : Subgroup n.permutation.range).map n.permutation.range.subtype ≤
      subspaceStabilizer (BinaryPermutation.naturalRepresentation (Fin 6)) W := by
  rw [imageSylow_map]
  rintro _ ⟨g, hg, rfl⟩
  exact (preimage_normalizer n W g).mp (hX ▸ hTX hg)

def naturalImage (n : NaturalSetup L T V V₁) (B : Subgroup G) :
    Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)) :=
  AddSubgroup.toZModSubmodule 2 (((B.subgroupOf V).map n.naturalMap).toAddSubgroup')

omit [Finite G] in
theorem naturalImage_card (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (B : Subgroup G) (hB : B ≤ V) :
    Nat.card (naturalImage n B) = Nat.card B := by
  change Nat.card ((B.subgroupOf V).map n.naturalMap) = Nat.card B
  exact (Nat.card_congr ((B.subgroupOf V).equivMapOfInjective n.naturalMap
    (naturalMap_injective n hfixed)).symm.toEquiv).trans
      (Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv)

omit [Finite G] in
theorem naturalImage_preimage (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (B : Subgroup G) (hB : B ≤ V) :
    sourceLinePreimage n.naturalMap (naturalImage n B) = B := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨w, hw, he⟩ := hv
    have hwv : w = v := naturalMap_injective n hfixed he
    have hh : (w : G) ∈ B := hw
    rw [hwv] at hh
    exact hh
  · intro b hb
    exact ⟨⟨b, hB hb⟩, ⟨⟨b, hB hb⟩, hb, rfl⟩, rfl⟩

omit [Finite G] in
theorem naturalImage_plane (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (B : Subgroup G) (hB : B ≤ V)
    (hc : Nat.card B = 4) : Module.finrank (ZMod 2) (naturalImage n B) = 2 := by
  have hp := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := naturalImage n B)
  rw [naturalImage_card n hfixed B hB, Nat.card_zmod, hc] at hp
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hp.symm

omit [Finite G] in
theorem original_card (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) : Nat.card V = 16 := by
  rw [Nat.card_congr (Equiv.ofBijective n.naturalMap
    ⟨naturalMap_injective n hfixed, n.naturalMap_surjective⟩)]
  change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
  rfl

omit [Finite G] in
theorem naturalImage_hyperplane (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (V₃ : Subgroup G)
    (h3V : V₃ ≤ V) (hindex : V₃.relIndex V = 2) :
    Module.finrank (ZMod 2) (naturalImage n V₃) = 3 := by
  have hc := (V₃.subgroupOf V).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe h3V).toEquiv, original_card n hfixed] at hc
  change Nat.card V₃ * V₃.relIndex V = 16 at hc
  rw [hindex] at hc
  have h8 : Nat.card V₃ = 8 := by omega
  have hp := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := naturalImage n V₃)
  rw [naturalImage_card n hfixed V₃ h3V, Nat.card_zmod, h8] at hp
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hp.symm

theorem permutation_residual_image (n : NaturalSetup L T V V₁)
    (X : Subgroup G) (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hX : X = sourceLinePreimage n.naturalMap W) :
    ((sourceResidual L T X).subgroupOf (L ⊔ T)).map n.permutation =
      TransvectionParabolic.EarlierCore.residual (n.permutation.range ⊓
        subspaceStabilizer (BinaryPermutation.naturalRepresentation (Fin 6)) W) := by
  let M := (L ⊔ T) ⊓ normalizer (X : Set G)
  have hM : M ≤ L ⊔ T := inf_le_left
  have hres : (sourceResidual L T X).subgroupOf (L ⊔ T) =
      TransvectionParabolic.EarlierCore.residual (M.subgroupOf (L ⊔ T)) := by
    apply map_injective (L ⊔ T).subtype_injective
    rw [map_subgroupOf_eq_of_le (show sourceResidual L T X ≤ L ⊔ T from
      (map_subtype_le (pResidual 2 M)).trans hM)]
    change TransvectionParabolic.EarlierCore.residual M = (TransvectionParabolic.EarlierCore.residual (M.subgroupOf (L ⊔ T))).map (L ⊔ T).subtype
    unfold TransvectionParabolic.EarlierCore.residual
    rw [map_embedded_pResidual, map_subgroupOf_eq_of_le hM]
  rw [hres]
  change ((pResidual 2 (M.subgroupOf (L ⊔ T))).map
    (M.subgroupOf (L ⊔ T)).subtype).map n.permutation = _
  rw [map_embedded_pResidual]
  change TransvectionParabolic.EarlierCore.residual ((M.subgroupOf (L ⊔ T)).map n.permutation) = _
  congr 1
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, (preimage_normalizer n W g).mp (hX ▸ hg.2)⟩
  · rintro ⟨⟨g, rfl⟩, hg⟩
    exact ⟨g, ⟨g.property, hX.symm ▸ (preimage_normalizer n W g).mpr hg⟩, rfl⟩

theorem original_generation (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (V₂ V₃ L₂ : Subgroup G) (W₂ : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW₂ : Module.finrank (ZMod 2) W₂ = 2)
    (hV₂ : V₂ = sourceLinePreimage n.naturalMap W₂)
    (hT₂ : T ≤ normalizer (V₂ : Set G))
    (h3V : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hL₂ : L₂ = sourceResidual L T V₂) : V = conjugateSpanBy V₃ L₂ := by
  let B := conjugateSpanBy V₃ L₂
  have hL₂P : L₂ ≤ L ⊔ T := by
    rw [hL₂]
    exact (map_subtype_le _).trans inf_le_left
  have hBV : B ≤ V := conjugateSpanBy_le h3V (hL₂P.trans n.normalizes_V)
  have himage : (L₂.subgroupOf (L ⊔ T)).map n.permutation =
      TransvectionParabolic.EarlierCore.residual (n.permutation.range ⊓
        subspaceStabilizer (BinaryPermutation.naturalRepresentation (Fin 6)) W₂) := by
    rw [hL₂]
    exact permutation_residual_image n V₂ W₂ hV₂
  obtain ⟨_, ho⟩ := TransvectionParabolic.EarlierCore.PlaneGeometry.plane_generation n.permutation.range
    n.alternating_le_range (imageSylow n) W₂ (naturalImage n V₃) hW₂
    (naturalImage_hyperplane n hfixed V₃ h3V hindex)
    (imageSylow_stable n V₂ W₂ hV₂ hT₂)
  have hfull : naturalImage n B = ⊤ := by
    apply top_unique
    rw [← ho]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, w, hw, rfl⟩
    rw [← himage] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    obtain ⟨v, hv, he⟩ := hw
    change (n.naturalMap v).toAdd = w at he
    let v' := V.normalizerMonoidHom ⟨a.val, n.normalizes_V a.property⟩ v
    refine ⟨v', subset_closure ⟨a.val, ha, v.val, hv, rfl⟩, ?_⟩
    change (n.naturalMap (V.normalizerMonoidHom
      ⟨a.val, n.normalizes_V a.property⟩ v)).toAdd = _
    rw [n.conjugation, he]
    rfl
  apply le_antisymm ?_ hBV
  intro v hv
  have hm : (n.naturalMap ⟨v, hv⟩).toAdd ∈ naturalImage n B := by rw [hfull]; trivial
  obtain ⟨w, hw, he⟩ := hm
  have hwv : w = ⟨v, hv⟩ := naturalMap_injective n hfixed he
  have hh : (w : G) ∈ B := hw
  rw [hwv] at hh
  exact hh

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.BarQuotients

end
