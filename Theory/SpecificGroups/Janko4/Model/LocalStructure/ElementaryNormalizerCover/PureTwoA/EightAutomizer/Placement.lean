module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Action
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Finite
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Assembly
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.AmbientCentralizers

/-!
# Placement of the whole native eight normalizer

The finite automizer certificate exhausts the XOR actions preserving the
canonical sixteen and the two ambient involution classes. The checked native
words realize all those actions inside one conjugate F-normalizer. Their
second-class orbit spans the eight; its self-centralization then accounts for
the kernel of the normalizer action.
Source: Kleidman--Wilson (1988), Corollary 2.3.6 and the order-256 case of §2.1.
-/
set_option backward.isDefEq.respectTransparency true
public noncomputable section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Subgroup ElementaryEightGeometry ElementaryEightGeometry.Loewy
attribute [local irreducible] modelGroup matrixA matrixB

theorem color_iff_first (m : Mask) :
    orbitColor m = true ↔ IsConj Janko4.a (maskElement m) := by
  by_cases hm : m = 0
  · subst m
    rw [maskElement_zero,isConj_one_left]
    have ha : Janko4.a ≠ 1 := by
      intro h
      have ho := orderOf_a
      rw [h,orderOf_one] at ho
      contradiction
    have hc : orbitColor 0 = false := by decide +kernel
    rw [hc]
    simp [ha]
  · have hconj := word_isConj (orbitWord m) (orbitRepresentative m)
    rw [orbit_word m hm] at hconj
    by_cases hK : inK m = true
    · have hc := inK_color m hm hK
      simp only [orbitRepresentative,hK,↓reduceIte] at hconj
      exact ⟨fun _ => mask_three_first.trans hconj,fun _ => hc⟩
    · by_cases hc : orbitColor m = true
      · simp only [orbitRepresentative,hK,hc,↓reduceIte] at hconj
        exact ⟨fun _ => mask_sixtyfour_first.trans hconj,fun _ => hc⟩
      · simp only [orbitRepresentative,hK,hc] at hconj
        exact ⟨fun h => (hc h).elim,fun h => (mask_one_not_first (h.trans hconj.symm)).elim⟩

private theorem second_orbit_mem_target (m : Mask)
    (hm : m ≠ 0) (hr : orbitRepresentative m = 1) : maskElement m ∈ target := by
  have he := word_action (orbitWord m) (orbitRepresentative m)
  rw [orbit_word m hm,hr] at he
  rw [← he]
  exact target.mul_mem (target.mul_mem (word_mem_target _) mask_one_mem_target)
    (target.inv_mem (word_mem_target _))

theorem nativeEight_le_target : nativeEight 0 ≤ target := by
  rw [← nativeGenerator_closure,closure_le]
  rintro _ ⟨i,rfl⟩
  obtain ⟨ha,hb,hra,hrb,hab⟩ := second_color_spans i
  rw [← maskElement_basis,← hab,maskElement_xor]
  exact target.mul_mem (second_orbit_mem_target _ ha hra) (second_orbit_mem_target _ hb hrb)

private def normalizerAction (n : normalizer (nativeEight 0 : Set Model)) : Mask ≃ Mask :=
  (nativeParam.trans ((nativeEight 0).normalizerMonoidHom n).toEquiv).trans nativeParam.symm

private theorem normalizerAction_eval (n : normalizer (nativeEight 0 : Set Model)) (m : Mask) :
    maskElement (normalizerAction n m) = (n : Model) * maskElement m * (n : Model)⁻¹ := by
  rw [← nativeParam_coe]
  change (nativeParam (nativeParam.symm ((nativeEight 0).normalizerMonoidHom n
    (nativeParam m))) : Model) = _
  rw [nativeParam.apply_symm_apply]
  change (n : Model) * (nativeParam m : Model) * (n : Model)⁻¹ = _
  rw [nativeParam_coe]

private theorem normalizerAction_good (n : normalizer (nativeEight 0 : Set Model)) :
    Good (normalizerAction n) where
  zero := by
    apply maskElement_injective
    rw [normalizerAction_eval,maskElement_zero]
    simp
  map_xor := by
    intro x y
    apply maskElement_injective
    rw [normalizerAction_eval,maskElement_xor,maskElement_xor,
      normalizerAction_eval,normalizerAction_eval]
    group
  injective := (normalizerAction n).injective
  map_inK := by
    intro m
    apply Bool.eq_iff_iff.mpr
    rw [inK_iff_isotropic,inK_iff_isotropic,normalizerAction_eval]
    exact (nativeEight_normalizer_le_isotropic_normalizer n.property (maskElement m)).symm
  map_color := by
    intro m
    apply Bool.eq_iff_iff.mpr
    rw [color_iff_first,color_iff_first,normalizerAction_eval]
    have hc : IsConj (maskElement m) ((n : Model) * maskElement m * (n : Model)⁻¹) :=
      isConj_iff.mpr ⟨n,rfl⟩
    exact ⟨fun h => h.trans hc.symm,fun h => h.trans hc⟩

/-- The exact native row-zero whole normalizer lies in the same F conjugate
as the three certified automizer words. -/
theorem nativeEight_normalizer_le_target : normalizer (nativeEight 0 : Set Model) ≤ target := by
  intro n hn
  obtain ⟨w,hw⟩ := exhaustion_of_good (normalizerAction ⟨n,hn⟩)
    (normalizerAction_good ⟨n,hn⟩)
  have ha (m : Mask) : wordElement w * maskElement m * (wordElement w)⁻¹ =
      n * maskElement m * n⁻¹ := by
    rw [word_action,hw,normalizerAction_eval]
  have hc : (wordElement w)⁻¹ * n ∈ centralizer (nativeEight 0 : Set Model) := by
    intro x hx
    have hx' : x ∈ Set.range maskElement := by rwa [maskElement_range]
    obtain ⟨m,rfl⟩ := hx'
    have he := ha m
    have he' : ((wordElement w)⁻¹ * n) * maskElement m * ((wordElement w)⁻¹ * n)⁻¹ =
        maskElement m := by
      calc
        _ = (wordElement w)⁻¹ * (n * maskElement m * n⁻¹) * wordElement w := by group
        _ = maskElement m := by rw [← he]; group
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  rw [nativeEight_self_centralizing 0] at hc
  have ht := target.mul_mem (word_mem_target w) (nativeEight_le_target hc)
  simpa only [mul_inv_cancel_left] using ht

theorem nativeEight_one_normalizer_placement :
    normalizer (nativeEight 1 : Set Model) ≤
      (normalizer (LinearFive.F : Set Model)).map
        (MulAut.conj (nativeFusion * c)).toMonoidHom := by
  have hn := Subgroup.map_mono (f := (MulAut.conj nativeFusion).toMonoidHom)
    nativeEight_normalizer_le_target
  rw [map_equiv_normalizer_eq,nativeFusion_eight] at hn
  have ht : target.map (MulAut.conj nativeFusion).toMonoidHom =
      (normalizer (LinearFive.F : Set Model)).map
        (MulAut.conj (nativeFusion*c)).toMonoidHom := by
    rw [target,map_map]
    congr 1
    ext x
    simp [mul_assoc]
  rwa [ht] at hn

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
