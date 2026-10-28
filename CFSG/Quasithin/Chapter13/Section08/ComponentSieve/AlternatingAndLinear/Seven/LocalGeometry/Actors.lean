module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.ConjugateObstruction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# Transport of the marked critical actors to H*

The quotient map preserves conjugation by actual elements of H. Its
restriction to each local subgroup has two-group kernel, so it carries
that subgroup's intrinsic two-core onto the intrinsic two-core of its
image. These facts transport the F.9.13 containment of a conjugated Vδ.

An involution acting as a transvection on a module containing the natural
six-dimensional core has odd permutation image. Together with the
alternating subgroup this makes the seven-point action surjective.
Thus a relative four-plus-three partition placement suffices for the
existing even-core obstruction, applied to the image of the actual actor.

These are conditional transport results, not the complete exclusion of
case (1) of 13.8.8. That exclusion must still derive the partition placement
and the compatible natural-module identification from 13.8.5.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, first paragraph of the proof, printed p.958, using F.9.13(1–2)
(combined manuscript, 1 March 2004).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Containment passes to the literal images in H/O₂(H). -/
theorem starImage_mono (H : Subgroup G) {A B : Subgroup G} (hAB : A ≤ B) :
    Source.starImage H A ≤ Source.starImage H B :=
  map_mono (comap_mono hAB)

omit [Finite G] in
/-- Conjugate by y in H before, or by its actual quotient image after, taking stars. -/
theorem starImage_conjugate (H V : Subgroup G) (hVH : V ≤ H) (y : H) :
    Source.starImage H (V.map (MulAut.conj (y : G)).toMonoidHom) =
      (Source.starImage H V).map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 H) y)).toMonoidHom := by
  let q := QuotientGroup.mk' (pCore 2 H)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨v, hv, he⟩ := hx
    have hx : x = (MulAut.conj y) ⟨v, hVH hv⟩ := Subtype.ext he.symm
    subst x
    refine ⟨q ⟨v, hVH hv⟩, ⟨⟨v, hVH hv⟩, hv, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    rfl
  · rintro _ ⟨v, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(MulAut.conj y) x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

/-- The local two-core is preserved exactly; no ambient normality is imposed. -/
theorem starImage_twoCore (H B : Subgroup G) (hBH : B ≤ H) :
    Source.starImage H (B.pCoreIn 2) = (Source.starImage H B).pCoreIn 2 := by
  have he : (B.pCoreIn 2).subgroupOf H = (B.subgroupOf H).pCoreIn 2 := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 B).trans hBH),
      map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hBH]
  change ((B.pCoreIn 2).subgroupOf H).map _ = _
  rw [he]
  exact map_pCoreIn_of_ker_isPGroup (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) (B.subgroupOf H)

/-- Transport the ambient F.9.13 placement of the marked conjugate. -/
theorem star_conjugate_le_twoCore (H B V : Subgroup G) (hBH : B ≤ H)
    (hVH : V ≤ H) (y : H)
    (hplace : V.map (MulAut.conj (y : G)).toMonoidHom ≤ B.pCoreIn 2) :
    (Source.starImage H V).map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 H) y)).toMonoidHom ≤
      (Source.starImage H B).pCoreIn 2 := by
  rw [← starImage_conjugate H V hVH y, ← starImage_twoCore H B hBH]
  exact starImage_mono H hplace

open Representation.BinaryOffender
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The alternating image and one odd image generate all seven-point permutations. -/
theorem surjective_of_alternating_and_odd {J : Type*} [Group J]
    (φ : J →* S7) (hAlt : alternatingGroup (Fin 7) ≤ φ.range)
    (a : J) (ha : (φ a).sign = -1) : Function.Surjective φ := by
  intro x
  rcases Int.units_eq_one_or x.sign with hx | hx
  · exact hAlt (Equiv.Perm.mem_alternatingGroup.mpr hx)
  · have he : x * (φ a)⁻¹ ∈ alternatingGroup (Fin 7) := by
      simp only [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hx, ha]
      norm_num
    obtain ⟨b, hb⟩ := hAlt he
    refine ⟨b * a, ?_⟩
    rw [map_mul, hb, inv_mul_cancel_right]

/-- A natural transvection supplies the odd image and forces surjectivity. -/
theorem surjective_of_natural_transvection {J : Type*} [Group J]
    (ρ : Representation (ZMod 2) J E) (φ : J →* S7)
    (hφ : Function.Injective φ) (hAlt : alternatingGroup (Fin 7) ≤ φ.range)
    (hmodel : HasNaturalSubmodule ρ φ) (a : J) (ha : a ≠ 1)
    (ha2 : a ^ 2 = 1) (ht : fixedCodim ρ (zpowers a) = 1) :
    Function.Surjective φ := by
  let : Finite J := Finite.of_injective φ hφ
  obtain ⟨j, hj, he⟩ := hmodel
  exact surjective_of_alternating_and_odd φ hAlt a
    (swap_of_involution_fixedCodim_one ρ φ hφ j hj he a ha ha2 ht).sign_eq

/-- Apply the even-core obstruction to the image of the actual ambient actor. -/
theorem no_ambient_conjugated_transvection
    (H B A V : Subgroup G) (hBH : B ≤ H) (hVH : V ≤ H) (hAV : A ≤ V)
    [IsElementaryAbelian 2 A]
    (ρ : Representation (ZMod 2) (Source.Hstar H) E)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hmodel : HasNaturalSubmodule ρ φ)
    (hB : (Source.starImage H B).map φ = fourThreeStabilizer)
    (y : H) (hplace : V.map (MulAut.conj (y : G)).toMonoidHom ≤ B.pCoreIn 2)
    (ht : ∃ a ∈ Source.starImage H A,
      a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) : False := by
  have hA : IsElementaryTwo (Source.starImage H A) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨a, ha, hn, _⟩ := ht
      intro he
      exact hn (mem_bot.mp (he ▸ ha))
    · let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf (hAV.trans hVH)
      exact IsElementaryAbelian.map _
  exact no_conjugated_transvection_in_fourThreeCore ρ φ hφ hmodel
    (Source.starImage H B) (Source.starImage H A) (Source.starImage H V)
    hB hA (starImage_mono H hAV) (QuotientGroup.mk' (pCore 2 H) y)
    (star_conjugate_le_twoCore H B V hBH hVH y hplace) ht

/-- A relative partition placement suffices: the transvection supplies surjectivity. -/
theorem no_ambient_transvection_of_relative_partition
    (H B A V : Subgroup G) (hBH : B ≤ H) (hVH : V ≤ H) (hAV : A ≤ V)
    [IsElementaryAbelian 2 A]
    (ρ : Representation (ZMod 2) (Source.Hstar H) E)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hAlt : alternatingGroup (Fin 7) ≤ φ.range)
    (hmodel : HasNaturalSubmodule ρ φ)
    (hB : Source.starImage H B = fourThreeStabilizer.comap φ)
    (y : H) (hplace : V.map (MulAut.conj (y : G)).toMonoidHom ≤ B.pCoreIn 2)
    (ht : ∃ a ∈ Source.starImage H A,
      a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) : False := by
  obtain ⟨a, ha, hn, hc⟩ := ht
  let : IsElementaryAbelian 2 (A.subgroupOf H) :=
    IsElementaryAbelian.subgroupOf (hAV.trans hVH)
  let : IsElementaryAbelian 2 (Source.starImage H A) := IsElementaryAbelian.map _
  have hs := surjective_of_natural_transvection ρ φ hφ hAlt hmodel a hn
    (elemPow_eq_one_of_isElementaryAbelian a ha) hc
  apply no_ambient_conjugated_transvection H B A V hBH hVH hAV ρ φ hφ hmodel
    _ y hplace ⟨a, ha, hn, hc⟩
  rw [hB, map_comap_eq_self_of_surjective hs]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry

end
