module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.TorusTransfer

/-!
# The intrinsic core of the local quotient centralizer

For the literal B_C = O²(C_{BL₁}(L/O₂(L))), simultaneous normalizers
preserve B_C. If t belongs to L and normalizes BL₁, then [B_C,⟨t⟩]
lies in B_C ∩ O₂(L), a normal two-subgroup of B_C. Thus its denominator
is the intrinsic O₂(B_C), even when B_C is not contained in B or K.

The star map carries this calculation and relative normalization to H*.
Together with O³(B) ≤ B_C this proves fixation by the original marked
actor. The residual containment is still a local source obligation.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
variable {G : Type*} [Group G]

/-- The centralizing residual stays inside the literal product BL₁. -/
theorem centralizingResidual_le (B L₁ L : Subgroup G) :
    centralizingResidual B L₁ L ≤ B ⊔ L₁ :=
  (map_subtype_le _).trans (commutatorPreimage_le _ _ _)

/-- No ambient normality of L or its core is needed. -/
theorem centralizingResidual_normalized (B L₁ L A : Subgroup G)
    (hJL : B ⊔ L₁ ≤ normalizer (L : Set G))
    (hAJ : A ≤ normalizer ((B ⊔ L₁ : Subgroup G) : Set G))
    (hAL : A ≤ normalizer (L : Set G)) :
    A ≤ normalizer (centralizingResidual B L₁ L : Set G) := by
  have hcore := normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  exact (commutatorPreimage_normalized _ _ _ _ (hJL.trans hcore)
    hAJ hAL (hAL.trans hcore)).trans
      (normalizer_le_normalizer_characteristic_image
        (borelCentralizer B L₁ L) (pResidual 2 (borelCentralizer B L₁ L)))

/-- B normalizes B_C because BL₁ normalizes L. -/
theorem borel_normalizes_centralizingResidual (B L₁ L : Subgroup G)
    (hJL : B ⊔ L₁ ≤ normalizer (L : Set G)) :
    B ≤ normalizer (centralizingResidual B L₁ L : Set G) :=
  centralizingResidual_normalized B L₁ L B hJL
    (le_sup_left.trans (B ⊔ L₁).le_normalizer) (le_sup_left.trans hJL)

/-- Placement of B_C in M requires only the already established placement
of B and L₁. Its centralization of V is a separate assertion. -/
theorem centralizingResidual_le_M (B L₁ L M : Subgroup G)
    (hBM : B ≤ M) (hL₁M : L₁ ≤ M) : centralizingResidual B L₁ L ≤ M :=
  (centralizingResidual_le B L₁ L).trans (sup_le hBM hL₁M)

/-- The entire cyclic commutator, for the same t, lies in the intrinsic core.
The actor need not be an involution. -/
theorem centralizingResidual_commutator_core (B L₁ L : Subgroup G)
    (hJL : B ⊔ L₁ ≤ normalizer (L : Set G)) (t : G)
    (htL : t ∈ L) (htJ : t ∈ normalizer ((B ⊔ L₁ : Subgroup G) : Set G)) :
    ⁅centralizingResidual B L₁ L, zpowers t⁆ ≤
      (centralizingResidual B L₁ L).pCoreIn 2 := by
  let C := centralizingResidual B L₁ L
  have hJQ := hJL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have htC : zpowers t ≤ normalizer (C : Set G) :=
    centralizingResidual_normalized B L₁ L (zpowers t) hJL
      (zpowers_le.mpr htJ) ((zpowers_le.mpr htL).trans L.le_normalizer)
  have hCcore : C ≤ normalizer (L.pCoreIn 2 : Set G) :=
    (centralizingResidual_le B L₁ L).trans hJQ
  have hsmall : C ⊓ L.pCoreIn 2 ≤ C.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 L).to_le inf_le_right) inf_le_left
      ((le_inf C.le_normalizer hCcore).trans inf_normalizer_le_normalizer_inf)
  apply le_trans ?_ hsmall
  exact le_inf (le_normalizer_iff_commutator_le_left.mp htC)
    ((commutator_mono le_rfl (zpowers_le.mpr htL)).trans
      (centralizingResidual_commutator_le B L₁ L hJQ))

/-- Passing to H* preserves relative normalization. -/
theorem starImage_normalizes (H A C : Subgroup G)
    (hAC : A ≤ normalizer (C : Set G)) :
    Source.starImage H A ≤ normalizer (Source.starImage H C : Set (Source.Hstar H)) := by
  have hn : A.subgroupOf H ≤ normalizer (C.subgroupOf H : Set H) := by
    apply le_normalizer_iff.mpr
    intro a ha c hc
    exact le_normalizer_iff.mp hAC a.val ha c.val hc
  exact (map_mono hn).trans (le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))

/-- The image of an intrinsic two-core lies in the intrinsic core of its
actual star image. No equality of K* and K/O₂(K) is used. -/
theorem starImage_twoCore_le (H C : Subgroup G) (hCH : C ≤ H) :
    Source.starImage H (C.pCoreIn 2) ≤ (Source.starImage H C).pCoreIn 2 := by
  let f := starHom H C hCH
  have hn : ((pCore 2 C).map f.rangeRestrict).Normal :=
    (inferInstance : (pCore 2 C).Normal).map _ f.rangeRestrict_surjective
  have hcore : (pCore 2 C).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨hn, pCore_isPGroup.map _⟩
  have hm := map_mono (f := f.range.subtype) hcore
  rw [map_map] at hm
  change (pCore 2 C).map f ≤ f.range.pCoreIn 2 at hm
  rw [pCoreIn, starImage_map_subtype H C hCH]
  simpa only [f, range_starHom] using hm

/-- Displacement descends with the intrinsic two-core denominator. -/
theorem starImage_displacement (H C : Subgroup G) (hCH : C ≤ H) (t : H)
    (hc : ⁅C, zpowers t.val⁆ ≤ C.pCoreIn 2) :
    ∀ x ∈ Source.starImage H C,
      QuotientGroup.mk' (pCore 2 H) t * x *
        (QuotientGroup.mk' (pCore 2 H) t)⁻¹ * x⁻¹ ∈
          (Source.starImage H C).pCoreIn 2 := by
  rintro _ ⟨c, hcC, rfl⟩
  have hh : ⁅c.val, t.val⁆ ∈ C.pCoreIn 2 :=
    hc (commutator_mem_commutator hcC (mem_zpowers t.val))
  have hi : ⁅t.val, c.val⁆ ∈ C.pCoreIn 2 := by
    rw [← commutatorElement_inv]
    exact (C.pCoreIn 2).inv_mem hh
  have hm := starImage_twoCore_le H C hCH
    (show QuotientGroup.mk' (pCore 2 H) ⁅t, c⁆ ∈ Source.starImage H (C.pCoreIn 2) from
      ⟨⁅t, c⁆, hi, rfl⟩)
  simpa only [commutatorElement_def, map_mul, map_inv] using hm

variable [Finite G]
/-- Every t in T∩L gives the required torus fixation as soon as the local
residual identity supplies O³(B)≤B_C. In particular this retains the t
chosen later to invert the marked cubic quotient. -/
theorem markedActor_fixes_of_residual_containment
    (H K T L₁ L : Subgroup G) [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H) (hL₁H : L₁ ≤ H)
    (hJL : borel H K T hKH hT ⊔ L₁ ≤ normalizer (L : Set G))
    (hTJ : T ≤ normalizer ((borel H K T hKH hT ⊔ L₁ : Subgroup G) : Set G))
    (hR : residualIn 3 (borel H K T hKH hT) ≤
      centralizingResidual (borel H K T hKH hT) L₁ L)
    (t : H) (ht : t.val ∈ T) (htL : t.val ∈ L) :
    TorusModels.Assembly.FixesTorus (TorusModels.Assembly.residualAt (sourceSylow H K T hT))
      (markedActor H K T t ht) := by
  let B := borel H K T hKH hT
  let C := centralizingResidual B L₁ L
  have hBH : B ≤ H := (borel_le_component H K T hKH hT).trans hKH
  have hCH : C ≤ H := (centralizingResidual_le B L₁ L).trans (sup_le hBH hL₁H)
  apply markedActor_fixes_of_centralizer H K T hKH hT t ht (Source.starImage H C)
  · exact starImage_normalizes H B C (borel_normalizes_centralizingResidual B L₁ L hJL)
  · rw [← starImage_residualIn 3 H B hBH]
    exact map_mono (comap_mono hR)
  · exact starImage_displacement H C hCH t
      (centralizingResidual_commutator_core B L₁ L hJL t.val htL (hTJ ht))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
