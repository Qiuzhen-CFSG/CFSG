module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.LiftedTorus
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.CartanAction

/-!
# Actual conjugation on the moving binary component orbit

Index two makes every H-conjugation preserve both components or exchange
both; the specified moving element exchanges them. The marked multiplication
coordinates identify the two product axes with the actual component images
in H/O₂(H). Conjugating through these coordinates and restricting by the
surjective source map constructs the automorphism of the genuine binary
Borel. Its axis formulas are derived from the component orbit, and neither
conjugating element is assumed involutory.

Source: Aschbacher–Smith, proof of 13.8.16(1), printed p.952/PDF p.969.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions
variable {G : Type*} [Group G]

/-- Every element outside the index-two component normalizer gives the same conjugate. -/
theorem conjugate_eq_of_outside (H K : Subgroup G) (hKH : K ≤ H)
    (hi : (normalizer (K.subgroupOf H : Set H)).index = 2)
    {t s : G} (ht : t ∈ H) (hs : s ∈ H)
    (htn : t ∉ normalizer (K : Set G)) (hsn : s ∉ normalizer (K : Set G)) :
    K.conjBy s = K.conjBy t := by
  let tH : H := ⟨t, ht⟩
  let sH : H := ⟨s, hs⟩
  have htH : tH ∉ normalizer (K.subgroupOf H : Set H) := by
    rwa [← subgroupOf_normalizer_eq hKH]
  have hsH : sH ∉ normalizer (K.subgroupOf H : Set H) := by
    rwa [← subgroupOf_normalizer_eq hKH]
  have hm : tH⁻¹ * sH ∈ normalizer (K.subgroupOf H : Set H) :=
    (mul_mem_iff_of_index_two hi).mpr (by simp [htH, hsH])
  rw [← subgroupOf_normalizer_eq hKH] at hm
  have he : K.conjBy (t⁻¹ * s) = K := mem_normalizer_iff_map_conj_eq.mp hm
  have he' := congrArg (fun A : Subgroup G => A.conjBy t) he
  rwa [conjBy_mul, conjBy_inv'] at he'

/-- The genuine two-component orbit is either fixed factorwise or exchanged.
No order-two assumption is made about either element. -/
theorem component_permutation (H K : Subgroup G) (hKH : K ≤ H)
    (hi : (normalizer (K.subgroupOf H : Set H)).index = 2)
    {t s : G} (ht : t ∈ H) (hs : s ∈ H)
    (htn : t ∉ normalizer (K : Set G)) :
    (K.conjBy s = K ∧ (K.conjBy t).conjBy s = K.conjBy t) ∨
      (K.conjBy s = K.conjBy t ∧ (K.conjBy t).conjBy s = K) := by
  let tH : H := ⟨t, ht⟩
  let sH : H := ⟨s, hs⟩
  have htH : tH ∉ normalizer (K.subgroupOf H : Set H) := by
    rwa [← subgroupOf_normalizer_eq hKH]
  by_cases hsn : s ∈ normalizer (K : Set G)
  · left
    refine ⟨mem_normalizer_iff_map_conj_eq.mp hsn, ?_⟩
    rw [← conjBy_mul]
    apply conjugate_eq_of_outside H K hKH hi ht (H.mul_mem hs ht) htn
    intro hm
    have hsH : sH ∈ normalizer (K.subgroupOf H : Set H) := by
      rwa [← subgroupOf_normalizer_eq hKH]
    have hstH : sH * tH ∈ normalizer (K.subgroupOf H : Set H) := by
      rwa [← subgroupOf_normalizer_eq hKH]
    exact htH ((normalizer (K.subgroupOf H : Set H)).mul_mem_cancel_left hsH |>.mp hstH)
  · right
    refine ⟨conjugate_eq_of_outside H K hKH hi ht hs htn hsn, ?_⟩
    rw [← conjBy_mul]
    apply mem_normalizer_iff_map_conj_eq.mp
    have hsH : sH ∉ normalizer (K.subgroupOf H : Set H) := by
      rwa [← subgroupOf_normalizer_eq hKH]
    have hm : sH * tH ∈ normalizer (K.subgroupOf H : Set H) :=
      (mul_mem_iff_of_index_two hi).mpr (by simp [htH, hsH])
    rwa [← subgroupOf_normalizer_eq hKH] at hm

/-- The moving element exchanges both components, although its square need not be one. -/
theorem moving_exchanges_components (H K : Subgroup G) (hKH : K ≤ H)
    (hi : (normalizer (K.subgroupOf H : Set H)).index = 2)
    {t : G} (ht : t ∈ H) (htn : t ∉ normalizer (K : Set G)) :
    (K.conjBy t).conjBy t = K := by
  rcases component_permutation H K hKH hi ht ht htn with h | h
  · exact (htn (mem_normalizer_iff_map_conj_eq.mpr h.1)).elim
  · exact h.2

/-- The join of the two components is normalized by every element of H. -/
theorem normalizes_orbit (H K : Subgroup G) (hKH : K ≤ H)
    (hi : (normalizer (K.subgroupOf H : Set H)).index = 2)
    {t : G} (ht : t ∈ H) (htn : t ∉ normalizer (K : Set G)) :
    H ≤ normalizer ((K ⊔ K.conjBy t : Subgroup G) : Set G) := by
  intro s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_sup]
  change (K.conjBy s) ⊔ (K.conjBy t).conjBy s = _
  rcases component_permutation H K hKH hi ht hs htn with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, sup_comm]

/-- A normalizing ambient element acts on the literal star image. -/
theorem normalizes_star (H K₀ : Subgroup G) (hK : K₀ ≤ H)
    {g : G} (hgH : g ∈ H) (hgK : g ∈ normalizer (K₀ : Set G)) :
    QuotientGroup.mk' (pCore 2 H) ⟨g, hgH⟩ ∈
      normalizer (Source.starImage H K₀ : Set (Source.Hstar H)) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (Source.starImage H K₀).map
    (MulAut.conj (QuotientGroup.mk' (pCore 2 H) ⟨g, hgH⟩)).toMonoidHom = _
  rw [starImage_conjBy H K₀ hK hgH]
  exact congrArg (Source.starImage H)
    (show K₀.conjBy g = K₀ from mem_normalizer_iff_map_conj_eq.mp hgK)

variable {Q : Type*} [Group Q]
variable (H K₀ : Subgroup G) (hK : K₀ ≤ H)
  (e : Source.starImage H K₀ ≃* Q × Q)

/-- Actual ambient conjugation, transported through the specified product coordinates. -/
noncomputable def productAction {g : G} (hgH : g ∈ H)
    (hgK : g ∈ normalizer (K₀ : Set G)) : MulAut (Q × Q) :=
  e.symm.trans (((Source.starImage H K₀).normalizerMonoidHom
    ⟨QuotientGroup.mk' (pCore 2 H) ⟨g, hgH⟩, normalizes_star H K₀ hK hgH hgK⟩).trans e)

/-- Formula in the actual H/O₂(H) quotient, before restricting to the Borel. -/
theorem productAction_star {g : G} (hgH : g ∈ H)
    (hgK : g ∈ normalizer (K₀ : Set G)) (z : Q × Q) :
    (e.symm (productAction H K₀ hK e hgH hgK z) : Source.Hstar H) =
      QuotientGroup.mk' (pCore 2 H) ⟨g, hgH⟩ * (e.symm z : Source.Hstar H) *
        (QuotientGroup.mk' (pCore 2 H) ⟨g, hgH⟩)⁻¹ := by
  simp only [productAction, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

variable [Finite G] [Finite Q]
variable (S : Sylow 2 (Source.starImage H K₀))

omit [Finite Q] in
/-- The source-to-binary map agrees with the original quotient on every representative. -/
theorem toBinary_star (x : SourceTorus.chosenLift H K₀ hK S) :
    (e.symm (SourceTorus.toBinary H K₀ hK e S x : Q × Q) : Source.Hstar H) =
      QuotientGroup.mk' (pCore 2 H)
        ⟨x.val, ((borelLift_le H K₀ hK _).trans hK) x.property⟩ := by
  change (e.symm (SylowBorel.coordinates _ e S (liftToBorel H K₀ hK _ x) : Q × Q) :
    Source.Hstar H) = _
  rw [SylowBorel.coordinates_apply, MulEquiv.symm_apply_apply]
  rfl

omit [Finite Q] in
/-- The literal source quotient intertwines actual conjugation with the product action. -/
theorem productAction_toBinary {g : G} (hgH : g ∈ H)
    (hgK : g ∈ normalizer (K₀ : Set G))
    (hgB : g ∈ normalizer (SourceTorus.chosenLift H K₀ hK S : Set G))
    (x : SourceTorus.chosenLift H K₀ hK S) :
    productAction H K₀ hK e hgH hgK (SourceTorus.toBinary H K₀ hK e S x) =
      (SourceTorus.toBinary H K₀ hK e S
        ((SourceTorus.chosenLift H K₀ hK S).normalizerMonoidHom ⟨g, hgB⟩ x) : Q × Q) := by
  apply e.symm.injective
  apply Subtype.ext
  rw [productAction_star, toBinary_star, toBinary_star]
  change _ = QuotientGroup.mk' (pCore 2 H)
    ((⟨g, hgH⟩ : H) * ⟨x.val, ((borelLift_le H K₀ hK _).trans hK) x.property⟩ *
      (⟨g, hgH⟩ : H)⁻¹)
  rw [map_mul, map_mul, map_inv]

omit [Finite Q] in
/-- The product action preserves the actual binary Borel, by source surjectivity. -/
theorem productAction_borel {g : G} (hgH : g ∈ H)
    (hgK : g ∈ normalizer (K₀ : Set G))
    (hgB : g ∈ normalizer (SourceTorus.chosenLift H K₀ hK S : Set G)) :
    (BinaryBorel.borel (SourceTorus.chosenSylow H K₀ e S)).map
      (productAction H K₀ hK e hgH hgK).toMonoidHom =
        BinaryBorel.borel (SourceTorus.chosenSylow H K₀ e S) := by
  let a := (SourceTorus.chosenLift H K₀ hK S).normalizerMonoidHom ⟨g, hgB⟩
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, hx⟩ := SourceTorus.toBinary_surjective H K₀ hK e S ⟨z, hz⟩
    have hv := congrArg Subtype.val hx
    change (SourceTorus.toBinary H K₀ hK e S x : Q × Q) = z at hv
    change productAction H K₀ hK e hgH hgK z ∈ _
    rw [← hv, productAction_toBinary H K₀ hK e S hgH hgK hgB]
    exact Subtype.property _
  · intro z hz
    obtain ⟨x, hx⟩ := SourceTorus.toBinary_surjective H K₀ hK e S ⟨z, hz⟩
    refine ⟨SourceTorus.toBinary H K₀ hK e S (a.symm x), Subtype.property _, ?_⟩
    change productAction H K₀ hK e hgH hgK
      (SourceTorus.toBinary H K₀ hK e S (a.symm x) : Q × Q) = z
    rw [productAction_toBinary H K₀ hK e S hgH hgK hgB]
    change (SourceTorus.toBinary H K₀ hK e S (a (a.symm x)) : Q × Q) = z
    rw [a.apply_symm_apply]
    exact congrArg Subtype.val hx

/-- The induced automorphism of the genuine binary Borel. -/
noncomputable def binaryAction {g : G} (hgH : g ∈ H)
    (hgK : g ∈ normalizer (K₀ : Set G))
    (hgB : g ∈ normalizer (SourceTorus.chosenLift H K₀ hK S : Set G)) :
    MulAut (BinaryBorel.borel (SourceTorus.chosenSylow H K₀ e S)) :=
  BinaryBorel.restrictAut _ (productAction H K₀ hK e hgH hgK)
    (productAction_borel H K₀ hK e S hgH hgK hgB)

omit [Finite Q] in
/-- Equivariance for the existing literal toBinary map. -/
theorem binaryAction_toBinary {g : G} (hgH : g ∈ H)
    (hgK : g ∈ normalizer (K₀ : Set G))
    (hgB : g ∈ normalizer (SourceTorus.chosenLift H K₀ hK S : Set G))
    (x : SourceTorus.chosenLift H K₀ hK S) :
    binaryAction H K₀ hK e S hgH hgK hgB (SourceTorus.toBinary H K₀ hK e S x) =
      SourceTorus.toBinary H K₀ hK e S
        ((SourceTorus.chosenLift H K₀ hK S).normalizerMonoidHom ⟨g, hgB⟩ x) :=
  Subtype.ext (productAction_toBinary H K₀ hK e S hgH hgK hgB x)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions
variable {G : Type*} [Group G]
variable (H K : Subgroup G) {t : G} (ht : t ∈ H)
variable (e : Source.starImage H (K ⊔ K.conjBy t) ≃*
  Source.starImage H K × Source.starImage H K)
variable (he : ∀ a b, (e.symm (a, b) : Source.Hstar H) = (a : Source.Hstar H) *
  (QuotientGroup.mk' (pCore 2 H) ⟨t, ht⟩ * b *
    (QuotientGroup.mk' (pCore 2 H) ⟨t, ht⟩)⁻¹))

/-- The product-coordinate inclusion into the actual star quotient. -/
noncomputable def coordinateInclusion :
    Source.starImage H K × Source.starImage H K →* Source.Hstar H :=
  (Source.starImage H (K ⊔ K.conjBy t)).subtype.comp e.symm.toMonoidHom

theorem coordinateInclusion_injective : Function.Injective (coordinateInclusion H K e) :=
  Subtype.val_injective.comp e.symm.injective

include he in
/-- The first coordinate axis is precisely the original component image. -/
theorem coordinate_first_image :
    (MonoidHom.snd (Source.starImage H K) (Source.starImage H K)).ker.map
      (coordinateInclusion H K e) = Source.starImage H K := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change (e.symm z : Source.Hstar H) ∈ Source.starImage H K
    have hz' : z.2 = 1 := hz
    change (e.symm (z.1, z.2) : Source.Hstar H) ∈ _
    rw [he, hz']
    simp
  · intro hx
    refine ⟨(⟨x, hx⟩, 1), rfl, ?_⟩
    change (e.symm (⟨x, hx⟩, 1) : Source.Hstar H) = x
    simp [he]

include he in
/-- The second axis is the image of the specified conjugate, with its actual conjugation marking. -/
theorem coordinate_second_image (hKH : K ≤ H) :
    (MonoidHom.fst (Source.starImage H K) (Source.starImage H K)).ker.map
      (coordinateInclusion H K e) = Source.starImage H (K.conjBy t) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change (e.symm z : Source.Hstar H) ∈ Source.starImage H (K.conjBy t)
    have hz' : z.1 = 1 := hz
    change (e.symm (z.1, z.2) : Source.Hstar H) ∈ _
    rw [he, hz']
    rw [coe_one, one_mul]
    exact (starConjugateEquiv H K hKH ht z.2).property
  · intro hx
    obtain ⟨b, hb⟩ := (starConjugateEquiv H K hKH ht).surjective ⟨x, hx⟩
    refine ⟨(1, b), rfl, ?_⟩
    change (e.symm (1, b) : Source.Hstar H) = x
    rw [he]
    simpa only [coe_one, one_mul, starConjugateEquiv_apply] using congrArg Subtype.val hb

include he in
/-- Coordinate axis identities follow from the actual star images and conjugation. -/
theorem productAction_axes (hK : K ⊔ K.conjBy t ≤ H)
    {g : G} (hgH : g ∈ H) (hgK : g ∈ normalizer ((K ⊔ K.conjBy t : Subgroup G) : Set G)) :
    let a := productAction H (K ⊔ K.conjBy t) hK e hgH hgK
    ((K.conjBy g = K ∧ (K.conjBy t).conjBy g = K.conjBy t) →
      (MonoidHom.snd _ _).ker.map a.toMonoidHom = (MonoidHom.snd _ _).ker ∧
      (MonoidHom.fst _ _).ker.map a.toMonoidHom = (MonoidHom.fst _ _).ker) ∧
    ((K.conjBy g = K.conjBy t ∧ (K.conjBy t).conjBy g = K) →
      (MonoidHom.snd _ _).ker.map a.toMonoidHom = (MonoidHom.fst _ _).ker ∧
      (MonoidHom.fst _ _).ker.map a.toMonoidHom = (MonoidHom.snd _ _).ker) := by
  dsimp only
  let a := productAction H (K ⊔ K.conjBy t) hK e hgH hgK
  let j := coordinateInclusion H K e
  let c := (MulAut.conj (QuotientGroup.mk' (pCore 2 H) ⟨g, hgH⟩)).toMonoidHom
  have hcomm : j.comp a.toMonoidHom = c.comp j :=
    MonoidHom.ext (productAction_star H (K ⊔ K.conjBy t) hK e hgH hgK)
  have hmap (A : Subgroup (Source.starImage H K × Source.starImage H K)) :
      (A.map a.toMonoidHom).map j = (A.map j).map c := by
    rw [map_map, hcomm, ← map_map]
  have h₁ := coordinate_first_image H K ht e he
  have h₂ := coordinate_second_image H K ht e he (le_sup_left.trans hK)
  have hc₁ : (Source.starImage H K).map c = Source.starImage H (K.conjBy g) :=
    starImage_conjBy H K (le_sup_left.trans hK) hgH
  have hc₂ : (Source.starImage H (K.conjBy t)).map c =
      Source.starImage H ((K.conjBy t).conjBy g) :=
    starImage_conjBy H (K.conjBy t) (le_sup_right.trans hK) hgH
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · apply map_injective (coordinateInclusion_injective H K e)
      rw [hmap, h₁, hc₁, hl]
    · apply map_injective (coordinateInclusion_injective H K e)
      rw [hmap, h₂, hc₂, hr]
  · rintro ⟨hl, hr⟩
    constructor
    · apply map_injective (coordinateInclusion_injective H K e)
      rw [hmap, h₁, h₂, hc₁, hl]
    · apply map_injective (coordinateInclusion_injective H K e)
      rw [hmap, h₁, h₂, hc₂, hr]

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions
variable {G : Type*} [Group G] [Finite G]
variable (H K : Subgroup G) {t : G} (ht : t ∈ H)
variable (hK : K ⊔ K.conjBy t ≤ H)
variable (hi : (normalizer (K.subgroupOf H : Set H)).index = 2)
variable (htn : t ∉ normalizer (K : Set G))
variable (e : Source.starImage H (K ⊔ K.conjBy t) ≃*
  Source.starImage H K × Source.starImage H K)
variable (he : ∀ a b, (e.symm (a, b) : Source.Hstar H) = (a : Source.Hstar H) *
  (QuotientGroup.mk' (pCore 2 H) ⟨t, ht⟩ * b *
    (QuotientGroup.mk' (pCore 2 H) ⟨t, ht⟩)⁻¹))
variable (S : Sylow 2 (Source.starImage H (K ⊔ K.conjBy t)))

include hi htn he in
/-- Every ambient element of H that normalizes the source Borel either preserves
both binary axes or exchanges both. The coordinate identities are conclusions. -/
theorem binary_permutation {g : G} (hgH : g ∈ H)
    (hgK : g ∈ normalizer ((K ⊔ K.conjBy t : Subgroup G) : Set G))
    (hgB : g ∈ normalizer (SourceTorus.chosenLift H (K ⊔ K.conjBy t) hK S : Set G)) :
    let a := binaryAction H (K ⊔ K.conjBy t) hK e S hgH hgK hgB
    let P := SourceTorus.chosenSylow H (K ⊔ K.conjBy t) e S
    ((BinaryBorel.firstAxis P).map a.toMonoidHom = BinaryBorel.firstAxis P ∧
      (BinaryBorel.secondAxis P).map a.toMonoidHom = BinaryBorel.secondAxis P) ∨
    ((BinaryBorel.firstAxis P).map a.toMonoidHom = BinaryBorel.secondAxis P ∧
      (BinaryBorel.secondAxis P).map a.toMonoidHom = BinaryBorel.firstAxis P) := by
  obtain ⟨hfix, hswap⟩ := productAction_axes H K ht e he hK hgH hgK
  rcases component_permutation H K (le_sup_left.trans hK) hi ht hgH htn with h | h
  · obtain ⟨h₁, h₂⟩ := hfix h
    exact Or.inl ⟨BinaryBorel.restrictAut_map _ _ _ _ _ h₁,
      BinaryBorel.restrictAut_map _ _ _ _ _ h₂⟩
  · obtain ⟨h₁, h₂⟩ := hswap h
    exact Or.inr ⟨BinaryBorel.restrictAut_map _ _ _ _ _ h₁,
      BinaryBorel.restrictAut_map _ _ _ _ _ h₂⟩

include hi htn he in
/-- The actual moving element exchanges both binary axes. -/
theorem binary_moving_exchanges
    (htK : t ∈ normalizer ((K ⊔ K.conjBy t : Subgroup G) : Set G))
    (htB : t ∈ normalizer (SourceTorus.chosenLift H (K ⊔ K.conjBy t) hK S : Set G)) :
    let a := binaryAction H (K ⊔ K.conjBy t) hK e S ht htK htB
    let P := SourceTorus.chosenSylow H (K ⊔ K.conjBy t) e S
    (BinaryBorel.firstAxis P).map a.toMonoidHom = BinaryBorel.secondAxis P ∧
      (BinaryBorel.secondAxis P).map a.toMonoidHom = BinaryBorel.firstAxis P := by
  obtain ⟨h₁, h₂⟩ := (productAction_axes H K ht e he hK ht htK).2
    ⟨rfl, moving_exchanges_components H K (le_sup_left.trans hK) hi ht htn⟩
  exact ⟨BinaryBorel.restrictAut_map _ _ _ _ _ h₁,
    BinaryBorel.restrictAut_map _ _ _ _ _ h₂⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions


end
