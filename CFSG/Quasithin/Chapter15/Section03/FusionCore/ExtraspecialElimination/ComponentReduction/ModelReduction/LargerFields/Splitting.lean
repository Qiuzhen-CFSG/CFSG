module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.ComponentSection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SpanSplitting
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.CommutatorPreimageTransport

/-!
# The B.2.14 decomposition in the larger-field branch

Work in the actual quotient H/Z, with Z normal only relative to H. The
faithful conjugation action on U/Z, where U = ⟨Z_S^H⟩ is elementary abelian,
makes the quotient two-core self-centralizing. Thus H/Z has characteristic
two. The image of the given Sylow subgroup is Sylow, and 15.3.48(2) puts the
seed image in its omega-center. The case of a trivial seed image is handled
directly; otherwise the universal splitting clause of B.2.14 applies.

After (k), H = L₀T. The identity L = [L,Y₀] and T-invariance of Y₀ make
L₀ = ⟨L^T⟩ normal relative to H. As the seed centralizes T modulo Z, the
normal-closure supplement lemma identifies the full quotient commutator
with the image of [U,L₀]. Pulling back gives exactly
U = [U,L₀] ⊔ commutatorPreimage U H Z. This is equivalent to the quotient
product identity and implies the sum of the literal component section and
the fixed space. No disjointness of these summands is asserted.

The universal B.2.14 splitting clause and the genuine earlier local inputs
remain explicit. In particular, the commutator bound used for 15.3.48(2)
is proved equivalent to its precise tilde-center statement below. The
original characteristic-two hypothesis is retained in the source adapters;
the action supplies the stronger fact needed about the quotient directly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.13–14,
printed p.78, and 15.3.48–49, printed pp.1141–1144.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.Splitting
universe u
variable {G : Type u} [Group G]

private theorem span_subgroupOf_eq_normalClosure (A H : Subgroup G) (hAH : A ≤ H) :
    (localSpan A H).subgroupOf H = normalClosure (A.subgroupOf H : Set H) := by
  let _ := localSpan_normal A H hAH
  apply le_antisymm
  · let N := normalClosure (A.subgroupOf H : Set H)
    have hle : localSpan A H ≤ N.map H.subtype := by
      apply conjugateSpanBy_le
      · intro a ha
        exact ⟨⟨a, hAH ha⟩, le_normalClosure ha, rfl⟩
      · exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le N)).mp (by
          rw [show (N.map H.subtype).subgroupOf H = N from
            comap_map_eq_self_of_injective H.subtype_injective N]
          infer_instance)
    intro x hx
    obtain ⟨y, hy, he⟩ := hle hx
    exact (Subtype.ext he : y = x) ▸ hy
  · exact normalClosure_le_normal (comap_mono (le_conjugateSpanBy A H))

variable (H Z : Subgroup G) [(Z.subgroupOf H).Normal]

/-- Image of an ambient subgroup in the literal relative quotient H/Z. -/
@[expose] def tildeImage (A : Subgroup G) : Subgroup (H ⧸ Z.subgroupOf H) :=
  (A.subgroupOf H).map (QuotientGroup.mk' (Z.subgroupOf H))

private theorem subgroupOf_sup (A B : Subgroup G) (hAH : A ≤ H) (hBH : B ≤ H) :
    (A ⊔ B).subgroupOf H = A.subgroupOf H ⊔ B.subgroupOf H := by
  apply map_injective H.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (sup_le hAH hBH),
    map_subgroupOf_eq_of_le hAH, map_subgroupOf_eq_of_le hBH]

private theorem subgroupOf_commutator (A B : Subgroup G) (hAH : A ≤ H) (hBH : B ≤ H) :
    (⁅A, B⁆).subgroupOf H = ⁅A.subgroupOf H, B.subgroupOf H⁆ := by
  apply map_injective H.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le hAH, map_subgroupOf_eq_of_le hBH,
    map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup A B).trans (sup_le hAH hBH))]

/-- Normal closure commutes with passage to the actual relative quotient. -/
theorem tildeImage_span (A : Subgroup G) (hAH : A ≤ H) :
    tildeImage H Z (localSpan A H) = normalClosure (tildeImage H Z A : Set (H ⧸ Z.subgroupOf H)) := by
  unfold tildeImage
  rw [span_subgroupOf_eq_normalClosure A H hAH, map_normalClosure _ _ (QuotientGroup.mk'_surjective _)]
  rfl

/-- The quotient image of an ambient commutator is the quotient commutator. -/
theorem tildeImage_commutator (A B : Subgroup G) (hAH : A ≤ H) (hBH : B ≤ H) :
    tildeImage H Z ⁅A, B⁆ = ⁅tildeImage H Z A, tildeImage H Z B⁆ := by
  simp only [tildeImage, subgroupOf_commutator H A B hAH hBH, map_commutator]

/-- Centralization in H/Z is exactly an ambient commutator bound by Z. -/
theorem tildeImage_centralizes_iff (A B : Subgroup G) (hAH : A ≤ H) (hBH : B ≤ H) :
    tildeImage H Z A ≤ centralizer (tildeImage H Z B : Set (H ⧸ Z.subgroupOf H)) ↔ ⁅A, B⁆ ≤ Z := by
  have hcommH : ⁅A, B⁆ ≤ H := (Subgroup.commutator_le_sup A B).trans (sup_le hAH hBH)
  rw [← commutator_eq_bot_iff_le_centralizer, ← tildeImage_commutator H Z A B hAH hBH,
    tildeImage, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  constructor
  · intro h x hx
    exact h (show (⟨x, hcommH hx⟩ : H) ∈ (⁅A, B⁆).subgroupOf H from hx)
  · exact fun h => comap_mono h

/-- The precise tilde-center assertion of 15.3.48(2), in equivalent ambient form. -/
theorem tildeImage_le_center_iff (A T : Subgroup G) (hAT : A ≤ T) (hTH : T ≤ H) :
    tildeImage H Z A ≤ (center (tildeImage H Z T)).map (tildeImage H Z T).subtype ↔
      ⁅A, T⁆ ≤ Z := by
  rw [← tildeImage_centralizes_iff H Z A T (hAT.trans hTH) hTH]
  constructor
  · intro h a ha t ht
    obtain ⟨b, hb, rfl⟩ := h ha
    exact congrArg Subtype.val (mem_center_iff.mp hb ⟨t, ht⟩)
  · intro h a ha
    refine ⟨⟨a, (map_mono (comap_mono hAT)) ha⟩, ?_, rfl⟩
    exact mem_center_iff.mpr fun t => Subtype.ext (h ha t t.property)

/-- The commutator preimage maps onto the full quotient centralizer on U. -/
theorem tildeImage_preimage (U : Subgroup G) (hUH : U ≤ H)
    (hHZ : H ≤ normalizer (Z : Set G)) :
    tildeImage H Z (commutatorPreimage U H Z) =
      tildeImage H Z U ⊓ center (H ⧸ Z.subgroupOf H) := by
  unfold tildeImage
  rw [commutatorPreimage_subgroupOf U H Z H hUH le_rfl hHZ,
    commutatorPreimage_eq_inf_comap_centralizer, subgroupOf_self,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _), coe_top, centralizer_univ]
  ext x
  constructor
  · rintro ⟨u, ⟨hu, hc⟩, rfl⟩
    exact ⟨⟨u, hu, rfl⟩, hc⟩
  · rintro ⟨⟨u, hu, rfl⟩, hc⟩
    exact ⟨u, ⟨hu, hc⟩, rfl⟩

/-- The quotient product identity is equivalent to the requested preimage identity. -/
theorem tilde_split_iff (U A : Subgroup G) (hUH : U ≤ H) (hAU : A ≤ U)
    (hZU : Z ≤ U) (hHZ : H ≤ normalizer (Z : Set G)) :
    tildeImage H Z U = tildeImage H Z A ⊔
        (tildeImage H Z U ⊓ center (H ⧸ Z.subgroupOf H)) ↔
      U = A ⊔ commutatorPreimage U H Z := by
  rw [← tildeImage_preimage H Z U hUH hHZ]
  have hs : tildeImage H Z (A ⊔ commutatorPreimage U H Z) =
      tildeImage H Z A ⊔ tildeImage H Z (commutatorPreimage U H Z) := by
    rw [tildeImage, subgroupOf_sup H A _ (hAU.trans hUH)
      ((commutatorPreimage_le U H Z).trans hUH), Subgroup.map_sup]
    rfl
  rw [← hs]
  constructor
  · intro he
    have hZC : Z ≤ commutatorPreimage U H Z := le_commutatorPreimage hZU
      (le_normalizer_iff_commutator_le_left.mp hHZ)
    have hi := map_injective_of_ker_le (QuotientGroup.mk' (Z.subgroupOf H))
      (by rw [QuotientGroup.ker_mk']; exact comap_mono hZU)
      (by rw [QuotientGroup.ker_mk']; exact comap_mono (hZC.trans le_sup_right)) he
    have hm := congrArg (Subgroup.map H.subtype) hi
    rwa [map_subgroupOf_eq_of_le hUH, map_subgroupOf_eq_of_le
      (sup_le (hAU.trans hUH) ((commutatorPreimage_le U H Z).trans hUH))] at hm
  · exact congrArg (tildeImage H Z)

/-- Faithful conjugation on the elementary section makes H/Z characteristic two. -/
theorem quotient_characteristicTwo [Finite G] (U : Subgroup G) [IsElementaryAbelian 2 U]
    (action : SectionAction H U Z) (hUH : U ≤ H) :
    Theory.GroupTheory.generalizedFitting (H ⧸ Z.subgroupOf H) = pCore 2 (H ⧸ Z.subgroupOf H) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : (U.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer action.normalizes
  let _ := IsElementaryAbelian.subgroupOf (p := 2) hUH
  let q := QuotientGroup.mk' (Z.subgroupOf H)
  have hUQ : U.subgroupOf H ≤ pCore 2 H :=
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 _⟩
  have hmapQ : (pCore 2 H).map q ≤ pCore 2 (H ⧸ Z.subgroupOf H) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _),
      pCore_isPGroup.map q⟩
  have hbarU : tildeImage H Z U ≤ pCore 2 (H ⧸ Z.subgroupOf H) :=
    (map_mono hUQ).trans hmapQ
  apply Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf H) x
  have hc : q h ∈ centralizer (tildeImage H Z U : Set (H ⧸ Z.subgroupOf H)) :=
    centralizer_le hbarU hx
  have hfaith : QuotientGroup.mk' (pCore 2 H) h = 1 := by
    apply action.faithful
    ext w
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w.toMul
    change action.representation (QuotientGroup.mk' (pCore 2 H) h)
      (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u)) = _
    rw [action.on_representatives]
    simp only [map_one]
    apply congrArg Additive.ofMul
    apply QuotientGroup.eq_iff_div_mem.mpr
    have he : q (⁅h, (⟨u, hUH u.property⟩ : H)⁆) = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (hc (q ⟨u, hUH u.property⟩) ⟨⟨u, hUH u.property⟩, u.property, rfl⟩).symm
    have hz := (QuotientGroup.eq_one_iff _).mp he
    change ((h : G) * (u : G) * (h : G)⁻¹) / (u : G) ∈ Z
    change (h : G) * (u : G) * (h : G)⁻¹ * (u : G)⁻¹ ∈ Z at hz
    simpa only [div_eq_mul_inv] using hz
  exact hmapQ (mem_map_of_mem q ((QuotientGroup.eq_one_iff _).mp hfaith))



/-- A seed not contained in the quotient kernel has nontrivial image. -/
theorem tildeImage_ne_bot (A : Subgroup G) (hAH : A ≤ H) (hAZ : ¬ A ≤ Z) :
    tildeImage H Z A ≠ ⊥ := by
  intro hb
  have h := (Subgroup.map_eq_bot_iff (A.subgroupOf H)).mp hb
  rw [QuotientGroup.ker_mk'] at h
  exact hAZ (fun a ha => h (show (⟨a, hAH ha⟩ : H) ∈ A.subgroupOf H from ha))

/-- The genuine Sylow image contains the elementary central seed from 15.3.48(2). -/
theorem seed_le_tilde_sylow_omega [Finite G]
    (ZS T U : Subgroup G) [IsElementaryAbelian 2 U]
    (hZSU : ZS ≤ U) (hZST : ZS ≤ T) (hTH : T ≤ H)
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = T)
    (h48 : ⁅ZS, T⁆ ≤ Z) :
    tildeImage H Z ZS ≤ Stellmacher.omegaOneCenterAmbient
      ((P.mapSurjective (QuotientGroup.mk'_surjective (Z.subgroupOf H)) :
        Sylow 2 (H ⧸ Z.subgroupOf H)) : Subgroup (H ⧸ Z.subgroupOf H)) := by
  let q := QuotientGroup.mk' (Z.subgroupOf H)
  have hPT : (P : Subgroup H) = T.subgroupOf H := by
    rw [← hP]
    exact (comap_map_eq_self_of_injective H.subtype_injective (P : Subgroup H)).symm
  have hc := (tildeImage_centralizes_iff H Z ZS T (hZST.trans hTH) hTH).mpr h48
  intro x hx
  obtain ⟨a, ha, rfl⟩ := hx
  apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
  rw [Sylow.coe_mapSurjective, hPT]
  refine ⟨mem_map_of_mem q (hZST ha), ?_, ?_⟩
  · rw [← map_pow]
    have ha2 : a ^ 2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : G) (hZSU ha))
    rw [ha2, map_one]
  · exact hc (mem_map_of_mem q ha)

/-- After (k), the full-group quotient commutator is the image of [U,L₀]. -/
theorem full_commutator_image_eq_component
    (ZS L Y0 T : Subgroup G)
    (hgen : H = reducedOvergroup L Y0 T)
    (hcomm : L = ⁅L, Y0⁆) (hTY : T ≤ normalizer (Y0 : Set G))
    (hYL0 : Y0 ≤ localSpan L T) (hZST : ZS ≤ T) (h48 : ⁅ZS, T⁆ ≤ Z) :
    ⁅tildeImage H Z (localSpan ZS H), (⊤ : Subgroup (H ⧸ Z.subgroupOf H))⁆ =
      tildeImage H Z ⁅localSpan ZS H, localSpan L T⁆ := by
  have hL0H : localSpan L T ≤ H := hgen ▸ le_sup_left
  have hTH : T ≤ H := hgen ▸ le_sup_right.trans le_sup_right
  have hZSH : ZS ≤ H := hZST.trans hTH
  have hUH : localSpan ZS H ≤ H := conjugateSpanBy_le_self hZSH
  have hn := componentClosure_normal_in_replacement L Y0 T
    (le_normalizer_iff_commutator_le_left.mpr hcomm.ge) hTY
  rw [← hgen] at hn
  let _ := hn
  let _ := localSpan_normal ZS H hZSH
  let q := QuotientGroup.mk' (Z.subgroupOf H)
  let _ : (tildeImage H Z (localSpan L T)).Normal :=
    Subgroup.Normal.map hn q (QuotientGroup.mk'_surjective _)
  let _ : (tildeImage H Z (localSpan ZS H)).Normal :=
    Subgroup.Normal.map (localSpan_normal ZS H hZSH) q (QuotientGroup.mk'_surjective _)
  have hHT : H = localSpan L T ⊔ T := by
    rw [hgen, reducedOvergroup, ← sup_assoc, sup_eq_left.mpr hYL0]
  have htop : tildeImage H Z (localSpan L T) ⊔ tildeImage H Z T = ⊤ := by
    rw [tildeImage, tildeImage, ← Subgroup.map_sup,
      ← subgroupOf_sup H _ _ hL0H hTH, ← hHT, subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rw [tildeImage_commutator H Z _ _ hUH hL0H]
  exact commutator_normalClosure_eq_of_normal_supplement
    (tildeImage H Z ZS) (tildeImage H Z (localSpan ZS H))
    (tildeImage H Z (localSpan L T)) (tildeImage H Z T)
    (map_mono (comap_mono (le_conjugateSpanBy ZS H)))
    (tildeImage_span H Z ZS hZSH)
    ((tildeImage_centralizes_iff H Z ZS T hZSH hTH).mpr h48) htop

omit [(Z.subgroupOf H).Normal] in
/-- Apply the universal B.2.14 clause with every quotient hypothesis verified. The trivial seed case is proved directly. -/
theorem preimage_split_of_source [Finite G]
    (hB : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (ZS L Y0 T : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (_hchar : Theory.GroupTheory.generalizedFitting H = pCore 2 H)
    (hgen : H = reducedOvergroup L Y0 T)
    (hcomm : L = ⁅L, Y0⁆) (hTY : T ≤ normalizer (Y0 : Set G))
    (hYL0 : Y0 ≤ localSpan L T) (hZST : ZS ≤ T)
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = T)
    (h48 : ⁅ZS, T⁆ ≤ Z) :
    localSpan ZS H = ⁅localSpan ZS H, localSpan L T⁆ ⊔
      commutatorPreimage (localSpan ZS H) H Z := by
  let _ : (Z.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer action.normalizes_layer
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hP ▸ map_subtype_le _
  have hZSH : ZS ≤ H := hZST.trans hTH
  have hUH : localSpan ZS H ≤ H := conjugateSpanBy_le_self hZSH
  have hL0H : localSpan L T ≤ H := hgen ▸ le_sup_left
  have hcommU : ⁅localSpan ZS H, localSpan L T⁆ ≤ localSpan ZS H :=
    le_normalizer_iff_commutator_le_left.mp (hL0H.trans action.normalizes)
  by_cases hseed : ZS ≤ Z
  · have hUZ : localSpan ZS H ≤ Z :=
      conjugateSpanBy_le hseed action.normalizes_layer
    apply le_antisymm
    · exact (le_commutatorPreimage le_rfl
        ((commutator_mono hUZ le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp action.normalizes_layer))).trans
        le_sup_right
    · exact sup_le hcommU (commutatorPreimage_le _ _ _)
  let Pbar := P.mapSurjective (QuotientGroup.mk'_surjective (Z.subgroupOf H))
  have hb := hB (H ⧸ Z.subgroupOf H)
    (quotient_characteristicTwo H Z (localSpan ZS H) action hUH) Pbar
    (tildeImage H Z ZS) (tildeImage_ne_bot H Z ZS hZSH hseed)
    (seed_le_tilde_sylow_omega H Z ZS T (localSpan ZS H)
      (le_conjugateSpanBy ZS H) hZST hTH P hP h48)
  change normalClosure (tildeImage H Z ZS : Set (H ⧸ Z.subgroupOf H)) = _ at hb
  rw [← tildeImage_span H Z ZS hZSH,
    full_commutator_image_eq_component H Z ZS L Y0 T hgen hcomm hTY hYL0 hZST h48] at hb
  exact (tilde_split_iff H Z (localSpan ZS H) ⁅localSpan ZS H, localSpan L T⁆ hUH
    (le_normalizer_iff_commutator_le_left.mp (hL0H.trans action.normalizes))
    action.layer_le action.normalizes_layer).mp hb


omit [(Z.subgroupOf H).Normal] in
/-- The literal component section and the global fixed space span U/Z, from the legitimate B.2.14 application. -/
theorem componentSection_split_of_source [Finite G]
    (hB : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (ZS L Y0 T : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hchar : Theory.GroupTheory.generalizedFitting H = pCore 2 H)
    (hgen : H = reducedOvergroup L Y0 T)
    (hcomm : L = ⁅L, Y0⁆) (hTY : T ≤ normalizer (Y0 : Set G))
    (hYL0 : Y0 ≤ localSpan L T) (hZST : ZS ≤ T)
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = T)
    (h48 : ⁅ZS, T⁆ ≤ Z) :
    componentSection Z H ZS L T ⊔ fixedSpace action.representation ⊤ = ⊤ := by
  have hTH : T ≤ H := hP ▸ map_subtype_le _
  exact componentSection_split_of_commutatorPreimage Z H ZS L T action
    (conjugateSpanBy_le_self (hZST.trans hTH)) (hgen ▸ le_sup_left)
    (preimage_split_of_source H Z hB ZS L Y0 T action hchar hgen hcomm hTY
      hYL0 hZST P hP h48)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.Splitting
