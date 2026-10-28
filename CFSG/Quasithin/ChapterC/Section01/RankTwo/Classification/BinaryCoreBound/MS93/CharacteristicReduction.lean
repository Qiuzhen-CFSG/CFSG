module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.InnerQuotient
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The characteristic replacement in the final MS93 reduction

For the genuine binary MS input, choose a characteristic subgroup `T₀` of
`R` of minimum order subject to `(L T₀) ∩ O₂(J) ≤ T₀`. The candidate `R`
exists because the odd-index radical condition puts `O₂(J)` inside `R`.
The actual replacement group `J₀ = L T₀` is normal in `J`: `R` normalizes
both factors and `L` is contained in their join.

Its two-core is `O₂(J) ∩ J₀`. The existing internal commutator identity for
`L` sandwiches the image of `[O₂(J₀),L]` between the same actual subgroup
`D = [O₂(J),L]`, so the replacement preserves `D`. A characteristic subgroup
of `T₀` normal in `J₀` is characteristic in `R` and normalized by both `L`
and `R`; the original MS3 therefore makes it trivial. Minimum order gives
the source's terminal characteristic-minimality clause. Finally, restricting
the already proved core projection gives the compatible SL₃(2) quotient.

This construction does not assert that `T₀` satisfies the original odd-index
radical condition, or create a new `BinaryMS.Input` on `J₀`.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
Section 7, printed pp.932--933, the characteristic replacement before the
application of Section 4. In that notation `M = J`, `T = R`, and `Q = O₂(J)`.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93

open Subgroup

universe u
variable {J : Type u} [Group J] {κ : GroupClass.{u}} {L R : Subgroup J}

/-- A constructed minimum-order characteristic replacement, with its literal
subgroup image and the source core-containment property. -/
structure CharacteristicReduction (L R : Subgroup J) where
  subgroup : Subgroup R
  characteristic : subgroup.Characteristic
  core_containment : (L ⊔ subgroup.map R.subtype) ⊓ pCore 2 J ≤ subgroup.map R.subtype
  card_minimal : ∀ T : Subgroup R, T.Characteristic →
    (L ⊔ T.map R.subtype) ⊓ pCore 2 J ≤ T.map R.subtype →
    Nat.card subgroup ≤ Nat.card T

namespace CharacteristicReduction

variable (d : CharacteristicReduction L R)

/-- The replacement subgroup embedded in the original ambient group. -/
abbrev ambient : Subgroup J := d.subgroup.map R.subtype
/-- The actual replacement group generated with the original component. -/
abbrev overgroup : Subgroup J := L ⊔ d.ambient
/-- The same replacement subgroup, now inside the replacement group. -/
abbrev radical : Subgroup d.overgroup := d.ambient.subgroupOf d.overgroup

/-- A further characteristic subgroup satisfying the source containment
cannot be smaller than the chosen replacement. -/
theorem minimal [Finite J] (T : Subgroup R) (hle : T ≤ d.subgroup)
    (hchar : (T.subgroupOf d.subgroup).Characteristic)
    (hcut : (L ⊔ T.map R.subtype) ⊓ pCore 2 J ≤ T.map R.subtype) : T = d.subgroup := by
  let := d.characteristic
  let := hchar
  have hc : T.Characteristic := by
    rw [← map_subgroupOf_eq_of_le hle]
    infer_instance
  exact eq_of_le_of_card_ge hle (d.card_minimal T hc hcut)

/-- The replacement group is normal in the original group. -/
theorem overgroup_normal [Finite J] (h : Input κ L R) : d.overgroup.Normal := by
  let := d.characteristic
  let := h.component_normal
  have hRU : R ≤ normalizer (d.ambient : Set J) :=
    R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R d.subgroup)
  apply normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  rw [← h.sup_eq_top]
  apply sup_le
  · exact le_sup_left.trans d.overgroup.le_normalizer
  · intro r hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (L ⊔ d.ambient).map (MulAut.conj r).toMonoidHom = L ⊔ d.ambient
    have hL : L.map (MulAut.conj r).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp (show r ∈ normalizer (L : Set J) by
        rw [normalizer_eq_top]; trivial)
    have hU : d.ambient.map (MulAut.conj r).toMonoidHom = d.ambient :=
      mem_normalizer_iff_map_conj_eq.mp (hRU hr)
    rw [Subgroup.map_sup, hL, hU]

/-- Its intrinsic two-core is the original two-core restricted to it. -/
theorem core_eq [Finite J] (h : Input κ L R) :
    pCore 2 d.overgroup = (pCore 2 J).comap d.overgroup.subtype :=
  pCore_subnormal_eq_comap 2 (d.overgroup_normal h).isSubnormal

/-- Replacement preserves the actual ambient commutator core, through the
specified subgroup inclusion. -/
theorem commutatorCore_eq [Finite J] (h : Input κ L R) :
    (⁅pCore 2 d.overgroup, L.subgroupOf d.overgroup⁆).map d.overgroup.subtype =
      commutatorCore L := by
  rw [map_commutator, d.core_eq h, map_comap_eq, range_subtype,
    map_subgroupOf_eq_of_le (show L ≤ d.overgroup from le_sup_left)]
  apply le_antisymm
  · exact commutator_mono inf_le_right le_rfl
  · have he : commutatorCore L = ⁅(pCore 2 L).map L.subtype, L⁆ := by
      rw [h.commutatorCore_eq_internal, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rw [he]
    apply commutator_mono _ le_rfl
    have hOL : (pCore 2 L).map L.subtype ≤ L := map_subtype_le _
    exact le_inf (hOL.trans le_sup_left) (h.componentCore_eq_inf.le.trans inf_le_left)

/-- Restriction of the original compatible matrix projection. -/
noncomputable def projection [Finite J] (h : Input κ L R) :
    d.overgroup →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  h.coreProjection.comp d.overgroup.subtype

/-- The original component already supplies every matrix in the quotient. -/
theorem projection_surjective [Finite J] (h : Input κ L R) :
    Function.Surjective (d.projection h) := by
  intro y
  obtain ⟨z, hz⟩ := h.quotientEquiv.surjective y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
  refine ⟨⟨l, (show L ≤ d.overgroup from le_sup_left) l.property⟩, ?_⟩
  exact (h.coreProjection_component l).trans hz

/-- The restricted projection has precisely the replacement two-core as kernel. -/
theorem projection_kernel [Finite J] (h : Input κ L R) :
    (d.projection h).ker = pCore 2 d.overgroup := by
  change h.coreProjection.ker.comap d.overgroup.subtype = pCore 2 d.overgroup
  rw [h.coreProjection_kernel, d.core_eq h]

/-- The actual replacement quotient in the original SL₃(2) model. -/
noncomputable def quotientEquiv [Finite J] (h : Input κ L R) :
    (d.overgroup ⧸ pCore 2 d.overgroup) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq (d.projection_kernel h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (d.projection h) (d.projection_surjective h))

/-- The quotient equivalence agrees with the original projection on representatives. -/
theorem quotientEquiv_mk [Finite J] (h : Input κ L R) (x : d.overgroup) :
    d.quotientEquiv h (QuotientGroup.mk' (pCore 2 d.overgroup) x) =
      h.coreProjection (x : J) := by
  rfl

/-- The canonical identification of the two intrinsic replacement carriers. -/
noncomputable def radicalEquiv : d.subgroup ≃* d.radical :=
  (d.subgroup.equivMapOfInjective R.subtype R.subtype_injective).trans
    (subgroupOfEquivOfLe (show d.ambient ≤ d.overgroup from le_sup_right)).symm

/-- This carrier identification preserves the original ambient element. -/
theorem radicalEquiv_apply (t : d.subgroup) :
    (((d.radicalEquiv t : d.radical) : d.overgroup) : J) = ((t : R) : J) := by
  rfl

private theorem characteristic_comap_equiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (C : Subgroup B) [C.Characteristic] : (C.comap e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  change e (a x) ∈ C
  have hh := characteristic_iff_le_comap.mp (inferInstance : C.Characteristic)
    ((e.symm.trans a).trans e) hx
  change e (a (e.symm (e x))) ∈ C at hh
  simpa only [MulEquiv.symm_apply_apply] using hh

/-- The replacement satisfies MS3 inside its actual overgroup; no new radicality
hypothesis is used. -/
theorem msCharacteristic [Finite J] (h : Input κ L R) : MSCharacteristicCondition d.radical := by
  intro C hC hCne hCn
  let := d.characteristic
  let := hC
  let e := d.radicalEquiv
  let K : Subgroup d.subgroup := C.comap e.toMonoidHom
  let : K.Characteristic := characteristic_comap_equiv e C
  let A : Subgroup R := K.map d.subgroup.subtype
  let : A.Characteristic := inferInstance
  have hKC : K.map e.toMonoidHom = C := by
    dsimp only [K]
    rw [map_comap_eq, MonoidHom.range_eq_top_of_surjective e.toMonoidHom e.surjective,
      top_inf_eq]
  have he : A.map R.subtype = (C.map d.radical.subtype).map d.overgroup.subtype := by
    rw [← hKC, map_map, map_map, map_map]
    rfl
  have hCJ : ((C.map d.radical.subtype).map d.overgroup.subtype).subgroupOf
      d.overgroup |>.Normal := by
    rw [subgroupOf_map_subtype_eq]
    exact hCn
  have hnorm : d.overgroup ≤ normalizer
      ((C.map d.radical.subtype).map d.overgroup.subtype : Set J) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp hCJ
  rw [← he] at hnorm
  have hAn : (A.map R.subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [← h.sup_eq_top]
    exact sup_le (le_sup_left.trans hnorm)
      (R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R A))
  have hAbot : A = ⊥ := h.characteristic.eq_bot_of_normal A hAn
  have hKbot : K = ⊥ := by
    apply map_injective d.subgroup.subtype_injective
    change K.map d.subgroup.subtype = ⊥ at hAbot
    simpa only [Subgroup.map_bot] using hAbot
  apply hCne
  rw [← hKC, hKbot, Subgroup.map_bot]

/-- The defining containment puts the replacement two-core inside its radical. -/
theorem core_le_radical [Finite J] (h : Input κ L R) :
    pCore 2 d.overgroup ≤ d.radical := by
  rw [d.core_eq h]
  intro x hx
  exact d.core_containment ⟨x.property, hx⟩


end CharacteristicReduction

/-- Existence of the characteristic replacement from the genuine binary MS input. -/
theorem exists_characteristicReduction [Finite J] (h : Input κ L R) :
    Nonempty (CharacteristicReduction L R) := by
  classical
  have he : ∃ n : ℕ, ∃ T : Subgroup R, T.Characteristic ∧
      (L ⊔ T.map R.subtype) ⊓ pCore 2 J ≤ T.map R.subtype ∧ Nat.card T = n := by
    refine ⟨Nat.card (⊤ : Subgroup R), ⊤, inferInstance, ?_, rfl⟩
    simpa only [← MonoidHom.range_eq_map, range_subtype, h.sup_eq_top, top_inf_eq]
      using h.radical.twoCore_le
  obtain ⟨T, hT, hcut, hcard⟩ := Nat.find_spec he
  refine ⟨⟨T, hT, hcut, ?_⟩⟩
  intro U hU hUcut
  rw [hcard]
  exact Nat.find_min' he ⟨U, hU, hUcut, rfl⟩

/-- A chosen replacement with all defining fields proved from the input. -/
noncomputable def characteristicReduction [Finite J] (h : Input κ L R) :
    CharacteristicReduction L R := Classical.choice (exists_characteristicReduction h)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
