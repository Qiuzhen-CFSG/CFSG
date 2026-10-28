module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Source

/-!
# Characteristic-minimal replacement for the native symplectic pair

The minimum-order characteristic edge subgroup satisfying the two-core cut
exists because the original edge contains the two-core. Its product with
the component is normal, so the two-core restricts literally. The original
MS3 condition passes to the replacement, and minimum order gives precisely
the terminal characteristic-minimality clause. The commutator comparison
uses the intrinsic component core and no assumption on its shape.

These are the group-theoretic parts of MS93 Section 7, printed pp.932--933.
The original SL3-specific constructor is not applied to the symplectic pair.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
variable {J : Type*} [Group J] [Finite J] {L R : Subgroup J}

namespace Reduction
variable (d : CharacteristicReduction L R)
omit [Finite J] in
/-- The replacement group is normal in the original group. -/
theorem overgroup_normal (hLN : L.Normal) (hgen : L ⊔ R = ⊤) : d.overgroup.Normal := by
  let := d.characteristic
  let := hLN
  have hRU : R ≤ normalizer (d.ambient : Set J) :=
    R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R d.subgroup)
  apply normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  rw [← hgen]
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
theorem core_eq (hLN : L.Normal) (hgen : L ⊔ R = ⊤) :
    pCore 2 d.overgroup = (pCore 2 J).comap d.overgroup.subtype :=
  pCore_subnormal_eq_comap 2 (overgroup_normal d hLN hgen).isSubnormal

/-- Replacement preserves the actual ambient commutator core, through the
specified subgroup inclusion. -/
theorem commutatorCore_eq (hLN : L.Normal) (hgen : L ⊔ R = ⊤)
    (hint : ⁅pCore 2 J,L⁆ = (⁅pCore 2 L,(⊤ : Subgroup L)⁆).map L.subtype) :
    (⁅pCore 2 d.overgroup, L.subgroupOf d.overgroup⁆).map d.overgroup.subtype =
      ⁅pCore 2 J,L⁆ := by
  rw [map_commutator, core_eq d hLN hgen, map_comap_eq, range_subtype,
    map_subgroupOf_eq_of_le (show L ≤ d.overgroup from le_sup_left)]
  apply le_antisymm
  · exact commutator_mono inf_le_right le_rfl
  · have he : ⁅pCore 2 J,L⁆ = ⁅(pCore 2 L).map L.subtype, L⁆ := by
      rw [hint, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rw [he]
    apply commutator_mono _ le_rfl
    have hOL : (pCore 2 L).map L.subtype ≤ L := map_subtype_le _
    exact le_inf (hOL.trans le_sup_left) (by
      rw [pCore_subnormal_eq_comap 2 hLN.isSubnormal,map_comap_eq,range_subtype]
      exact inf_le_right)

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

omit [Finite J] in
/-- The replacement satisfies MS3 inside its actual overgroup; no new radicality
hypothesis is used. -/
theorem msCharacteristic (hgen : L ⊔ R = ⊤)
    (hchar : MSCharacteristicCondition R) : MSCharacteristicCondition d.radical := by
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
    rw [← hgen]
    exact sup_le (le_sup_left.trans hnorm)
      (R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R A))
  have hAbot : A = ⊥ := hchar.eq_bot_of_normal A hAn
  have hKbot : K = ⊥ := by
    apply map_injective d.subgroup.subtype_injective
    change K.map d.subgroup.subtype = ⊥ at hAbot
    simpa only [Subgroup.map_bot] using hAbot
  apply hCne
  rw [← hKC, hKbot, Subgroup.map_bot]

/-- The defining containment puts the replacement two-core inside its radical. -/
theorem core_le_radical (hLN : L.Normal) (hgen : L ⊔ R = ⊤) :
    pCore 2 d.overgroup ≤ d.radical := by
  rw [core_eq d hLN hgen]
  intro x hx
  exact d.core_containment ⟨x.property, hx⟩

/-- Source 4.0 follows from the native minimum-order choice. -/
theorem reduced_minimal (hLN : L.Normal) (hgen : L ⊔ R = ⊤) : CharacteristicMinimal (L.subgroupOf d.overgroup) d.radical := by
  intro C hC hcut
  let := hC
  let := d.characteristic
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
  have hjoin : ((L.subgroupOf d.overgroup) ⊔ C.map d.radical.subtype).map
      d.overgroup.subtype = L ⊔ A.map R.subtype := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show L ≤ d.overgroup from le_sup_left), he]
  have hAc : (L ⊔ A.map R.subtype) ⊓ pCore 2 J ≤ A.map R.subtype := by
    rintro x ⟨hx, hn⟩
    rw [← hjoin] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [he]
    apply mem_map_of_mem
    apply hcut
    exact ⟨hy, (core_eq d hLN hgen).symm ▸ hn⟩
  have hA : A = d.subgroup := eq_of_le_of_card_ge (map_subtype_le K)
    (d.card_minimal A inferInstance hAc)
  have hK : K = ⊤ := by
    apply map_injective d.subgroup.subtype_injective
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hA
  rw [← hKC, hK, map_top_of_surjective _ e.surjective]

end Reduction

omit [Finite J] in
/-- Minimum-order characteristic replacement from the two-core containment. -/
theorem exists_reduction (hgen : L ⊔ R = ⊤) (hcore : pCore 2 J ≤ R) :
    Nonempty (CharacteristicReduction L R) := by
  classical
  have he : ∃ n : ℕ, ∃ T : Subgroup R, T.Characteristic ∧
      (L ⊔ T.map R.subtype) ⊓ pCore 2 J ≤ T.map R.subtype ∧ Nat.card T = n := by
    refine ⟨Nat.card (⊤ : Subgroup R), ⊤, inferInstance, ?_, rfl⟩
    simpa only [← MonoidHom.range_eq_map, range_subtype, hgen, top_inf_eq] using hcore
  obtain ⟨T, hT, hcut, hcard⟩ := Nat.find_spec he
  refine ⟨⟨T, hT, hcut, ?_⟩⟩
  intro U hU hUcut
  rw [hcard]
  exact Nat.find_min' he ⟨U,hU,hUcut,rfl⟩

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
