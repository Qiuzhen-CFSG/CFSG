module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.CharacteristicReduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.ComponentQuotient
/-!
# Characteristic replacement without a binary quotient assumption

The minimum characteristic replacement from MS93 Section 7 depends on the
normal component, the product H=KR and the original MS3 condition. This
extension discharges those inputs separately, so the same literal replacement
is available in the Sp4(4) branch. The embedded commutator core is preserved.
No claim that the replacement has already removed outer automorphisms is made;
that is the separate source theorem MS93 (3.4).

Source: MS93, Section 7, pp.932–933.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {J : Type*} [Group J] [Finite J] {L R : Subgroup J}

namespace CharacteristicReduction
variable (d : CharacteristicReduction L R)
omit [Finite J] in
/-- The replacement group is normal in the original group. -/
theorem overgroup_normal_of_sup [L.Normal] (hsup : L ⊔ R = ⊤) : d.overgroup.Normal := by
  let := d.characteristic
  have hRU : R ≤ normalizer (d.ambient : Set J) :=
    R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R d.subgroup)
  apply normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  rw [← hsup]
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
theorem core_eq_of_sup [L.Normal] (hsup : L ⊔ R = ⊤) :
    pCore 2 d.overgroup = (pCore 2 J).comap d.overgroup.subtype :=
  pCore_subnormal_eq_comap 2 (d.overgroup_normal_of_sup hsup).isSubnormal

/-- The replacement preserves the intrinsic core of the same perfect component. -/
theorem commutatorCore_eq_intrinsic_of_sup [L.Normal]
    (hsup : L ⊔ R = ⊤) (hperfect : IsPPerfect 2 L) :
    (⁅pCore 2 d.overgroup, L.subgroupOf d.overgroup⁆).map d.overgroup.subtype =
      (blockU L).map L.subtype := by
  rw [map_commutator, d.core_eq_of_sup hsup, map_comap_eq, range_subtype,
    map_subgroupOf_eq_of_le (show L ≤ d.overgroup from le_sup_left)]
  have hi := MSCentralOrbit.commutatorCore_eq_intrinsic L hperfect
  apply le_antisymm
  · exact (commutator_mono inf_le_right le_rfl).trans hi.le
  · have he : (blockU L).map L.subtype = ⁅(pCore 2 L).map L.subtype, L⁆ := by
      change (⁅pCore 2 L,(⊤ : Subgroup L)⁆).map L.subtype = _
      rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rw [he]
    apply commutator_mono _ le_rfl
    exact le_inf ((map_subtype_le _).trans le_sup_left)
      (by
        rw [pCore_subnormal_eq_comap 2 (inferInstance : L.Normal).isSubnormal,
          map_comap_eq, range_subtype]
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
theorem msCharacteristic_of_sup (hsup : L ⊔ R = ⊤) (hms : MSCharacteristicCondition R) : MSCharacteristicCondition d.radical := by
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
    rw [← hsup]
    exact sup_le (le_sup_left.trans hnorm)
      (R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R A))
  have hAbot : A = ⊥ := hms.eq_bot_of_normal A hAn
  have hKbot : K = ⊥ := by
    apply map_injective d.subgroup.subtype_injective
    change K.map d.subgroup.subtype = ⊥ at hAbot
    simpa only [Subgroup.map_bot] using hAbot
  apply hCne
  rw [← hKC, hKbot, Subgroup.map_bot]

/-- The defining containment supplies the replacement two-core. -/
theorem core_le_radical_of_sup [L.Normal] (hsup : L ⊔ R = ⊤) :
    pCore 2 d.overgroup ≤ d.radical := by
  rw [d.core_eq_of_sup hsup]
  intro x hx
  exact d.core_containment ⟨x.property,hx⟩

end CharacteristicReduction

omit [Finite J] in
/-- The source minimum exists as soon as the original radical contains O₂. -/
theorem exists_characteristicReduction_of_core_le
    (hQR : pCore 2 J ≤ R) : Nonempty (CharacteristicReduction L R) := by
  classical
  have he : ∃ n : ℕ, ∃ T : Subgroup R, T.Characteristic ∧
      (L ⊔ T.map R.subtype) ⊓ pCore 2 J ≤ T.map R.subtype ∧ Nat.card T = n := by
    refine ⟨Nat.card (⊤ : Subgroup R), ⊤, inferInstance, ?_, rfl⟩
    simpa only [← MonoidHom.range_eq_map, range_subtype] using
      (inf_le_right.trans hQR : (L ⊔ R) ⊓ pCore 2 J ≤ R)
  obtain ⟨T,hT,hcut,hcard⟩ := Nat.find_spec he
  refine ⟨⟨T,hT,hcut,?_⟩⟩
  intro U hU hUcut
  rw [hcard]
  exact Nat.find_min' he ⟨U,hU,hUcut,rfl⟩

/-- Application to the actual MS component: no quotient-recognition premise
is needed for the Section 7 characteristic replacement. -/
theorem component_characteristic_reduction (L R : Subgroup J)
    (hL : L.IsCComponent) (hp : IsPGroup 2 R)
    (hprod : ∀ g : J, ∃ l ∈ L, ∃ r ∈ R, l*r=g)
    (hQR : pCore 2 J ≤ R) (hms : MSCharacteristicCondition R) :
    ∃ d : CharacteristicReduction L R,
      d.overgroup.Normal ∧ MSCharacteristicCondition d.radical ∧
      pCore 2 d.overgroup ≤ d.radical ∧
      (⁅pCore 2 d.overgroup,L.subgroupOf d.overgroup⁆).map d.overgroup.subtype =
        (blockU L).map L.subtype := by
  have hres := MSCentralOrbit.component_eq_residual L R hL hp hprod
  let : L.Normal := by rw [← hres]; infer_instance
  have hsup : L ⊔ R = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨l,hl,r,hr,rfl⟩ := hprod g
    exact mul_mem (mem_sup_left hl) (mem_sup_right hr)
  obtain ⟨d⟩ := exists_characteristicReduction_of_core_le (L := L) hQR
  have hperfect : IsPPerfect 2 L := by
    rw [← hres]
    exact isPPerfect_pResidual 2
  exact ⟨d,d.overgroup_normal_of_sup hsup,d.msCharacteristic_of_sup hsup hms,
    d.core_le_radical_of_sup hsup,d.commutatorCore_eq_intrinsic_of_sup hsup hperfect⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93
