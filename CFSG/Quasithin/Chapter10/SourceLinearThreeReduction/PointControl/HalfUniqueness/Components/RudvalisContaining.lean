module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.HeldContaining

/-!
# Excluding the Rudvalis containing quotient in 10.2.6

The original local component has a noncentral two-core, witnessed by its
nonzero fully moved module. Since a quasisimple containing component has
central two-core, the image of the original component retains nontrivial
two-core in the literal containing quotient.

The source full Sylow intersects the containing component in its full
intrinsic Sylow. The mapped local component is subnormal in its join with
that Sylow, so the join also has nontrivial two-core. Its core normalizer
is a genuine Sylow-containing two-local of the actual Rudvalis carrier.
The proved local cover places it in a conjugate of max4 or max6, whose
orders are 2^14*3*7 and 2^14*3*5. Neither admits a Suzuki simple section.
Thus three divides the original quotient. The already proved distinctness
and ranked-enlargement contradiction exclude either original strict factor.

The complete containing-model sieve now leaves only a strict J4 quotient.
That row, the zero-kernel binary-three normalizer and final half-Sylow assembly
remain with qt-d-10-nona5-half-sylow-unique. The independent ModuleChoiceAt
input belongs to qt-d-10-nona5-point-selection, with final discharge and the
unconditional half-Sylow result retained by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith A.3.12 and 10.2.6, pp.47--48,748--749; GLS3 Table 5.3r.
The imported Rudvalis cover uses the original ATLAS carrier and literal subgroups.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 ChapterA.Section03 ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H K : Subgroup G} {s : G}

private theorem core_not_central
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K) :
    ¬ ((L.map (MulAut.conj s).toMonoidHom).subgroupOf K).pCoreIn 2 ≤ center K := by
  let B := L.map (MulAut.conj s).toMonoidHom
  let c := (MulAut.conj s).toMonoidHom
  intro hc
  have hBC : B.pCoreIn 2 ≤ centralizer (B : Set G) := by
    intro b hb a ha
    have hbK : b ∈ K := hBK (B.pCoreIn_le 2 hb)
    have haK : a ∈ K := hBK ha
    have hbC : (⟨b,hbK⟩ : K) ∈ center K := by
      apply hc
      rw [pCoreIn_subgroupOf 2 B K hBK]
      exact hb
    exact congrArg K.subtype (mem_center_iff.mp hbC ⟨a,haK⟩)
  have hLC : L.pCoreIn 2 ≤ centralizer (L : Set G) := by
    intro l hl a ha
    apply (MulAut.conj s).injective
    simpa only [map_mul,c,MulEquiv.coe_toMonoidHom] using hBC
      ((map_pCoreIn_of_injective 2 L c (MulAut.conj s).injective) ▸ mem_map_of_mem c hl)
      (c a) (mem_map_of_mem c ha)
  have hz := commutator_eq_bot_iff_le_centralizer.mpr
    ((source_full_moved_le_component_core D).trans hLC)
  rw [source_full_moved_eq_commutator D] at hz
  exact source_full_moved_ne_bot D hz

/-- The original component retains nontrivial two-core in every containing central quotient. -/
theorem source_local_component_core_image_ne_bot
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) [IsQuasisimple K]
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    {X : Type*} [Group X] [Finite X] (d : (K ⧸ pCore 2 K) ≃* X) :
    pCore 2 (((L.map (MulAut.conj s).toMonoidHom).subgroupOf K).map
      (d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) ≠ ⊥ := by
  let A := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let q := d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let f := q.subgroupMap A
  have hqker : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap,hqker]
    exact pCore_isPGroup.comap_of_injective A.subtype A.subtype_injective
  intro he
  have hp := f.comap_pCore_of_ker_isPGroup (q.subgroupMap_surjective A) hk
  rw [he] at hp
  change f.ker = pCore 2 A at hp
  apply core_not_central D hBK
  rintro x ⟨a,ha,rfl⟩
  apply IsQuasisimple.pCore_le_center 2
  have hf : f a = 1 := MonoidHom.mem_ker.mp (hp.symm ▸ ha)
  have hq : q (a : K) = 1 := congrArg Subtype.val hf
  exact hqker ▸ MonoidHom.mem_ker.mpr hq

private theorem suzuki_order_not_dvd_rudvalis_local {m : ℕ} (hm : 1 ≤ m) {N : ℕ}
    (hN : N = 2 ^ 14 * 3 * 7 ∨ N = 2 ^ 14 * 3 * 5) :
    ¬ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∣ N := by
  rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m (by omega)]
  intro hd
  have hb : m ≤ 3 := by
    by_contra h
    have hp : (2 ^ (2*m+1)) ^ 2 ∣ N :=
      (dvd_mul_of_dvd_left (dvd_mul_left _ _) _).trans hd
    have hd18 : 2^18 ∣ N := by
      apply dvd_trans _ hp
      rw [←pow_mul]
      exact Nat.pow_dvd_pow 2 (by omega)
    rcases hN with rfl | rfl <;> norm_num at hd18
  interval_cases m <;> rcases hN with rfl | rfl <;> norm_num at hd

/-- The literal Rudvalis two-local cover excludes an original Suzuki quotient. -/
theorem ContainingPair.three_dvd_of_rudvalis_quotient
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G} [IsQuasisimple K]
    (hK : K ∈ cComponentsIn H) (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    (d : (K ⧸ pCore 2 K) ≃* Rudvalis.Model) : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  obtain ⟨S,hS,hl⟩ := C.local_sylow_in_containing hs hK hBK
  let A := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let b : L ≃* A := ((MulAut.conj s).subgroupMap L).trans (subgroupOfEquivOfLe hBK).symm
  let q := d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := d.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent q.ker := hqker.symm ▸ pCore_isNilpotent
  let S' := S.mapSurjective hq
  let B := A.map q
  have hB : B ∈ localCComponents S' := Section02.localCComponents_map_of_solvable_ker hl q
  have hBcore : pCore 2 B ≠ ⊥ := source_local_component_core_image_ne_bot D hBK d
  let P := B ⊔ (S' : Subgroup Rudvalis.Model)
  have hPcore : P.pCoreIn 2 ≠ ⊥ := by
    intro hz
    have hh := map_mono (f := P.subtype) (pCoreIn_le_of_subnormal 2 hB.subnormal)
    rw [pCoreIn_subgroupOf 2 B P le_sup_left,map_subgroupOf_eq_of_le
      ((B.pCoreIn_le 2).trans le_sup_left)] at hh
    change B.pCoreIn 2 ≤ P.pCoreIn 2 at hh
    rw [hz] at hh
    exact hBcore ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp (le_bot_iff.mp hh))
  have hPN : P ≤ normalizer (P.pCoreIn 2 : Set Rudvalis.Model) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have htwo : IsTwoLocal (normalizer (P.pCoreIn 2 : Set Rudvalis.Model)) :=
    ⟨_,hPcore,isPGroup_pCoreIn 2 P,rfl⟩
  have horder : Nat.card B ∣ 2^14*3*7 ∨ Nat.card B ∣ 2^14*3*5 := by
    rcases Rudvalis.SylowOvergroups.twoLocal_cover S' _ htwo (le_sup_right.trans hPN) with
      ⟨e,he⟩ | ⟨e,he⟩
    · left
      have hh := card_dvd_of_le ((map_mono (le_sup_left.trans hPN)).trans he)
      rwa [card_map_of_injective e.injective,Rudvalis.SylowOvergroups.max4_card] at hh
    · right
      have hh := card_dvd_of_le ((map_mono (le_sup_left.trans hPN)).trans he)
      rwa [card_map_of_injective e.injective,Rudvalis.SylowOvergroups.max6_card] at hh
  let r : L →* B := (q.subgroupMap A).comp b.toMonoidHom
  have hk : r.ker = (pCore 2 K).comap (A.subtype.comp b.toMonoidHom) := by
    ext l
    constructor
    · intro hl
      have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
      change q (b l : K) = 1 at hh
      exact hqker ▸ MonoidHom.mem_ker.mpr hh
    · intro hl
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      change q (b l : K) = 1
      exact MonoidHom.mem_ker.mp (hqker.symm ▸ hl)
  have hr : IsPGroup 2 r.ker := hk.symm ▸ pCore_isPGroup.comap_of_injective
    (A.subtype.comp b.toMonoidHom) (A.subtype_injective.comp b.injective)
  let := hr.isNilpotent
  have hd := source_quotient_card_dvd_of_solvable_image D hn r
  by_contra h3
  obtain ⟨m,hm,⟨e⟩⟩ := (Selection.ModuleChoice.component_quotient_model D hn).suzuki_of_three_free h3
  rw [Nat.card_congr e.toEquiv] at hd
  rcases horder with ho | ho
  · exact suzuki_order_not_dvd_rudvalis_local hm (.inl rfl) (hd.trans ho)
  · exact suzuki_order_not_dvd_rudvalis_local hm (.inr rfl) (hd.trans ho)

/-- The first strict Rudvalis quotient is excluded using its actual local cover. -/
theorem ContainingPair.impossible_of_first_strict_rudvalis_quotient
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : L.subgroupOf H < K₁)
    (hm : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* Rudvalis.Model)) : False := by
  let := C.first_quasisimple_of_strict hchoice hmany hn hna hstrict
  let K := K₁.map H.subtype
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv a.symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans hm.some
  have hmap : K.subgroupOf H = K₁ := comap_map_eq_self_of_injective H.subtype_injective K₁
  have hK : K ∈ cComponentsIn H := ⟨map_subtype_le _,hmap.symm ▸ C.first_component⟩
  have hLK : L ≤ K := by
    simpa only [map_subgroupOf_eq_of_le C.left_le] using map_mono (f := H.subtype) C.first_le
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  have hBK : L.map (MulAut.conj (1 : G)).toMonoidHom ≤ K := by
    simpa only [hid,Subgroup.map_id] using hLK
  exact C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_first_held_or_rudvalis_quotient (.inr hm))
    (C.three_dvd_of_rudvalis_quotient hn (one_mem _) hK hBK b)

/-- The second strict Rudvalis exclusion retains the original exchanger. -/
theorem ContainingPair.impossible_of_second_strict_rudvalis_quotient
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : (L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂)
    (hm : Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* Rudvalis.Model)) : False := by
  let := C.second_quasisimple_of_strict hchoice hmany hn hna hstrict
  let K := K₂.map H.subtype
  let a := (K₂.equivMapOfInjective H.subtype H.subtype_injective).symm
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv a.symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans hm.some
  have hmap : K.subgroupOf H = K₂ := comap_map_eq_self_of_injective H.subtype_injective K₂
  have hK : K ∈ cComponentsIn H := ⟨map_subtype_le _,hmap.symm ▸ C.second_component⟩
  have hBK : L.map (MulAut.conj t).toMonoidHom ≤ K := by
    simpa only [map_subgroupOf_eq_of_le C.right_le] using map_mono (f := H.subtype) C.second_le
  exact C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_second_held_or_rudvalis_quotient (.inr hm))
    (C.three_dvd_of_rudvalis_quotient hn C.t_mem hK hBK b)

/-- Only J4 remains among the actual strict containing quotients. -/
theorem ContainingPair.exists_strict_jankoFour_quotient
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    (L.subgroupOf H < K₁ ∧ Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* Janko4.Model)) ∨
      ((L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂ ∧
        Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* Janko4.Model)) := by
  obtain ⟨name,hm,hp,_⟩ := C.exists_strict_jankoFour_or_rudvalis_quotient hchoice hmany hn hna
  rcases hm with rfl | rfl
  · exact hp
  · rcases hp with ⟨hs,he⟩ | ⟨hs,he⟩
    · exact (C.impossible_of_first_strict_rudvalis_quotient hchoice hmany hn hna hs he).elim
    · exact (C.impossible_of_second_strict_rudvalis_quotient hchoice hmany hn hna hs he).elim

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
