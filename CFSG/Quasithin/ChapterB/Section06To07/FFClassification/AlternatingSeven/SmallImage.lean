module
public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.PrimitiveSeven.OrderAlternative
public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.PrimitiveSeven.Order168Recognition
public import Theory.SpecificGroups.Alternating.SevenPerfectSylow
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.Alternating.OddCentralCovers
public import Theory.SpecificGroups.AlternatingFiveCore
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.AlternatingSix.Image
public import Theory.GroupAction.PrimitiveSimplicity
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.BinaryLinear.SylowImage
public import Theory.SpecificGroups.Alternating.SevenThreeSection

/-!
# Residual recognition in an alternating seven-letter image

A perfect subgroup of A₇ with quasisimple two-core quotient is A₅, A₆,
or PSL₃(2), unless it is all of A₇. Without a seven-element it fixes a
letter and the A₆ perfect-subgroup theorem applies. With a seven-element,
primitivity kills its two-core and center, and the checked primitive-seven
order and recognition theorems identify PSL₃(2).

Both A₆ and PSL₃(2) are self-normalizing here. If the subgroup is normal
in a minimal-parabolic image, either case makes that image the subgroup
itself, contradicting its two distinct Sylow parabolics. The surviving A₅
image lifts through an arbitrary solvable kernel: its Schur multiplier has
order two, and the original quotient by its own two-core has trivial two-core.

The original H-star application is LocalConfigurationNaturalHStarSourceResidualFive.
Source: Aschbacher–Smith, 12.2.7(2), printed pp.797–798. The elementary
seven-point recognition is reused from the narrow MainConverse modules;
no constructed-carrier catalogue or converse classification is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory MulAction Equiv
namespace CFSG.Quasithin.ChapterB.AlternatingSevenImage
local notation "A7" => alternatingGroup (Fin 7)
local notation "S7" => Perm (Fin 7)

private theorem primitive_of_seven_dvd (B : Subgroup A7) (h7 : 7 ∣ Nat.card B) :
    IsPreprimitive B (Fin 7) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 7 h7
  have ho : orderOf b.val.val = 7 := (orderOf_coe b.val).trans ((orderOf_coe b).trans hb)
  have hc := Perm.isCycle_of_prime_order'' (by decide) ho
  have hsup : b.val.val.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [←hc.orderOf,ho]
    rfl
  let : IsPretransitive B (Fin 7) := ⟨fun x y => by
    obtain ⟨n,hn⟩ := hc.exists_zpow_eq
      (Perm.mem_support.mp (hsup ▸ Finset.mem_univ x))
      (Perm.mem_support.mp (hsup ▸ Finset.mem_univ y))
    exact ⟨b^n,hn⟩⟩
  exact IsPreprimitive.of_prime_card (by rw [Nat.card_fin]; decide)

private theorem simple_of_seven_dvd (B : Subgroup A7) [Group.IsPerfect B]
    (hq : IsQuasisimple (B ⧸ pCore 2 B)) (h7 : 7 ∣ Nat.card B) : IsSimpleGroup B := by
  let : IsPreprimitive B (Fin 7) := primitive_of_seven_dvd B h7
  have hcore : pCore 2 B = ⊥ := by
    by_contra hn
    have hd := card_dvd_card_normal_of_quasiprimitive (X := Fin 7) (pCore 2 B) hn
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
    rw [Nat.card_fin,hn] at hd
    exact (by decide : ¬ 7 ∣ 2) ((by decide : Nat.Prime 7).dvd_of_dvd_pow hd)
  let e : (B ⧸ pCore 2 B) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  let := hq
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hz : center B = ⊥ := by
    by_contra hn
    have hd : 7 ∣ Nat.card (center B) := by
      simpa only [Nat.card_fin] using
        card_dvd_card_normal_of_quasiprimitive (X := Fin 7) (center B) hn
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center B) 7 hd
    let f := (alternatingGroup (Fin 7)).subtype.comp B.subtype
    have hc := centralizer_eq_zpowers_of_prime_degree (by decide) f
      ((alternatingGroup (Fin 7)).subtype_injective.comp B.subtype_injective)
      z.val ((orderOf_coe z).trans hz)
    have ht : centralizer ({z.val} : Set B) = ⊤ := by
      apply top_unique
      intro b _
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp z.property b)
    have hcyc : IsCyclic B := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨z.val,hc.symm.trans ht⟩
    let := hcyc
    let : CommGroup B := IsCyclic.commGroup
    have hs : Subsingleton B := inferInstance
    have hcard : Nat.card B = 1 := by simp
    rw [hcard] at h7
    norm_num at h7
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem five_or_six_of_no_seven (B : Subgroup A7) [Group.IsPerfect B]
    (hne : B ≠ ⊥) (h7 : ¬ 7 ∣ Nat.card B) :
    Nonempty (B ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (B ≃* alternatingGroup (Fin 6)) := by
  let C := B.map (alternatingGroup (Fin 7)).subtype
  let e : B ≃* C := B.equivMapOfInjective _ (alternatingGroup (Fin 7)).subtype_injective
  let : Group.IsPerfect C := Group.IsPerfect.map _
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.SevenPerfectSylow.exists_fixed C (by
    rwa [card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective])
  have hBA : B ≤ stabilizer A7 i := fun b hb => hi (e ⟨b,hb⟩)
  let D := B.subgroupOf (stabilizer A7 i)
  let d : D ≃* B := subgroupOfEquivOfLe hBA
  let f := AlternatingSix.SmallIndex.pointEquiv i
  let E := D.map f.toMonoidHom
  let c : D ≃* E := D.equivMapOfInjective f.toMonoidHom f.injective
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := d.symm.toMonoidHom) d.symm.surjective
  let : Group.IsPerfect E := Group.IsPerfect.map _
  by_cases ht : E = ⊤
  · exact Or.inr ⟨d.symm.trans (c.trans ((MulEquiv.subgroupCongr ht).trans topEquiv))⟩
  · have he : E ≠ ⊥ := by
      intro he
      have hs : Subsingleton E := by rw [he]; infer_instance
      let := hs
      let : Subsingleton D := c.injective.subsingleton
      let : Subsingleton B := d.symm.injective.subsingleton
      exact hne B.eq_bot_of_subsingleton
    obtain ⟨q⟩ := AlternatingSix.PerfectSubgroups.equiv_five E he ht
    exact Or.inl ⟨d.symm.trans (c.trans q)⟩

/-- The genuine perfect subgroup alternatives needed inside the original A₇ action. -/
theorem five_six_or_three (B : Subgroup A7) [Group.IsPerfect B]
    (hq : IsQuasisimple (B ⧸ pCore 2 B)) (hne : B ≠ ⊥) (hp : B ≠ ⊤) :
    Nonempty (B ≃* alternatingGroup (Fin 5)) ∨
    Nonempty (B ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  by_cases h7 : 7 ∣ Nat.card B
  · let C := B.map (alternatingGroup (Fin 7)).subtype
    let e : B ≃* C := B.equivMapOfInjective _ (alternatingGroup (Fin 7)).subtype_injective
    let : IsSimpleGroup B := simple_of_seven_dvd B hq h7
    let : IsSimpleGroup C := e.symm.isSimpleGroup
    let : Group.IsPerfect C := Group.IsPerfect.map _
    have hC : IsPreprimitive C (Fin 7) := by
      let : IsPreprimitive B (Fin 7) := primitive_of_seven_dvd B h7
      let φ : Fin 7 →ₑ[e.toMonoidHom] Fin 7 := ⟨id,fun _ _ => rfl⟩
      exact IsPreprimitive.of_surjective (f := φ) Function.surjective_id
    have hproper : ¬ alternatingGroup (Fin 7) ≤ C := by
      intro hc
      apply hp
      apply top_unique
      intro b _
      obtain ⟨a,ha,he⟩ := hc b.property
      exact (Subtype.ext he : a = b) ▸ ha
    have hns : ¬ Group.IsSolvable C := Group.IsPerfect.not_isSolvable C
    have hc := CFSG.Quasithin.MainConverse.primitiveSeven_simple_card_eq_168 C hC
      inferInstance hns hproper
    obtain ⟨q⟩ := CFSG.Quasithin.MainConverse.primitiveSeven_order168_equiv_psl3Two C hC
      inferInstance hc
    exact Or.inr (Or.inr ⟨e.trans (q.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide)))⟩)
  · rcases five_or_six_of_no_seven B hne h7 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

private theorem normalizer_ne_top (B : Subgroup A7) (hne : B ≠ ⊥) (hp : B ≠ ⊤) :
    normalizer (B : Set A7) ≠ ⊤ := by
  intro hn
  let : B.Normal := normalizer_eq_top_iff.mp hn
  let : IsSimpleGroup A7 := alternatingGroup.isSimpleGroup (by simp)
  exact (inferInstance : B.Normal).eq_bot_or_eq_top.elim hne hp

private theorem normalizer_six (B : Subgroup A7) (hne : B ≠ ⊥) (hp : B ≠ ⊤)
    (e : B ≃* alternatingGroup (Fin 6)) : normalizer (B : Set A7) = B := by
  let N := normalizer (B : Set A7)
  have hb : Nat.card B = 360 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hc : Nat.card A7 = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hi : B.index = 7 := by have h := B.card_mul_index; rw [hb,hc] at h; omega
  have hd0 : N.index ∣ B.index := index_dvd_of_le (show B ≤ N from B.le_normalizer)
  have hd : N.index ∣ 7 := by simpa only [hi] using hd0
  have hn : N.index = 7 := (Nat.dvd_prime (by decide)).mp hd |>.resolve_left
    (fun he => normalizer_ne_top B hne hp (index_eq_one.mp he))
  have hcard : Nat.card N = 360 := by have h := N.card_mul_index; rw [hn,hc] at h; omega
  exact (eq_of_le_of_card_ge B.le_normalizer (by rw [hcard,hb])).symm

private theorem normalizer_three (B : Subgroup A7) (hne : B ≠ ⊥) (hp : B ≠ ⊤)
    (e : B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : normalizer (B : Set A7) = B :=
  alternatingGroup.SevenThreeSection.eq_of_le_of_card B _
    ((Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_SL) B.le_normalizer
    (normalizer_ne_top B hne hp)

/-- A perfect normal subgroup of a minimal-parabolic seven-letter image is A₅.
The intrinsic two-core quotient is only assumed quasisimple, with no model marking. -/
theorem five_of_minimalParabolic (J : Subgroup A7) (S : Sylow 2 J)
    (hP : IsMinimalParabolicOver S ⊤) (B : Subgroup A7) [Group.IsPerfect B]
    (hq : IsQuasisimple (B ⧸ pCore 2 B)) (hne : B ≠ ⊥) (hp : B ≠ ⊤)
    (hBJ : B ≤ J) (hJB : J ≤ normalizer (B : Set A7)) :
    Nonempty (B ≃* alternatingGroup (Fin 5)) := by
  rcases five_six_or_three B hq hne hp with h | h
  · exact h
  rcases h with h | h
  · obtain ⟨e⟩ := h
    have he : J = B := le_antisymm ((normalizer_six B hne hp e) ▸ hJB) hBJ
    let f : J ≃* alternatingGroup (Fin 6) := (MulEquiv.subgroupCongr he).trans e
    have hmin := minimalParabolic_surjective S hP f.toMonoidHom f.surjective
      (by rw [f.toMonoidHom.ker_eq_bot_iff.mpr f.injective]; exact bot_le)
    exact (not_minimalParabolic_alternatingSix _ hmin).elim
  · obtain ⟨e⟩ := h
    have he : J = B := le_antisymm ((normalizer_three B hne hp e) ▸ hJB) hBJ
    let f : J ≃* BinaryLinear.OuterCyclic.LinearGroup 3 :=
      ((MulEquiv.subgroupCongr he).trans e).trans (BinaryLinear.OuterCyclic.slEquivLinear 3)
    let U := S.mapSurjective (f := f.toMonoidHom) f.surjective
    have hs := minimalParabolic_image_solvable_binary (by decide : 0 < 3) S hP f.toMonoidHom U rfl
    let := hs
    let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective
      (f := f.toMonoidHom.rangeRestrict) (by intro x y h; exact f.injective (congrArg Subtype.val h))
    let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
      (f := inclusion hBJ) (inclusion_injective hBJ)
    let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hne
    exact (Group.IsPerfect.not_isSolvable B inferInstance).elim

private theorem quasisimple_core_surjective {A D : Type*} [Group A] [Finite A]
    [Group D] [Finite D] [IsQuasisimple (A ⧸ pCore 2 A)]
    (f : A →* D) (hf : Function.Surjective f) (hs : ¬ Group.IsSolvable D) :
    IsQuasisimple (D ⧸ pCore 2 D) := by
  let : Nontrivial (D ⧸ pCore 2 D) := QuotientGroup.nontrivial_iff.mpr (by
    intro ht
    have hp : IsPGroup 2 (⊤ : Subgroup D) := ht ▸ pCore_isPGroup
    let : Group.IsNilpotent D := (hp.of_equiv topEquiv).isNilpotent
    exact hs inferInstance)
  have hm : (pCore 2 A).map f ≤ pCore 2 D :=
    le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map f hf,pCore_isPGroup.map f⟩
  let q := QuotientGroup.map (pCore 2 A) (pCore 2 D) f (map_le_iff_le_comap.mp hm)
  exact IsQuasisimple.of_surjective q (QuotientGroup.map_surjective_of_surjective _ _ f
    ((QuotientGroup.mk'_surjective _).comp hf) _)

private theorem core_five_of_surjective {A : Type*} [Group A] [Finite A]
    [IsQuasisimple (A ⧸ pCore 2 A)] (f : A →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) : Nonempty ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5)) := by
  have hm : (pCore 2 A).map f ≤ pCore 2 (alternatingGroup (Fin 5)) :=
    le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map f hf,pCore_isPGroup.map f⟩
  rw [alternatingGroup.five_twoCore_eq_bot, map_le_iff_le_comap, MonoidHom.comap_bot] at hm
  let Q := A ⧸ pCore 2 A
  let r := QuotientGroup.lift (pCore 2 A) f hm
  have hr : Function.Surjective r := QuotientGroup.lift_surjective_of_surjective _ _ hf _
  have hk : r.ker = center Q := by
    have hh := IsQuasisimple.comap_center_of_surjective r hr
    rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 5)), MonoidHom.comap_bot] at hh
    exact hh
  let E : (Q ⧸ center Q) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hr)
  have hd := GLS3.Chapter5.OddCentralCovers.center_card_dvd_two_of_nonexceptional
    5 (by decide) (by decide) (by decide) E
  have hz : center Q = ⊥ := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with hc | hc
    · exact (eq_bot_iff_card _).mpr hc
    · have hp : IsPGroup 2 (center Q) := IsPGroup.of_card (n := 1) (by simpa using hc)
      have hle : center Q ≤ pCore 2 Q := le_sSup ⟨inferInstance,hp⟩
      rw [pCore_quotient_pCore_eq_bot] at hle
      exact bot_unique hle
  exact ⟨QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans E)⟩

/-- An actual alternating seven-letter action with solvable kernel identifies
its normal quasisimple-core Sylow supplement modulo the supplement's own two-core. -/
theorem normal_supplement_core_five
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (hP : IsMinimalParabolicOver T ⊤) (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    [IsQuasisimple (K ⧸ pCore 2 K)] (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hs : ¬ Group.IsSolvable K) (f : G →* A7) (hk : Group.IsSolvable f.ker) :
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) := by
  let := hk
  let B := K.map f
  let J := f.range
  let q := f.subgroupMap K
  let : Group.IsPerfect B := Group.IsPerfect.map _
  have hns : ¬ Group.IsSolvable B := fun h =>
    hs ((Group.isSolvable_map_iff_of_solvable_ker f K).mp h)
  have hn : B ≠ ⊥ := by
    intro he
    apply hns
    rw [he]
    infer_instance
  have hq := quasisimple_core_surjective q (f.subgroupMap_surjective K) hns
  have hp : B ≠ ⊤ := by
    intro he
    let e : K ⧸ q.ker ≃* A7 :=
      (QuotientGroup.quotientKerEquivOfSurjective q (f.subgroupMap_surjective K)).trans
        ((MulEquiv.subgroupCongr he).trans topEquiv)
    apply normal_supplement_action_quotient_not_alternating T K hgen (MulEquiv.refl K)
      f q.ker ?_ (Or.inl rfl) e hP
    ext x
    exact (Subtype.ext_iff : q x = 1 ↔ (q x).val = (1 : B).val).symm
  have hBJ : B ≤ J := map_le_range f K
  have hJN : J ≤ normalizer (B : Set A7) := by
    have hh := le_normalizer_map (f := f) (H := K)
    rw [normalizer_eq_top, ←MonoidHom.range_eq_map] at hh
    exact hh
  have hJs : ¬ Group.IsSolvable J := by
    intro h
    let := h
    exact hns (Group.isSolvable_of_isSolvable_injective (f := inclusion hBJ) (inclusion_injective hBJ))
  have hmin := minimalParabolic_surjective_of_not_solvable T hP f.rangeRestrict
    f.rangeRestrict_surjective hJs
  obtain ⟨e⟩ := five_of_minimalParabolic J (T.mapSurjective f.rangeRestrict_surjective)
    hmin B hq hn hp hBJ hJN
  exact core_five_of_surjective (e.toMonoidHom.comp q)
    (e.surjective.comp (f.subgroupMap_surjective K))

end CFSG.Quasithin.ChapterB.AlternatingSevenImage
