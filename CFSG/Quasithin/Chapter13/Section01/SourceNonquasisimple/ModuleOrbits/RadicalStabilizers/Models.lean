module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.RadicalStabilizers.ComponentCover
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.RadicalStabilizers.Coprime
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.Stabilizer
public import Theory.SpecificGroups.SL2.PointStabilizerLifts

/-!
# Radical stabilizers in the literal SL₂ cover

The central-cover map from the original odd Frattini action to the moved
component action identifies every point stabilizer with a full preimage.
Their orders therefore double: S₃ lifts to order twelve, A₄ to twenty-four,
S₄ to forty-eight, and a four-group to eight. For S₃ the original radical
prime p>3 is prime to that order, which discharges the coprimality premise
of the irreducibility theorem. For the other branches a projective four-group
lifts to Q₈. Restricting the selected Sylow through the relative normality
of C_L(u) in C_{N_G(L)}(u) places a faithful Q₈ in the literal Frattini image
of C_T(u)∩L.

The marked S₅ and natural A₅ applications discharge these action inputs on
the original moved module. The earlier module markings and the A₄, S₄ or
four-group stabilizer identifications remain the inputs supplied by the
13.1.10/module-orbit classification; this module does not assume radical
irreducibility or a quaternion lift as part of those identifications.

Source: Aschbacher--Smith, Lemma 13.1.12(1), printed pp.872--873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 Chapter12.Section02

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem card_map_rangeRestrict {A B : Type*} [Group A] [Group B]
    (f : A →* B) (H : Subgroup A) :
    Nat.card (H.map f.rangeRestrict) = Nat.card (H.map f) := by
  rw [← card_map_of_injective f.range.subtype_injective (K := H.map f.rangeRestrict),
    map_map,MonoidHom.subtype_comp_rangeRestrict]

/-- The literal stabilizer in the odd Frattini image is a double cover of
the literal moved-action stabilizer. -/
theorem component_centralizer_frattini_card
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L) :
    Nat.card (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer))) =
      Nat.card (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
        (componentAction L)) * 2 := by
  let σ := xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)
  obtain ⟨f,hf,hk,he⟩ := moved_action_central_cover h hmany hL hn ho hd
  obtain ⟨_,q,hq,hq3,_,F,hF,hfin,hcard,⟨e⟩⟩ :=
    component_frattini_cover_model h.simpleQTKE hL.1.1 hn ho hd
  have h2 : (2 : F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F
    (by rw [hcard]; exact hq.odd_of_ne_two (by omega))
  have hz : Nat.card f.ker = 2 := by
    rw [hk,Nat.card_congr (centerCongr e).toEquiv]
    exact Matrix.SpecialLinearGroup.center_rank_two_card h2
  rw [← card_map_rangeRestrict σ,
    component_point_image_preimage L p u f he]
  erw [f.card_comap_of_surjective hf,card_map_rangeRestrict,hz]

/-- The S₃ stabilizer lifts to order twelve, prime to the original radical
prime p>3. This discharges the coprimality premise of the irreducibility sieve. -/
theorem radicalCentralizerIrreducible_of_component_symmetric_three
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L)
    (hs : Nonempty ((((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (componentAction L)) ≃* Equiv.Perm (Fin 3))) :
    Nat.card (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer))) = 12 ∧
      RadicalCentralizerIrreducible L p u := by
  obtain ⟨e⟩ := hs
  have hc : Nat.card (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (componentAction L)) = 6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hc12 := component_centralizer_frattini_card h hmany hL hn ho hd u
  rw [hc] at hc12
  refine ⟨hc12,radicalCentralizerIrreducible_of_coprime_component_image
    h hmany hL hn ho hd u ?_ ?_⟩
  · intro hcomm
    have he := congrArg e ((isMulCommutative_iff.mp hcomm)
      (e.symm (Equiv.swap (0 : Fin 3) 1)) (e.symm (Equiv.swap (1 : Fin 3) 2)))
    simp only [map_mul,e.apply_symm_apply] at he
    exact (by decide : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 ≠
      Equiv.swap 1 2 * Equiv.swap 0 1) he
  · rw [hc12]
    have hp := (radical_frattini_plane h.simpleQTKE hL.1.1 hn ho hd).1
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hd12
    have hh := (Fact.out : p.Prime).dvd_mul.mp (show p ∣ 3 * 4 from hd12)
    rcases hh with hh | hh
    · have := Nat.le_of_dvd (by decide : 0 < 3) hh
      omega
    · have hh2 := (Fact.out : p.Prime).dvd_of_dvd_pow (show p ∣ 2^2 from hh)
      have := Nat.le_of_dvd (by decide : 0 < 2) hh2
      omega

omit [Finite G] in
private theorem xiFrattiniAction_range_restrict {A B X : Subgroup G}
    (hAB : A ≤ B) (hB : B ≤ normalizer (X : Set G)) :
    (xiFrattiniAction A X (hAB.trans hB)).range =
      (A.subgroupOf B).map (xiFrattiniAction B X hB) := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨inclusion hAB a,a.property,(xiFrattiniAction_restrict hAB hB a).symm⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨⟨b,hb⟩,xiFrattiniAction_restrict hAB hB ⟨b,hb⟩⟩

private theorem quaternion_in_sylow_image {H : Type*} [Group H] [Finite H]
    {P C : Subgroup H} (hs : IsSylowIn 2 P C)
    (hq : ∃ f : QuaternionGroup 2 →* C, Function.Injective f) :
    ∃ f : QuaternionGroup 2 →* P, Function.Injective f := by
  obtain ⟨S,rfl⟩ := hs
  obtain ⟨f,hf⟩ := hq
  have hp : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by norm_num [Nat.card_eq_fintype_card,QuaternionGroup.card])
  obtain ⟨R,hR⟩ := (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  let e := (R.equiv S).trans ((S : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective)
  exact ⟨e.toMonoidHom.comp ((inclusion hR).comp f.rangeRestrict),
    e.injective.comp ((inclusion_injective hR).comp
      (MonoidHom.rangeRestrict_injective_iff.mpr hf))⟩

private theorem selected_frattini_sylow
    {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} (u : G)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({u} : Set G))) :
    IsSylowIn 2
      (xiFrattiniAction (((T : Subgroup G) ⊓ L) ⊓ centralizer ({u} : Set G))
        (XiP p L) (inf_le_left.trans (inf_le_right.trans
          (XiP_invariant p L.le_normalizer)))).range
      (((centralizer ({u} : Set G)).subgroupOf L).map
        (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer))) := by
  let C := centralizer ({u} : Set G)
  let M := normalizer (L : Set G) ⊓ C
  let K := L ⊓ C
  have hKM : K ≤ M := inf_le_inf_right C L.le_normalizer
  let : (K.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
    ((inf_le_inf_left (normalizer (L : Set G)) C.le_normalizer).trans
      inf_normalizer_le_normalizer_inf)
  have hs := IndexTwo.isSylowIn_inf_of_subnormal hlocal hKM
    (inferInstance : (K.subgroupOf M).Normal).isSubnormal
  have hsL : IsSylowIn 2 ((((T : Subgroup G) ⊓ L) ⊓ C).subgroupOf L)
      (C.subgroupOf L) := by
    apply (IsSylowIn.map_iff L.subtype L.subtype_injective).mp
    simpa only [subgroupOf_map_subtype,K,C,inf_assoc,inf_left_comm,inf_comm,inf_idem,inf_left_idem] using hs
  rw [xiFrattiniAction_range_restrict (inf_le_left.trans inf_le_right)]
  exact IndexTwo.isSylowIn_map hsL _

/-- A four-group in the actual moved centralizer has a Q₈ lift in the
original Frattini action. Sylow conjugacy places a faithful Q₈ in the
literal selected local intersection, and also proves radical irreducibility. -/
theorem radical_actions_of_component_four
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hfour : ∃ A : Subgroup (componentAction L).range,
      A ≤ ((centralizer ({(u : G)} : Set G)).subgroupOf L).map
        (componentAction L).rangeRestrict ∧
      Nat.card A = 4 ∧ ∀ a : A, a ^ 2 = 1) :
    RadicalCentralizerIrreducible L p u ∧
      ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
        (((T : Subgroup G) ⊓ L) ⊓ centralizer ({(u : G)} : Set G)) (XiP p L)
        (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))).range,
        Function.Injective f := by
  let σ := xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)
  let C := ((centralizer ({(u : G)} : Set G)).subgroupOf L).map σ
  obtain ⟨f,hf,hk,he⟩ := moved_action_central_cover h hmany hL hn ho hd
  obtain ⟨_,q,hq,hq3,_,F,hF,hfin,hcard,⟨e⟩⟩ :=
    component_frattini_cover_model h.simpleQTKE hL.1.1 hn ho hd
  have h2 : (2 : F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F
    (by rw [hcard]; exact hq.odd_of_ne_two (by omega))
  obtain ⟨A,hA,hAc,hAs⟩ := hfour
  obtain ⟨w⟩ := f.quaternion_comap_of_four h2 e hf hk A hAc hAs
  have hAC : A.comap f ≤ ((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      σ.rangeRestrict := by
    rw [component_point_image_preimage L p u f he]
    exact comap_mono hA
  let j : A.comap f →* C := (σ.range.subtype.comp (A.comap f).subtype).codRestrict C (by
    intro x
    obtain ⟨l,hl,hel⟩ := hAC x.property
    exact ⟨l,hl,congrArg Subtype.val hel⟩)
  have hj : Function.Injective j := by
    intro x y hxy
    have hh := congrArg (fun z : C => (z : MulAut (XiFrattiniQuotient (XiP p L)))) hxy
    exact Subtype.ext (Subtype.ext hh)
  have hQC : ∃ j : QuaternionGroup 2 →* C, Function.Injective j :=
    ⟨j.comp w.symm.toMonoidHom,hj.comp w.symm.injective⟩
  have hQT := quaternion_in_sylow_image (selected_frattini_sylow (T := T) (L := L) (p := p) (u : G) hlocal) hQC
  refine ⟨?_,hQT⟩
  apply radicalCentralizerIrreducible_of_quaternion h.simpleQTKE hL.1.1 hn ho hd u
  obtain ⟨j,hj⟩ := hQC
  let τ := xiFrattiniAction (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))
    (XiP p L) (XiP_invariant p inf_le_left)
  have hCτ : C ≤ τ.range := by
    rintro _ ⟨l,hl,rfl⟩
    refine ⟨⟨l,L.le_normalizer l.property,hl⟩,?_⟩
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with | H x =>
      induction x using QuotientGroup.induction_on with | H x => rfl
  exact ⟨(inclusion hCτ).comp j,(inclusion_injective hCτ).comp hj⟩

omit [Finite G] in
private def mapRangeRestrictEquiv {A B : Type*} [Group A] [Group B]
    (f : A →* B) (H : Subgroup A) : H.map f.rangeRestrict ≃* H.map f :=
  ((H.map f.rangeRestrict).equivMapOfInjective f.range.subtype f.range.subtype_injective).trans
    (MulEquiv.subgroupCongr (by rw [map_map,MonoidHom.subtype_comp_rangeRestrict]))

/-- The exact four-group stabilizer branch has radical stabilizer order eight
and the required local quaternion action. -/
theorem radical_actions_of_component_four_group
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hc : Nat.card (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (componentAction L)) = 4)
    (hs : ∀ a : (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (componentAction L)), a ^ 2 = 1) :
    Nat.card (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer))) = 8 ∧
    RadicalCentralizerIrreducible L p u ∧
      ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
        (((T : Subgroup G) ⊓ L) ⊓ centralizer ({(u : G)} : Set G)) (XiP p L)
        (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))).range,
        Function.Injective f := by
  constructor
  · norm_num only [component_centralizer_frattini_card h hmany hL hn ho hd u,hc]
  apply radical_actions_of_component_four h hmany hL hn ho hd u hlocal
  let C := ((centralizer ({(u : G)} : Set G)).subgroupOf L).map
    (componentAction L).rangeRestrict
  let e := mapRangeRestrictEquiv (componentAction L)
    ((centralizer ({(u : G)} : Set G)).subgroupOf L)
  refine ⟨C,le_rfl,(Nat.card_congr e.toEquiv).trans hc,?_⟩
  intro a
  apply e.injective
  rw [map_pow,hs,map_one]

/-- In the A₄ branch, the stabilizer has order twenty-four on the radical
plane, and its local Sylow image contains the required faithful Q₈. -/
theorem radical_actions_of_component_alternating_four
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (ha : Nonempty ((((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (componentAction L)) ≃* alternatingGroup (Fin 4))) :
    Nat.card (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer))) = 24 ∧
    RadicalCentralizerIrreducible L p u ∧
      ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
        (((T : Subgroup G) ⊓ L) ⊓ centralizer ({(u : G)} : Set G)) (XiP p L)
        (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))).range,
        Function.Injective f := by
  obtain ⟨e⟩ := ha
  constructor
  · rw [component_centralizer_frattini_card h hmany hL hn ho hd u,
      Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  apply radical_actions_of_component_four h hmany hL hn ho hd u hlocal
  let C := ((centralizer ({(u : G)} : Set G)).subgroupOf L).map
    (componentAction L).rangeRestrict
  let eC : C ≃* alternatingGroup (Fin 4) :=
    (mapRangeRestrictEquiv (componentAction L) _).trans e
  let j := C.subtype.comp eC.symm.toMonoidHom
  have hj : Function.Injective j := C.subtype_injective.comp eC.symm.injective
  let A := (alternatingGroup.kleinFour (Fin 4)).map j
  refine ⟨A,?_,?_,?_⟩
  · rintro _ ⟨a,ha,rfl⟩
    exact (eC.symm a).property
  · rw [card_map_of_injective hj]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  · intro a
    obtain ⟨b,hb,he⟩ := a.property
    apply Subtype.ext
    change (a : (componentAction L).range) ^ 2 = 1
    rw [← he,← map_pow]
    have hb2 : b ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent (alternatingGroup.kleinFour (Fin 4)) ∣ 2 by
          rw [alternatingGroup.exponent_kleinFour_of_card_eq_four (by simp)])
        (⟨b,hb⟩ : alternatingGroup.kleinFour (Fin 4)))
    rw [hb2,map_one]

/-- The S₄ stabilizer in the doubled-natural branch has radical image order
forty-eight and contains the same literal local quaternion action. -/
theorem radical_actions_of_component_symmetric_four
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (ha : Nonempty ((((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (componentAction L)) ≃* Equiv.Perm (Fin 4))) :
    Nat.card (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer))) = 48 ∧
    RadicalCentralizerIrreducible L p u ∧
      ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
        (((T : Subgroup G) ⊓ L) ⊓ centralizer ({(u : G)} : Set G)) (XiP p L)
        (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))).range,
        Function.Injective f := by
  obtain ⟨e⟩ := ha
  constructor
  · rw [component_centralizer_frattini_card h hmany hL hn ho hd u,
      Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  apply radical_actions_of_component_four h hmany hL hn ho hd u hlocal
  let C := ((centralizer ({(u : G)} : Set G)).subgroupOf L).map
    (componentAction L).rangeRestrict
  let eC : C ≃* Equiv.Perm (Fin 4) :=
    (mapRangeRestrictEquiv (componentAction L) _).trans e
  let j := C.subtype.comp (eC.symm.toMonoidHom.comp (alternatingGroup (Fin 4)).subtype)
  have hj : Function.Injective j := C.subtype_injective.comp
    (eC.symm.injective.comp (alternatingGroup (Fin 4)).subtype_injective)
  let A := (alternatingGroup.kleinFour (Fin 4)).map j
  refine ⟨A,?_,?_,?_⟩
  · rintro _ ⟨a,ha,rfl⟩
    exact (eC.symm (a : Equiv.Perm (Fin 4))).property
  · rw [card_map_of_injective hj]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  · intro a
    obtain ⟨b,hb,he⟩ := a.property
    apply Subtype.ext
    change (a : (componentAction L).range) ^ 2 = 1
    rw [← he,← map_pow]
    have hb2 : b ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent (alternatingGroup.kleinFour (Fin 4)) ∣ 2 by
          rw [alternatingGroup.exponent_kleinFour_of_card_eq_four (by simp)])
        (⟨b,hb⟩ : alternatingGroup.kleinFour (Fin 4)))
    rw [hb2,map_one]

omit [Finite G] in
private def mapEquivOfKerEq {A B D : Type*} [Group A] [Group B] [Group D]
    (f : A →* B) (g : A →* D) (hk : f.ker = g.ker) (H : Subgroup A) :
    H.map f ≃* H.map g := by
  have hh : (f.subgroupMap H).ker = (g.subgroupMap H).ker := by
    ext x
    change f.subgroupMap H x = 1 ↔ g.subgroupMap H x = 1
    rw [Subtype.ext_iff,Subtype.ext_iff]
    change f x = 1 ↔ g x = 1
    exact SetLike.ext_iff.mp hk (x : A)
  exact (QuotientGroup.quotientKerEquivOfSurjective (f.subgroupMap H)
    (f.subgroupMap_surjective H)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hh).trans
        (QuotientGroup.quotientKerEquivOfSurjective (g.subgroupMap H)
          (g.subgroupMap_surjective H)))

namespace SymmetricFiveMarking

/-- The marked S₅ source branch now has no extra prime-to-p order premise. -/
theorem centralizer_index_and_radical_irreducible
    {T : Sylow 2 G} {L : Subgroup G} (d : SymmetricFiveMarking T L)
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L) (hu : u ≠ 1)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≤ 2 ∧
      RadicalCentralizerIrreducible L p u := by
  obtain ⟨hi,hs⟩ := d.centralizer_orbit h hL hn u hu hlocal
  refine ⟨hi,?_⟩
  by_cases ht : (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)
  · exact radicalCentralizerIrreducible_of_sylow_centralizes h.simpleQTKE hL.1.1 hn ho hd ht
  obtain ⟨e⟩ := (hs ht).1
  apply (radicalCentralizerIrreducible_of_component_symmetric_three h hmany hL hn ho hd u ?_).2
  let C := (centralizer ({(u : G)} : Set G)).subgroupOf L
  let i := inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
  have hiC : C.map i = ((L ⊓ centralizer ({(u : G)} : Set G)).subgroupOf
      (L ⊔ (T : Subgroup G))) := by
    ext x
    constructor
    · rintro ⟨l,hl,rfl⟩
      exact ⟨l.property,hl⟩
    · intro hx
      exact ⟨⟨x,hx.1⟩,hx.2,Subtype.ext rfl⟩
  let w := mapEquivOfKerEq (componentAction L) (d.quotient.comp i)
    d.component_kernel.symm C
  refine ⟨w.trans ((MulEquiv.subgroupCongr ?_).trans e)⟩
  rw [← map_map,hiC]

end SymmetricFiveMarking

namespace AlternatingFive.Marking
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The natural A₅ cover branch gives the literal local quaternion action
directly from its selected component Sylow. The cover marking is unchanged. -/
theorem source_radical_actions
    {T : Sylow 2 G} {L : Subgroup G} (d : AlternatingFive.Marking T L W)
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    RadicalCentralizerIrreducible L p u ∧
      ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
        (((T : Subgroup G) ⊓ L) ⊓ centralizer ({(u : G)} : Set G)) (XiP p L)
        (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))).range,
        Function.Injective f := by
  obtain ⟨S,hS,_,_⟩ := d.source_selected_four_group h hL hn u hlocal
  have hle : (S : Subgroup Representation.SL2FourNatural.SL) ≤
      (((T : Subgroup G) ⊓ L).subgroupOf L).map d.component := by
    rw [hS]
    exact map_mono (fun x hx => ⟨hx.1,x.property⟩)
  have heq := S.is_maximal'
    (((T.isPGroup'.to_le inf_le_left).comap_subtype).map d.component) hle
  have hc : (T : Subgroup G) ⊓ L ≤ centralizer ({(u : G)} : Set G) := by
    intro x hx
    have hxmap : d.component ⟨x,hx.2⟩ ∈ (S : Subgroup Representation.SL2FourNatural.SL) := by
      rw [← heq]
      exact ⟨⟨x,hx.2⟩,hx,rfl⟩
    rw [hS] at hxmap
    obtain ⟨y,hy,hey⟩ := hxmap
    apply (d.component_fixes_iff ⟨x,hx.2⟩ u).mp
    rw [← hey]
    exact (d.component_fixes_iff y u).mpr hy.2
  exact radical_actions_of_component_sylow_centralizes h.simpleQTKE hL.1.1 hn ho hd u hc

end AlternatingFive.Marking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
