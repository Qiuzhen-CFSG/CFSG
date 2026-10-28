module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SylowUniqueContaining
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.ActionKernel
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.CubicNormality
public import Theory.GroupTheory.SimpleSectionOrder

/-!
# Solvable images of the original containing factors

The simple quotient L/O₂(L) survives every solvable-kernel representation.
If three is absent, the original nonnormal catalogue identifies that quotient
with Suzuki, of order at least 29120. Smaller targets therefore force a cubic.
A second test uses cubic divisibility in normalized full-Sylow local components.

Both tests apply to the literal first and second containing factors. Component
uniqueness in the same image proves distinctness before invoking the established
odd-rank contradiction. The actual exchanger and half-join are retained.
AlternatingContaining and ConstrainedStar apply these tests to concrete models.
Source: Aschbacher--Smith A.3.12 and 10.2.6, pp.47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

private theorem solvable_ker_comp_injective
    {A B X : Type*} [Group A] [Group B] [Group X]
    (q : B →* X) [Group.IsSolvable q.ker] (j : A →* B) (hj : Function.Injective j) :
    Group.IsSolvable (q.comp j).ker := by
  let k : (q.comp j).ker →* q.ker :=
    (j.comp (q.comp j).ker.subtype).codRestrict q.ker (fun x => x.property)
  exact Group.isSolvable_of_isSolvable_injective (f := k)
    (fun a b h => Subtype.ext (hj (congrArg Subtype.val h)))

/-- The actual simple source quotient survives a solvable representation kernel. -/
theorem source_quotient_card_dvd_of_solvable_image
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {X : Type*} [Group X] (r : L →* X) [Group.IsSolvable r.ker] :
    Nat.card (L ⧸ pCore 2 L) ∣ Nat.card X := by
  let := D.quasisimple
  let := Selection.ModuleChoice.component_quotient_simple D hn
  exact SimpleSection.card_dvd_of_solvable_representation
    (Group.IsPerfect.not_isSolvable _) (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) r

/-- A target smaller than the first Suzuki group forces a cubic in the original quotient. -/
theorem source_three_dvd_of_small_solvable_image
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {X : Type*} [Group X] [Finite X] (r : L →* X) [Group.IsSolvable r.ker]
    (hsmall : Nat.card X < 29120) : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  by_contra h3
  obtain ⟨m,hm,⟨e⟩⟩ :=
    (Selection.ModuleChoice.component_quotient_model D hn).suzuki_of_three_free h3
  have hd := source_quotient_card_dvd_of_solvable_image D hn r
  rw [Nat.card_congr e.toEquiv,BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m (by omega)] at hd
  have hq : 8 ≤ 2 ^ (2*m+1) := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 3 ≤ 2*m+1)
  have hsq : 64 ≤ (2 ^ (2*m+1)) ^ 2 := by nlinarith
  have hsub : 7 ≤ 2 ^ (2*m+1) - 1 := by omega
  have hlo : 29120 ≤ ((2 ^ (2*m+1)) ^ 2 + 1) * (2 ^ (2*m+1)) ^ 2 * (2 ^ (2*m+1) - 1) := by
    exact Nat.mul_le_mul (Nat.mul_le_mul (by omega : 65 ≤ (2 ^ (2*m+1)) ^ 2 + 1) hsq) hsub
  have hle := Nat.le_of_dvd Nat.card_pos hd
  omega

/-- Apply the small-image test to the literal conjugate contained in K. -/
theorem ContainingPair.three_dvd_of_small_solvable_image
    (_C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} {K : Subgroup G} (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    {X : Type*} [Group X] [Finite X] (q : K →* X) [Group.IsSolvable q.ker]
    (hsmall : Nat.card X < 29120) : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let b : L ≃* B := ((MulAut.conj s).subgroupMap L).trans (subgroupOfEquivOfLe hBK).symm
  let j := B.subtype.comp b.toMonoidHom
  let := solvable_ker_comp_injective q j (B.subtype_injective.comp b.injective)
  exact source_three_dvd_of_small_solvable_image D hn (q.comp j) hsmall

/-- Full-Sylow uniqueness in the first containing component proves distinctness. -/
theorem ContainingPair.distinct_of_first_sylow_unique
    (C : ContainingPair D H t K₁ K₂) (hu : SylowOvergroupComponentUnique K₁) : K₁ ≠ K₂ := by
  intro he
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  have hmap : (K₁.map H.subtype).subgroupOf H = K₁ :=
    comap_map_eq_self_of_injective H.subtype_injective K₁
  apply C.not_orbit_le_of_sylow_component_unique
    ⟨map_subtype_le _,hmap.symm ▸ C.first_component⟩ (.of_equiv a hu)
  rw [C.orbit_eq]
  apply sup_le
  · simpa only [map_subgroupOf_eq_of_le C.left_le] using map_mono (f := H.subtype) C.first_le
  · have hh := map_mono (f := H.subtype) C.second_le
    rwa [map_subgroupOf_eq_of_le C.right_le,←he] at hh

/-- The same distinctness test for the second original factor. -/
theorem ContainingPair.distinct_of_second_sylow_unique
    (C : ContainingPair D H t K₁ K₂) (hu : SylowOvergroupComponentUnique K₂) : K₁ ≠ K₂ := by
  intro he
  subst K₂
  exact C.distinct_of_first_sylow_unique hu rfl

/-- Small-image divisibility for the first original factor. -/
theorem ContainingPair.three_dvd_of_first_small_solvable_image
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {X : Type*} [Group X] [Finite X] (q : K₁ →* X) [Group.IsSolvable q.ker]
    (hsmall : Nat.card X < 29120) : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  let b := (subgroupOfEquivOfLe C.left_le).symm
  let j := (inclusion C.first_le).comp b.toMonoidHom
  let := solvable_ker_comp_injective q j ((inclusion_injective C.first_le).comp b.injective)
  exact source_three_dvd_of_small_solvable_image D hn (q.comp j) hsmall

/-- Small-image divisibility for the second original factor. -/
theorem ContainingPair.three_dvd_of_second_small_solvable_image
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {X : Type*} [Group X] [Finite X] (q : K₂ →* X) [Group.IsSolvable q.ker]
    (hsmall : Nat.card X < 29120) : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  let b := C.rightEquiv
  let j := (inclusion C.second_le).comp b.toMonoidHom
  let := solvable_ker_comp_injective q j ((inclusion_injective C.second_le).comp b.injective)
  exact source_three_dvd_of_small_solvable_image D hn (q.comp j) hsmall


/-- Exclude the pair using a small solvable image of its first component. -/
theorem ContainingPair.impossible_of_first_small_solvable_image
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {X : Type*} [Group X] [Finite X] (q : K₁ →* X) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] (hu : SylowOvergroupComponentUnique X)
    (hsmall : Nat.card X < 29120) : False := by
  exact C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_first_sylow_unique (.of_surjective q hq hu))
    (C.three_dvd_of_first_small_solvable_image hn q hsmall)

/-- Exclude the pair using a small solvable image of its second component. -/
theorem ContainingPair.impossible_of_second_small_solvable_image
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {X : Type*} [Group X] [Finite X] (q : K₂ →* X) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] (hu : SylowOvergroupComponentUnique X)
    (hsmall : Nat.card X < 29120) : False := by
  exact C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_second_sylow_unique (.of_surjective q hq hu))
    (C.three_dvd_of_second_small_solvable_image hn q hsmall)

/-- A cubic in the literal normalized local image lifts to L/O₂(L). -/
theorem ContainingPair.three_dvd_of_solvable_image_local_cubic
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    {X : Type*} [Group X] [Finite X] (q : K →* X) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker]
    (hc : ∀ (S : Sylow 2 X) (A : Subgroup X), A ∈ localCComponents S →
      (S : Subgroup X) ≤ normalizer (A : Set X) → 3 ∣ Nat.card A) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  obtain ⟨S,hS,hl⟩ := C.local_sylow_in_containing hs hK hBK
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let b : L ≃* B := ((MulAut.conj s).subgroupMap L).trans (subgroupOfEquivOfLe hBK).symm
  have hSN : (S : Subgroup K) ≤ normalizer (B : Set K) := by
    rw [←subgroupOf_normalizer_eq hBK,hS]
    intro x hx
    exact C.intersection_normalizes_conjugate_of_sylow hn hs
      ⟨hK.1 x.property,(le_normalizer_componentOrbit L T) hx.1⟩
  have hA : B.map q ∈ localCComponents (S.mapSurjective hq) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have hnA : ((S.mapSurjective hq) : Subgroup X) ≤ normalizer (B.map q : Set X) :=
    (map_mono hSN).trans (le_normalizer_map q)
  have hdB : 3 ∣ Nat.card B := (hc _ _ hA hnA).trans
    (card_dvd_of_surjective (q.subgroupMap B) (q.subgroupMap_surjective B))
  have hdL : 3 ∣ Nat.card L := (Nat.card_congr b.toEquiv).symm ▸ hdB
  by_contra hd
  have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
  rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 L) pCore_isPGroup] at hz
  exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz hdL

/-- Local-image divisibility for the first original factor. -/
theorem ContainingPair.three_dvd_of_first_solvable_image_local_cubic
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {X : Type*} [Group X] [Finite X] (q : K₁ →* X) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker]
    (hc : ∀ (S : Sylow 2 X) (A : Subgroup X), A ∈ localCComponents S →
      (S : Subgroup X) ≤ normalizer (A : Set X) → 3 ∣ Nat.card A) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let r := q.comp a.toMonoidHom
  let := solvable_ker_comp_injective q a.toMonoidHom a.injective
  have hmap : (K₁.map H.subtype).subgroupOf H = K₁ :=
    comap_map_eq_self_of_injective H.subtype_injective K₁
  have hBK : L.map (MulAut.conj (1 : G)).toMonoidHom ≤ K₁.map H.subtype := by
    have hh := map_mono (f := H.subtype) C.first_le
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
    simpa only [hid,Subgroup.map_id,map_subgroupOf_eq_of_le C.left_le] using hh
  exact C.three_dvd_of_solvable_image_local_cubic hn (one_mem _)
    ⟨map_subtype_le _,hmap.symm ▸ C.first_component⟩ hBK r (hq.comp a.surjective) hc

/-- Exclude the pair using the full-Sylow local image of its first component. -/
theorem ContainingPair.impossible_of_first_solvable_image_local_cubic
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {X : Type*} [Group X] [Finite X] (q : K₁ →* X) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] (hu : SylowOvergroupComponentUnique X)
    (hc : ∀ (S : Sylow 2 X) (A : Subgroup X), A ∈ localCComponents S →
      (S : Subgroup X) ≤ normalizer (A : Set X) → 3 ∣ Nat.card A) : False := by
  exact C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_first_sylow_unique (.of_surjective q hq hu))
    (C.three_dvd_of_first_solvable_image_local_cubic hn q hq hc)

/-- Local-image divisibility for the second original factor. -/
theorem ContainingPair.three_dvd_of_second_solvable_image_local_cubic
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {X : Type*} [Group X] [Finite X] (q : K₂ →* X) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker]
    (hc : ∀ (S : Sylow 2 X) (A : Subgroup X), A ∈ localCComponents S →
      (S : Subgroup X) ≤ normalizer (A : Set X) → 3 ∣ Nat.card A) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  let a := (K₂.equivMapOfInjective H.subtype H.subtype_injective).symm
  let r := q.comp a.toMonoidHom
  let := solvable_ker_comp_injective q a.toMonoidHom a.injective
  have hmap : (K₂.map H.subtype).subgroupOf H = K₂ :=
    comap_map_eq_self_of_injective H.subtype_injective K₂
  have hBK : L.map (MulAut.conj (t : G)).toMonoidHom ≤ K₂.map H.subtype := by
    have hh := map_mono (f := H.subtype) C.second_le
    simpa only [map_subgroupOf_eq_of_le C.right_le] using hh
  exact C.three_dvd_of_solvable_image_local_cubic hn C.t_mem
    ⟨map_subtype_le _,hmap.symm ▸ C.second_component⟩ hBK r (hq.comp a.surjective) hc

/-- Exclude the pair using the full-Sylow local image of its second component. -/
theorem ContainingPair.impossible_of_second_solvable_image_local_cubic
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {X : Type*} [Group X] [Finite X] (q : K₂ →* X) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] (hu : SylowOvergroupComponentUnique X)
    (hc : ∀ (S : Sylow 2 X) (A : Subgroup X), A ∈ localCComponents S →
      (S : Subgroup X) ≤ normalizer (A : Set X) → 3 ∣ Nat.card A) : False := by
  exact C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_second_sylow_unique (.of_surjective q hq hu))
    (C.three_dvd_of_second_solvable_image_local_cubic hn q hq hc)
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
