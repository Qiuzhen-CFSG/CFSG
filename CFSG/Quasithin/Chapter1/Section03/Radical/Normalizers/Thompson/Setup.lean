module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Basic
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.Chapter1.Section01
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Preparation for the two-prime Thompson argument

For the actual R = O₂(Ξ_p(L)T), relative normality gives O₂(Ξ_q(L)) ≤ R.
The odd quotient equivalence makes R Sylow in Ξ_q(L)R and proves solvability
and prime support {2,q}. Normality in Ξ_q(L)T transfers characteristic two.
The intrinsic subgroups J(R), Ω₁(Z(R)), and O₂,Φ(X) retain their actual
characteristic and quotient meanings. Frattini nongeneration is used only
for subgroups containing O₂(X).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed p.513, and Definitions B.2.2, printed pp.74–75.
The local characteristic-two condition remains an explicit earlier input;
this module does not assume Thompson factorization or the two-prime conclusion.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
variable {G : Type*} [Group G]

/-- The intrinsic inverse image O₂,Φ(X) of Φ(X/O₂(X)). -/
def twoFrattiniIn (X : Subgroup G) : Subgroup X :=
  (frattini (XiQuotient X)).comap (QuotientGroup.mk' (pCore 2 X))

instance twoFrattiniIn_characteristic (X : Subgroup G) :
    (twoFrattiniIn X).Characteristic := Characteristic.comap_quotient_mk inferInstance

/-- O₂,Φ(X), as a subgroup of the original ambient group. -/
def twoFrattini (X : Subgroup G) : Subgroup G :=
  (twoFrattiniIn X).map X.subtype

theorem twoFrattini_le (X : Subgroup G) : twoFrattini X ≤ X := map_subtype_le _

theorem normalizer_le_normalizer_twoFrattini (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (twoFrattini X : Set G) :=
  normalizer_le_normalizer_characteristic_image X (twoFrattiniIn X)

theorem twoCore_le_twoFrattini (X : Subgroup G) : X.pCoreIn 2 ≤ twoFrattini X := by
  apply map_mono
  intro x hx
  change QuotientGroup.mk' (pCore 2 X) x ∈ frattini (XiQuotient X)
  change (x : XiQuotient X) ∈ frattini (XiQuotient X)
  rw [(QuotientGroup.eq_one_iff x).mpr hx]
  exact one_mem _

theorem twoCore_XiP_le_radicalCore (p q : ℕ) {L T : Subgroup G}
    (hSyl : IsSylowIn 2 T (L ⊔ T)) (hT : T ≤ normalizer (L : Set G)) :
    (XiP q L).pCoreIn 2 ≤ radicalCore p L T :=
  (pCoreIn_mono_of_normalizes (XiP_le q L)
    (L.le_normalizer.trans (normalizer_le_normalizer_XiP q L))).trans
    (twoCore_le_radicalCore p hSyl hT)

theorem radicalCore_normalizes_XiP (p q : ℕ) {L T : Subgroup G}
    (hT : T ≤ normalizer (L : Set G)) :
    radicalCore p L T ≤ normalizer (XiP q L : Set G) :=
  (radicalCore_le_join p L T).trans
    (sup_le ((XiP_le p L).trans (L.le_normalizer.trans
      (normalizer_le_normalizer_XiP q L))) (XiP_invariant q hT))

variable [Finite G]

theorem XiP_quotient_isPGroup (q : ℕ) [Fact q.Prime] (hq : Odd q) (L : Subgroup G) :
    IsPGroup q (XiQuotient (XiP q L)) :=
  ((pCore_isPGroup (p := q) (G := XiQuotient L)).to_subgroup _).of_equiv
    (xiPQuotientEquivOmega hq L).symm

theorem radicalCore_sylow_XiP_join (p q : ℕ) [Fact q.Prime] (hq : Odd q)
    {L T : Subgroup G} (hSyl : IsSylowIn 2 T (L ⊔ T))
    (hT : T ≤ normalizer (L : Set G)) :
    IsSylowIn 2 (radicalCore p L T) (XiP q L ⊔ radicalCore p L T) := by
  apply IsPGroup.exists_sylow_sup_of_coprime_index _ _
    (radicalCore_isTwoGroup p L T) (radicalCore_normalizes_XiP p q hT)
    (pCore 2 (XiP q L))
  · rw [index_eq_card]
    obtain ⟨n, hn⟩ := (XiP_quotient_isPGroup q hq L).exists_card_eq
    rw [hn]
    exact Nat.prime_two.coprime_iff_not_dvd.mp
      ((Nat.coprime_two_left.mpr hq).pow_right n)
  · exact twoCore_XiP_le_radicalCore p q hSyl hT

theorem XiP_solvable (q : ℕ) [Fact q.Prime] (hq : Odd q) (L : Subgroup G) :
    Group.IsSolvable (XiP q L) := by
  let : Group.IsNilpotent (XiQuotient (XiP q L)) :=
    (XiP_quotient_isPGroup q hq L).isNilpotent
  let : Group.IsNilpotent (pCore 2 (XiP q L)) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 (XiP q L))).mpr
    ⟨inferInstance, inferInstance⟩

theorem XiP_join_radicalCore_solvable (p q : ℕ) [Fact q.Prime] (hq : Odd q)
    {L T : Subgroup G} (hT : T ≤ normalizer (L : Set G)) :
    Group.IsSolvable (XiP q L ⊔ radicalCore p L T : Subgroup G) := by
  let X := XiP q L
  let R := radicalCore p L T
  let H := X ⊔ R
  let : Group.IsSolvable X := XiP_solvable q hq L
  let : Group.IsNilpotent R := (radicalCore_isTwoGroup p L T).isNilpotent
  let : (X.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le X.le_normalizer (radicalCore_normalizes_XiP p q hT))
  let : Group.IsSolvable (X.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (show X ≤ H from le_sup_left)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (show X ≤ H from le_sup_left)).injective
  let : Group.IsSolvable (R.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (show R ≤ H from le_sup_right)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (show R ≤ H from le_sup_right)).injective
  exact Group.isSolvable_of_normal_sup_eq_top (X.subgroupOf H) (R.subgroupOf H)
    (by rw [← subgroupOf_sup le_sup_left le_sup_right]; exact subgroupOf_self H)


/-- A two-subgroup meets Ξ_q(L) only in its two-core. -/
theorem XiP_inf_twoGroup_le_core (q : ℕ) [Fact q.Prime] (hq : Odd q)
    (L D : Subgroup G) (hD : IsPGroup 2 D) :
    XiP q L ⊓ D ≤ (XiP q L).pCoreIn 2 := by
  let X := XiP q L
  let f := QuotientGroup.mk' (pCore 2 X)
  have hi : IsPGroup 2 ((D.subgroupOf X).map f) :=
    (hD.comap_of_injective X.subtype X.subtype_injective).map f
  have hd : Disjoint ((D.subgroupOf X).map f) ⊤ :=
    hi.disjoint_of_coprime ((XiP_quotient_isPGroup q hq L).to_subgroup ⊤)
      (Nat.coprime_two_left.mpr hq)
  have he : (D.subgroupOf X).map f = ⊥ := disjoint_top.mp hd
  intro x hx
  have hk : f ⟨x, hx.1⟩ = 1 :=
    (show D.subgroupOf X ≤ f.ker from (Subgroup.map_eq_bot_iff _).mp he) hx.2
  exact mem_map.mpr ⟨⟨x, hx.1⟩, (QuotientGroup.eq_one_iff _).mp hk, rfl⟩

/-- Nongeneration for the actual O₂,Φ(X). The subgroup must contain O₂(X). -/
theorem eq_of_sup_twoFrattini (X A : Subgroup G) (hAX : A ≤ X)
    (hcore : X.pCoreIn 2 ≤ A) (hsup : A ⊔ twoFrattini X = X) : A = X := by
  let f := QuotientGroup.mk' (pCore 2 X)
  have hm : (twoFrattiniIn X).map f = frattini (XiQuotient X) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hA : (A.subgroupOf X).map f = ⊤ := by
    apply frattini_nongenerating
    rw [← hm, ← Subgroup.map_sup]
    have hin : A.subgroupOf X ⊔ twoFrattiniIn X = ⊤ := by
      apply map_injective X.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hAX]
      simpa only [twoFrattini, ← MonoidHom.range_eq_map, range_subtype] using hsup
    rw [hin, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hc : pCore 2 X ≤ A.subgroupOf X := by
    intro x hx
    exact hcore (mem_map.mpr ⟨x, hx, rfl⟩)
  have htop : A.subgroupOf X = ⊤ := by
    have he := congrArg (comap f) hA
    simpa only [comap_map_eq, f, QuotientGroup.ker_mk', sup_of_le_left hc,
      comap_top] using he
  have he := congrArg (map X.subtype) htop
  simpa only [map_subgroupOf_eq_of_le hAX, ← MonoidHom.range_eq_map, range_subtype] using he

/-- Nontriviality of X/O₂(X) makes O₂,Φ(X) a proper subgroup of X. -/
theorem not_le_twoFrattini (X : Subgroup G) [Nontrivial (XiQuotient X)] :
    ¬ X ≤ twoFrattini X := by
  intro h
  have he : (pCore 2 X : Subgroup X) = ⊤ := by
    have hcore : X.pCoreIn 2 = X := eq_of_sup_twoFrattini X (X.pCoreIn 2)
      (pCoreIn_le 2 X) le_rfl (by
        rw [sup_of_le_right (twoCore_le_twoFrattini X)]
        exact le_antisymm (twoFrattini_le X) h)
    apply map_injective X.subtype_injective
    simpa only [pCoreIn, ← MonoidHom.range_eq_map, range_subtype] using hcore
  have hs : Subsingleton (XiQuotient X) := by
    change Subsingleton ((X : Type _) ⧸ pCore 2 X)
    rw [he]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton (XiQuotient X) hs

/-- The elementary Thompson subgroup, formed inside R. -/
noncomputable def elementaryThompsonIn (R : Subgroup G) : Subgroup R :=
  ChapterB.thompsonJ ⊤ 0

/-- The first omega subgroup of the center, formed inside R. -/
def omegaCenterIn (R : Subgroup G) : Subgroup R :=
  (omega₁ (center R) (p := 2)).map (center R).subtype

instance elementaryThompsonIn_characteristic (R : Subgroup G) :
    (elementaryThompsonIn R).Characteristic := ChapterB.thompsonJ_characteristic 0

instance omegaCenterIn_characteristic (R : Subgroup G) :
    (omegaCenterIn R).Characteristic := by
  let : (omega₁ (center R) (p := 2)).Characteristic := omega₁_characteristic (center R)
  exact characteristic_of_characteristic_of_characteristic

/-- The two actual characteristic subgroups used on printed p.513. -/
def IsThompsonChoice (R : Subgroup G) (C : Subgroup R) : Prop :=
  C = elementaryThompsonIn R ∨ C = omegaCenterIn R

theorem IsThompsonChoice.characteristic {R : Subgroup G} {C : Subgroup R}
    (h : IsThompsonChoice R C) : C.Characteristic := by
  rcases h with rfl | rfl <;> infer_instance

theorem omegaCenterIn_ne_bot (R : Subgroup G) (hR : IsPGroup 2 R) (hne : R ≠ ⊥) :
    omegaCenterIn R ≠ ⊥ := by
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hne
  let : Nontrivial (center R) := hR.center_nontrivial
  obtain ⟨n, hn, hc⟩ := (hR.to_subgroup (center R)).nontrivial_iff_card.mp inferInstance
  apply omega₁_map_subtype_ne_bot (center R) 2
  rw [hc]
  exact dvd_pow_self 2 (Nat.ne_of_gt hn)

theorem elementaryThompsonIn_ne_bot (R : Subgroup G) (hR : IsPGroup 2 R)
    (hne : R ≠ ⊥) : elementaryThompsonIn R ≠ ⊥ := by
  obtain ⟨A, hA⟩ := Stellmacher.elementaryAbelianMaxSubgroups_nonempty (⊤ : Subgroup R)
  let : IsElementaryAbelian 2 (omega₁ (center R) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative (center R)
  have hω : IsElementaryAbelian 2 (omegaCenterIn R) := IsElementaryAbelian.map _
  have hc := hA.2.2 (omegaCenterIn R) le_top hω
  intro he
  have hAJ : A ≤ elementaryThompsonIn R := by
    rw [elementaryThompsonIn, ChapterB.thompsonJ_zero]
    exact le_sSup hA
  have hAbot : A = ⊥ := bot_unique (he ▸ hAJ)
  rw [hAbot, Subgroup.card_bot] at hc
  exact omegaCenterIn_ne_bot R hR hne (Subgroup.eq_bot_of_card_le _ hc)

theorem IsThompsonChoice.ne_bot {R : Subgroup G} {C : Subgroup R}
    (h : IsThompsonChoice R C) (hR : IsPGroup 2 R) (hne : R ≠ ⊥) : C ≠ ⊥ := by
  rcases h with rfl | rfl
  · exact elementaryThompsonIn_ne_bot R hR hne
  · exact omegaCenterIn_ne_bot R hR hne

open scoped Pointwise

/-- The literal product used in Thompson factorization, with J and Ω₁(Z)
computed inside R and then embedded in G. -/
def ThompsonFactorization (X R : Subgroup G) : Prop :=
  ((X ⊔ R : Subgroup G) : Set G) =
    (((X ⊔ R) ⊓ normalizer ((elementaryThompsonIn R).map R.subtype : Set G) :
      Subgroup G) : Set G) *
    (((X ⊔ R) ⊓ centralizer ((omegaCenterIn R).map R.subtype : Set G) :
      Subgroup G) : Set G)

omit [Finite G] in
/-- The normalizer residual acts on each characteristic radical factor. -/
theorem Y_normalizes_XiP (p q : ℕ) (L T : Subgroup G) :
    normalizerResidual L (radicalCore p L T) ≤ normalizer (XiP q L : Set G) :=
  (normalizerResidual_le _ _).trans
    (L.le_normalizer.trans (normalizer_le_normalizer_XiP q L))

omit [Finite G] in
/-- The source R is contained in the given Sylow two-subgroup of LT. -/
theorem radicalCore_le_sylow (p : ℕ) {L T : Subgroup G}
    (hSyl : IsSylowIn 2 T (L ⊔ T)) : radicalCore p L T ≤ T := by
  obtain ⟨S, hS⟩ := hSyl.restrict (show T ≤ XiP p L ⊔ T from le_sup_right)
    (sup_le_sup_right (XiP_le p L) T)
  exact (pCoreIn_le_sylow _ S).trans hS.le

/-- XR is normal in XT, so the characteristic-two property of XT
passes to XR. This retains the earlier local characteristic-two hypothesis. -/
theorem XiP_join_radicalCore_generalizedFitting (p q : ℕ) {L T : Subgroup G}
    (hSyl : IsSylowIn 2 T (L ⊔ T)) (hT : T ≤ normalizer (L : Set G))
    (hHe : XiP q L ⊔ T ∈ He G) :
    Theory.GroupTheory.generalizedFitting (XiP q L ⊔ radicalCore p L T : Subgroup G) =
      pCore 2 (XiP q L ⊔ radicalCore p L T : Subgroup G) := by
  let X := XiP q L
  let R := radicalCore p L T
  let H := X ⊔ R
  let K := X ⊔ T
  have hHK : H ≤ K := sup_le_sup_left (radicalCore_le_sylow p hSyl) X
  have hTH : T ≤ normalizer (H : Set G) :=
    (le_inf (XiP_invariant q hT) (t_le_normalizer_radicalCore p L T)).trans
      (normalizer_inf_normalizer_le_normalizer_sup X R)
  let : (H.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (le_sup_left.trans H.le_normalizer) hTH)
  apply Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hHK)).mp
    (normal_core_selfCentralizing (mem_He_iff.mp hHe) (H.subgroupOf K))

/-- The only prime divisors of |X_q R| are 2 and q. -/
theorem XiP_join_radicalCore_primeSupport (p q : ℕ) [Fact q.Prime] (hq : Odd q)
    {L T : Subgroup G} (hT : T ≤ normalizer (L : Set G))
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card (XiP q L ⊔ radicalCore p L T : Subgroup G)) :
    r = 2 ∨ r = q := by
  let X := XiP q L
  let R := radicalCore p L T
  obtain ⟨a, ha⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  obtain ⟨b, hb⟩ := (XiP_quotient_isPGroup q hq L).exists_card_eq
  obtain ⟨c, hc⟩ := (radicalCore_isTwoGroup p L T).exists_card_eq
  have hXcard : Nat.card X = 2 ^ a * q ^ b := by
    rw [← (pCore 2 X).card_mul_index, index_eq_card, ha, hb]
  have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes X R
    (radicalCore_normalizes_XiP p q hT)
  have hdprod : r ∣ Nat.card X * Nat.card R := by
    rw [hm]
    exact dvd_mul_of_dvd_right hd _
  rw [hXcard, hc] at hdprod
  rcases hr.dvd_mul.mp hdprod with hdX | hdR
  · rcases hr.dvd_mul.mp hdX with hd2 | hdq
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow hd2)
        |>.resolve_left hr.ne_one)
    · exact Or.inr ((Nat.dvd_prime (Fact.out : q.Prime)).mp (hr.dvd_of_dvd_pow hdq)
        |>.resolve_left hr.ne_one)
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow hdR)
      |>.resolve_left hr.ne_one)

/-- In the source q ≥ 5 case, no section of X_q R can have order divisible by 3. -/
theorem XiP_join_radicalCore_three_coprime (p q : ℕ) [Fact q.Prime]
    (hq : Odd q) (hlarge : 5 ≤ q) {L T : Subgroup G}
    (hT : T ≤ normalizer (L : Set G)) :
    Nat.Coprime 3 (Nat.card (XiP q L ⊔ radicalCore p L T : Subgroup G)) := by
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  rcases XiP_join_radicalCore_primeSupport p q hq hT Nat.prime_three hd with h | h <;> omega

end CFSG.Quasithin.Chapter1.RadicalNormalizers
