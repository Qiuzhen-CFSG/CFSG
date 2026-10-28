module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Movement
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.Supercritical
public import Theory.GroupTheory.OddSubgroupLift
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.ElementaryAbelian.Quotient

/-!
# Constructing the small odd subgroup in 13.8.13

A nontrivial two-subgroup of the solvable star quotient moves an odd prime
core. Choose a supercritical subgroup of that core using A.1.21(1).
Characteristic-in-normal transport makes its embedded image normal, and
A.1.21(3), applied to the actual conjugation automorphisms, preserves
nontrivial movement. Odd prime rank passes through the two-core quotient.
The cyclic rank-one argument and A.1.24 give the three small-group shapes.

The small shapes are inherited by nontrivial subgroups, so finite minimal
selection gives a normal moved image with every proper normal subgroup
centralized by Vα*. Schur–Zassenhaus lifts this chosen subgroup to H with exactly its
specified star image. The residual trichotomy excludes containment in M,
and genuine Hz minimality proves H = ⟨P,L₁,T⟩. The lift itself need not be
normal in H; only its star image is normal.

The universal A.1.21 inputs reuse the interfaces in Chapter1.XiEmbedding;
`RankTwoStructure` is precisely the A.1.24 structure implication. They remain
explicit earlier-source parameters, owned by the A.1 development. This
module proves the cyclic prime-order irreducibility branch. Noncyclic
Frattini irreducibility and the restriction p = 3 or 5 remain open.
In particular, irreducibility must not be inferred for an arbitrary whole
supercritical subgroup without justifying that choice.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.1.21 and
A.1.24 on pp.24–25, and the proof of 13.8.13 on pp.950–951.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G]

/-- The precise structure implication of A.1.24 used below. -/
def RankTwoStructure : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Odd p → ∀ (Y : Type u) [Group Y] [Finite Y],
    IsPGroup p Y → omega₁ Y (p := p) = ⊤ → primeRank p Y = 2 →
    Group.nilpotencyClass Y ≤ 2 →
      (IsElementaryAbelian p Y ∧ Nat.card Y = p ^ 2) ∨
      (IsExtraspecial p Y ∧ Nat.card Y = p ^ 3)

/-- The small-group alternatives are transported along the actual isomorphism. -/
theorem smallOddGroup_of_equiv {p : ℕ} {Y W : Type*} [Group Y] [Group W]
    (e : Y ≃* W) (hY : SmallOddGroup p Y) : SmallOddGroup p W := by
  have hc : Nat.card Y = Nat.card W := Nat.card_congr e.toEquiv
  rcases hY with h | ⟨he, h⟩ | ⟨he, h, hx⟩
  · exact Or.inl (hc.symm.trans h)
  · let _ := he
    exact Or.inr (Or.inl ⟨IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective, hc.symm.trans h⟩)
  · refine Or.inr (Or.inr ⟨IsExtraspecial.of_mulEquiv e he, hc.symm.trans h, ?_⟩)
    intro x
    simpa only [map_pow, map_one, e.apply_symm_apply] using congrArg e (hx (e.symm x))

/-- A nontrivial supercritical subgroup in odd rank at most two has one of
exactly the three required structures. Only the rank-two branch uses A.1.24. -/
theorem small_of_supercritical [Finite G] (hA124 : RankTwoStructure.{u})
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hpG : IsPGroup p G)
    (D : Subgroup G) (hD : IsSupercriticalPSubgroup p D)
    (hne : D ≠ ⊥) (hrank : primeRank p D ≤ 2) : SmallOddGroup p D := by
  by_cases hr : primeRank p D ≤ 1
  · have hc : IsCyclic D := by
      apply (hpG.to_subgroup D).isCyclic_of_odd_of_elementary_card_le ho
      intro E he
      let _ := he
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr E
    let _ := hc
    have hd : Nat.card D ∣ p := by
      rw [← IsCyclic.exponent_eq_card]
      exact hD.exponent_dvd_p
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h | h
    · exact (hne (card_eq_one.mp h)).elim
    · exact Or.inl h
  · have hr : primeRank p D = 2 := by omega
    rcases hA124 p ho D (hpG.to_subgroup D) hD.omega₁_eq_top hr
      hD.nilpotencyClass_le_two with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h.1, h.2, hD.pow_eq_one⟩)

/-- Characteristic-in-normal transport, retaining the embedded subgroup. -/
theorem supercritical_image_normal (N : Subgroup G) [N.Normal]
    {p : ℕ} (D : Subgroup N) (hD : IsSupercriticalPSubgroup p D) :
    (D.map N.subtype).Normal := by
  let _ := hD.characteristic
  exact ConjAct.normal_of_characteristic_of_normal

/-- A two-subgroup moving an odd normal group also moves its supercritical
subgroup. The detection input concerns the actual conjugation automorphism. -/
theorem supercritical_image_moved [Finite G]
    (hA121_3 : SupercriticalCoprimeDetection.{u})
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (N A : Subgroup G) [N.Normal] (hpN : IsPGroup p N) (hpA : IsPGroup 2 A)
    (D : Subgroup N) (hD : IsSupercriticalPSubgroup p D)
    (hmoved : ⁅N, A⁆ ≠ ⊥) : ⁅D.map N.subtype, A⁆ ≠ ⊥ := by
  intro hc
  let _ := conjMulDistribMulActionOfLeNormalizer A N le_normalizer_of_normal
  let ρ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  have hcent : A ≤ centralizer (D.map N.subtype : Set G) :=
    le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp hc)
  apply hmoved
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mpr
  intro a ha
  have hid : ρ (⟨a, ha⟩ : A) = 1 := by
    apply hA121_3 p ho N hpN D hD
    · exact (hpA.orderOf_coprime (Nat.coprime_two_left.mpr ho) ⟨a, ha⟩).coprime_dvd_left
        (orderOf_map_dvd ρ _)
    · intro d
      apply Subtype.ext
      change a * (d : G) * a⁻¹ = (d : G)
      have he := (mem_centralizer_iff.mp (hcent ha)) (d : G)
        (mem_map_of_mem N.subtype d.property)
      calc
        a * (d : G) * a⁻¹ = (d : G) * a * a⁻¹ := by rw [he]
        _ = (d : G) := mul_inv_cancel_right _ _
  apply mem_centralizer_iff.mpr
  intro n hn
  have he := congrArg (fun b : MulAut N => ((b ⟨n, hn⟩ : N) : G)) hid
  change a * n * a⁻¹ = n at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Odd p-rank does not increase in the actual quotient H/O₂(H). -/
theorem star_primeRank_le [Finite G] (H : Subgroup G) {p : ℕ}
    [Fact p.Prime] (ho : Odd p) : primeRank p (Source.Hstar H) ≤ primeRank p H :=
  primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup

/-- A small normal odd group in H* moved by Vα*, chosen in the moved prime
core. No small-group, normality, or movement conclusion is assumed. -/
theorem exists_small_normal_moved_in_star [Finite G]
    (hA121_1 : SupercriticalExistence.{u})
    (hA121_3 : SupercriticalCoprimeDetection.{u}) (hA124 : RankTwoStructure.{u})
    {H Vα : Subgroup G} (hs : Group.IsSolvable H)
    (hr : IsStronglyQuasithin H) (hpA : IsPGroup 2 Vα)
    (hne : Source.starImage H Vα ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ R : Subgroup (Source.Hstar H),
      IsPGroup p R ∧ SmallOddGroup p R ∧ R.Normal ∧
      ⁅R, Source.starImage H Vα⁆ ≠ ⊥ := by
  obtain ⟨p, hp, ho, hm⟩ := exists_odd_core_moved_in_star hs hpA hne
  let _ : Fact p.Prime := ⟨hp⟩
  let N := pCore p (Source.Hstar H)
  obtain ⟨D, hD⟩ := hA121_1 p ho N pCore_isPGroup
  let R := D.map N.subtype
  have hmR : ⁅R, Source.starImage H Vα⁆ ≠ ⊥ :=
    supercritical_image_moved hA121_3 ho N _ pCore_isPGroup
      (starImage_isPGroup H Vα hpA) D hD hm
  have hdne : D ≠ ⊥ := by
    intro he
    apply hmR
    simp only [R, he, Subgroup.map_bot, commutator_bot_left]
  have hrD : primeRank p D ≤ 2 :=
    (primeRank_subgroup_le p D).trans ((primeRank_subgroup_le p N).trans
      ((star_primeRank_le H ho).trans (hr p hp ho)))
  have hsmall := small_of_supercritical hA124 ho pCore_isPGroup D hD hdne hrD
  exact ⟨p, hp, ho, R, (pCore_isPGroup.to_subgroup D).map _,
    smallOddGroup_of_equiv (D.equivMapOfInjective N.subtype N.subtype_injective) hsmall,
    supercritical_image_normal N D hD, hmR⟩

/-- Every odd p-subgroup of H* has an actual p-subgroup lift in H, with
exactly the specified star image. -/
theorem exists_odd_star_lift [Finite G] {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (R : Subgroup (Source.Hstar H)) (hpR : IsPGroup p R) :
    ∃ P : Subgroup G, P ≤ H ∧ IsPGroup p P ∧ Source.starImage H P = R := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hodd : Odd (Nat.card R) := by
    obtain ⟨n, hn⟩ := hpR.exists_card_eq
    rw [hn]
    exact ho.pow
  obtain ⟨D, hm, _, hc, _⟩ :=
    q.exists_odd_subgroup_lift (QuotientGroup.mk'_surjective _) hker R hodd
  have hpD : IsPGroup p D := by
    obtain ⟨n, hn⟩ := hpR.exists_card_eq
    exact IsPGroup.of_card (hc.trans hn)
  refine ⟨D.map H.subtype, map_subtype_le D, hpD.map _, ?_⟩
  change ((D.map H.subtype).comap H.subtype).map q = R
  rw [comap_map_eq_self_of_injective H.subtype_injective]
  exact hm

private theorem smallOddGroup_exponent {p : ℕ} [Fact p.Prime] [Finite G]
    (h : SmallOddGroup p G) : Monoid.exponent G ∣ p := by
  rcases h with h | ⟨he, _⟩ | ⟨_, _, he⟩
  · let _ := isCyclic_of_prime_card h
    rw [IsCyclic.exponent_eq_card, h]
  · exact he.exponent_dvd_p
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr he

/-- Nontrivial subgroups retain the three small odd-group alternatives. -/
theorem smallOddGroup_subgroup [Finite G] {p : ℕ} [Fact p.Prime]
    (h : SmallOddGroup p G) (D : Subgroup G) (hne : D ≠ ⊥) : SmallOddGroup p D := by
  have hexp : Monoid.exponent D ∣ p :=
    (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
      (smallOddGroup_exponent h)
  have hcard : Nat.card G = p ∨ Nat.card G = p ^ 2 ∨ Nat.card G = p ^ 3 := by
    rcases h with h | ⟨_, h⟩ | ⟨_, h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hd : Nat.card D ∣ p ^ 3 := by
    apply (card_subgroup_dvd_card D).trans
    rcases hcard with h | h | h
    · rw [h]
      exact dvd_pow_self p (by decide : 3 ≠ 0)
    · rw [h]
      exact pow_dvd_pow p (by decide : 2 ≤ 3)
    · rw [h]
  obtain ⟨n, hn, hDn⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  have hn0 : n ≠ 0 := by
    intro he
    apply hne
    apply card_eq_one.mp
    simpa only [he, pow_zero] using hDn
  interval_cases n
  · exact (hn0 rfl).elim
  · exact Or.inl (by simpa only [pow_one] using hDn)
  · have he : IsElementaryAbelian p D :=
      { toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hDn
        exponent_dvd_p := hexp }
    exact Or.inr (Or.inl ⟨he, hDn⟩)
  · have he : D = ⊤ := by
      apply eq_top_of_card_eq
      apply le_antisymm (Nat.card_le_card_of_injective D.subtype D.subtype_injective)
      rw [hDn]
      rcases hcard with h | h | h
      · rw [h]
        exact Nat.le_self_pow (by decide : 3 ≠ 0) p
      · rw [h]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by decide : 2 ≤ 3)
      · rw [h]
    rw [he]
    exact smallOddGroup_of_equiv Subgroup.topEquiv.symm h

/-- Choose the small moved normal image minimally. This permits later
refinement of the supercritical choice without assuming irreducibility. -/
theorem exists_small_minimal_normal_moved_in_star [Finite G]
    (hA121_1 : SupercriticalExistence.{u})
    (hA121_3 : SupercriticalCoprimeDetection.{u}) (hA124 : RankTwoStructure.{u})
    {H Vα : Subgroup G} (hs : Group.IsSolvable H)
    (hr : IsStronglyQuasithin H) (hpA : IsPGroup 2 Vα)
    (hne : Source.starImage H Vα ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ R : Subgroup (Source.Hstar H),
      SmallOddGroup p R ∧ Minimal (fun S : Subgroup (Source.Hstar H) =>
        S.Normal ∧ IsPGroup p S ∧ ⁅S, Source.starImage H Vα⁆ ≠ ⊥) R := by
  obtain ⟨p, hp, ho, R, hpR, hsR, hnR, hmR⟩ :=
    exists_small_normal_moved_in_star hA121_1 hA121_3 hA124 hs hr hpA hne
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, hDR, hD⟩ := exists_minimal_le_of_wellFoundedLT
    (fun S : Subgroup (Source.Hstar H) =>
      S.Normal ∧ IsPGroup p S ∧ ⁅S, Source.starImage H Vα⁆ ≠ ⊥) R ⟨hnR, hpR, hmR⟩
  have hneD : D.subgroupOf R ≠ ⊥ := by
    intro hz
    have hm := congrArg (map R.subtype) hz
    rw [map_subgroupOf_eq_of_le hDR, Subgroup.map_bot] at hm
    exact hD.prop.2.2 (by rw [hm, commutator_bot_left])
  exact ⟨p, hp, ho, D, smallOddGroup_of_equiv (subgroupOfEquivOfLe hDR)
    (smallOddGroup_subgroup hsR (D.subgroupOf R) hneD), hD⟩

/-- The cyclic prime-order alternative already has an irreducible Frattini
section, since there is no intermediate subgroup at all. -/
theorem starFrattiniIrreducible_of_prime_card [Finite G] {p : ℕ} [Fact p.Prime]
    {H P L₁ T : Subgroup G} (hcard : Nat.card (Source.starImage H P) = p) :
    starFrattiniIrreducible H P L₁ T := by
  intro N hFN hNP _
  have hd : Nat.card N ∣ p := hcard ▸ card_dvd_of_le hNP
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h | h
  · left
    exact le_antisymm (by rw [card_eq_one.mp h]; exact bot_le) hFN
  · right
    exact eq_of_le_of_card_ge hNP (by rw [hcard, h])


/-- The constructed small odd subgroup before Frattini irreducibility and
prime restriction. This is an output, not a standing-source hypothesis. -/
structure OddConstruction (p : ℕ) (H L₁ T M Vα : Subgroup G) where
  prime : p.Prime
  odd : Odd p
  P : Subgroup G
  P_le : P ≤ H
  P_isPGroup : IsPGroup p P
  Pstar_small : SmallOddGroup p (Source.starImage H P)
  Pstar_normal : (Source.starImage H P).Normal
  moved : ⁅Source.starImage H P, Source.starImage H Vα⁆ ≠ ⊥
  outside : ¬ P ≤ M
  generated : H = P ⊔ (L₁ ⊔ T)
  minimal_moved : Minimal (fun S : Subgroup (Source.Hstar H) =>
    S.Normal ∧ IsPGroup p S ∧ ⁅S, Source.starImage H Vα⁆ ≠ ⊥) (Source.starImage H P)

/-- The actual odd lift has the same small-group shape as its star image. -/
theorem OddConstruction.small {p : ℕ} {H L₁ T M Vα : Subgroup G}
    (c : OddConstruction p H L₁ T M Vα) : SmallOddGroup p c.P :=
  smallOddGroup_of_equiv (oddStarEquiv c.P_isPGroup c.odd c.P_le).symm c.Pstar_small

/-- Every proper normal subgroup of the chosen image centralizes Vα*.
This follows from the constructed minimal choice, not from irreducibility. -/
theorem OddConstruction.proper_normal_centralizes {p : ℕ}
    {H L₁ T M Vα : Subgroup G} (c : OddConstruction p H L₁ T M Vα)
    (S : Subgroup (Source.Hstar H)) (hn : S.Normal)
    (hS : S < Source.starImage H c.P) : ⁅S, Source.starImage H Vα⁆ = ⊥ := by
  have hp : IsPGroup p S :=
    ((starImage_isPGroup H c.P c.P_isPGroup).to_subgroup
      (S.subgroupOf (Source.starImage H c.P))).of_equiv (subgroupOfEquivOfLe hS.le)
  by_contra hm
  exact hS.not_ge (c.minimal_moved.le_of_le ⟨hn, hp, hm⟩ hS.le)

/-- The supercritical construction, odd lift, residual exclusion, and
minimal-generation steps of the first paragraph of 13.8.13. -/
theorem exists_oddConstruction [Finite G]
    (hA121_1 : SupercriticalExistence.{u})
    (hA121_3 : SupercriticalCoprimeDetection.{u}) (hA124 : RankTwoStructure.{u})
    {H Z L L₁ L₁plus T G₁ M Vα : Subgroup G}
    (hs : Group.IsSolvable H) (hr : IsStronglyQuasithin H)
    (hpA : IsPGroup 2 Vα) (hne : Source.starImage H Vα ≠ ⊥)
    (hZ : Z ≠ ⊥) (hpZ : IsPGroup 2 Z) (hZLT : Z ≤ L₁ ⊔ T)
    (hGZ : G₁ ≤ normalizer (Z : Set G))
    (hH : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hVα : Vα ≤ (L₁ ⊔ T).pCoreIn 2)
    (hres : ResidualAlternative L L₁ L₁plus (residualInM H M))
    (hplus : L₁plus ≤ L₁) :
    ∃ p : ℕ, Nonempty (OddConstruction p H L₁ T M Vα) := by
  obtain ⟨p, hp, ho, R, hsmall, hmin⟩ :=
    exists_small_minimal_normal_moved_in_star hA121_1 hA121_3 hA124 hs hr hpA hne
  obtain ⟨hn, hpR, hm⟩ := hmin.prop
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPH, hpP, he⟩ := exists_odd_star_lift ho R hpR
  have hsmallP : SmallOddGroup p (Source.starImage H P) := he ▸ hsmall
  have hnP : (Source.starImage H P).Normal := he ▸ hn
  have hmP : ⁅Source.starImage H P, Source.starImage H Vα⁆ ≠ ⊥ := by
    rw [he]
    exact hm
  have hout := normal_odd_outside hPH hpP ho hnP hmP hVα hres hplus
  have hgen := normal_odd_generated hZ hpZ hZLT hGZ hH hPH hpP ho hnP hmP hVα hres hplus
  have hminP : Minimal (fun S : Subgroup (Source.Hstar H) =>
      S.Normal ∧ IsPGroup p S ∧ ⁅S, Source.starImage H Vα⁆ ≠ ⊥)
      (Source.starImage H P) := he ▸ hmin
  exact ⟨p, ⟨⟨hp, ho, P, hPH, hpP, hsmallP, hnP, hmP, hout, hgen, hminP⟩⟩⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical
end
