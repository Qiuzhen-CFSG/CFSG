module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonNormalCentralizers
public import Theory.SpecificGroups.ProjectiveLinearThree
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.SpecificGroups.PSL2.PrimeOuterFixed
public import Theory.SpecificGroups.PSL2.InvolutionCentralizerSolvable
public import Theory.SpecificGroups.Alternating.SmallFixedComponents
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.QuotientFixedSource
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.Source
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoFour
public import Theory.Mathieu.M12.Properties.Order
public import Theory.SpecificGroups.BinaryLinear.InnerInvolutionComponents
public import Theory.Representation.BinaryNaturalDual.FourActors.PermutationCatalogue.Centralizers
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.FixedGeometry
/-!
# Prime fixed-component exclusions for source 2.5.19

The original nonnormal source component is PSL₂(p), with p at least seven.
Its characteristic divides its order. Exact orders exclude small Mathieu and
PSL₃(3) carriers, while the degree-six/seven alternating and HS fixed-component
calculations exclude their actual central quotients. Prime-field PSL₂ actors
have solvable fixed subgroups. In the binary degree-four/five models, inner
fixed groups have no components and outer fixed groups have order48 or720.

The intrinsic arithmetic and actor results also accept explicit prime models,
so the later normal-prime source branch can reuse them. The source consumers
retain the original component and use its literal central-quotient image.
Source: Aschbacher–Smith 2.5.19, printed pp.560–564, and 2.5.21, pp.566–567.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime

theorem prime_pslTwo_not_alternating {p n : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    ¬ Nonempty (PSL(2, ZMod p) ≃* alternatingGroup (Fin n)) := by
  let : Fact p.Prime := ⟨hp⟩
  rintro ⟨e⟩
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
    (F := ZMod p) (by simpa using hp.odd_of_ne_two (by omega))
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod] at hc
  have hsub : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel (by nlinarith)
  rcases hn with rfl | rfl | rfl | rfl
  · rw [nat_card_alternatingGroup] at hc
    norm_num at hc
    have hq : 48 ≤ p ^ 2 - 1 := by nlinarith
    have hh := Nat.mul_le_mul hp7 hq
    omega
  · rw [nat_card_alternatingGroup] at hc
    norm_num at hc
    have hb : p ≤ 9 := by
      by_contra hb
      have hq : 99 ≤ p ^ 2 - 1 := by nlinarith
      have hh := Nat.mul_le_mul (show 10 ≤ p by omega) hq
      omega
    have hcases : p = 7 ∨ p = 8 ∨ p = 9 := by omega
    rcases hcases with rfl | rfl | rfl
    · norm_num at hc
    · norm_num at hp
    · norm_num at hp
  · rw [nat_card_alternatingGroup] at hc
    norm_num at hc
    by_cases hb : p ≤ 17
    · have hq : p ^ 2 - 1 ≤ 288 := by nlinarith
      have hh := Nat.mul_le_mul hb hq
      omega
    · have hq : 323 ≤ p ^ 2 - 1 := by nlinarith
      have hh := Nat.mul_le_mul (show 18 ≤ p by omega) hq
      omega
  · rw [nat_card_alternatingGroup] at hc
    norm_num at hc
    by_cases hb : p ≤ 34
    · have hq : p ^ 2 - 1 ≤ 1155 := by nlinarith
      have hh := Nat.mul_le_mul hb hq
      omega
    · have hq : 1224 ≤ p ^ 2 - 1 := by nlinarith
      have hh := Nat.mul_le_mul (show 35 ≤ p by omega) hq
      omega


/-- The defining odd-field characteristic divides the projective group order. -/
theorem prime_dvd_pslTwo_card {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    p ∣ Nat.card PSL(2,ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
    (F := ZMod p) (by simpa using hp.odd_of_ne_two (by omega))
  rw [Nat.card_zmod] at hc
  have hd : p ∣ Nat.card PSL(2,ZMod p) * 2 := by
    rw [hc]
    exact dvd_mul_right _ _
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact hd
  · have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega

/-- No prime-field PSL₂ with characteristic at least seven embeds in any
of these exact fixed-group orders. -/
theorem prime_pslTwo_no_injective_small_fixed {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {D : Type*} [Group D]
    (hcard : Nat.card D = 48 ∨ Nat.card D = 320 ∨ Nat.card D = 720 ∨
      Nat.card D = 7680 ∨ Nat.card D = 245760)
    (f : PSL(2,ZMod p) →* D) (hf : Function.Injective f) : False := by
  have hd := (prime_dvd_pslTwo_card hp hp7).trans (Subgroup.card_dvd_of_injective f hf)
  rcases hcard with hc | hc | hc | hc | hc
  all_goals
    rw [hc] at hd
    have hfac := Nat.mem_primeFactors.mpr ⟨hp,hd,by omega⟩
  · have hh : Nat.primeFactors 48 = {2,3} := by decide +kernel
    rw [hh] at hfac
    simp only [Finset.mem_insert,Finset.mem_singleton] at hfac
    omega
  · have hh : Nat.primeFactors 320 = {2,5} := by decide +kernel
    rw [hh] at hfac
    simp only [Finset.mem_insert,Finset.mem_singleton] at hfac
    omega
  · have hh : Nat.primeFactors 720 = {2,3,5} := by decide +kernel
    rw [hh] at hfac
    simp only [Finset.mem_insert,Finset.mem_singleton] at hfac
    omega
  · have hh : Nat.primeFactors 7680 = {2,3,5} := by decide +kernel
    rw [hh] at hfac
    simp only [Finset.mem_insert,Finset.mem_singleton] at hfac
    omega
  · have hh : Nat.primeFactors 245760 = {2,3,5} := by decide +kernel
    rw [hh] at hfac
    simp only [Finset.mem_insert,Finset.mem_singleton] at hfac
    omega

/-- A group of order prime to three cannot contain a projective special
linear group of dimension two. -/
theorem pslTwo_no_injective_three_free {F : Type*} [Field F]
    {D : Type*} [Group D] (hcard : ¬ 3 ∣ Nat.card D)
    (f : PSL(2,F) →* D) (hf : Function.Injective f) : False :=
  hcard ((Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F 2 (by decide)).trans
    (Subgroup.card_dvd_of_injective f hf))


open ComponentRefinement ComponentSelection
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem source_not_small_alternating
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hnK : ¬ (K.subgroupOf H).Normal)
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    ¬ Nonempty (K ≃* alternatingGroup (Fin n)) := by
  obtain ⟨p,hp,hp7,⟨e⟩⟩ :=
    MathieuSourceSetup.nonnormal_component_prime_model c hG hempty hgen hb hnK
  rintro ⟨f⟩
  exact prime_pslTwo_not_alternating hp.1 hp7 hn ⟨e.symm.trans f⟩

private theorem fixed_component_in {D : Type*} [Group D] (a : MulAut D)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) :
    IsComponentIn (B.map a.fixedSubgroup.subtype) a.fixedSubgroup := by
  refine ⟨map_subtype_le _, ?_⟩
  have he : (B.map a.fixedSubgroup.subtype).subgroupOf a.fixedSubgroup = B :=
    comap_map_eq_self_of_injective a.fixedSubgroup.subtype_injective _
  rwa [he]

/-- The direct degree-six and degree-seven catalogue models have no
involution-fixed prime component of characteristic at least seven. -/
theorem alternating_model_fixed_no_prime_component
    {E : Type*} [Group E] {n p : ℕ} (hn : n = 6 ∨ n = 7)
    (e : E ≃* alternatingGroup (Fin n)) (hp : p.Prime) (hp7 : 7 ≤ p)
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : PSL(2,ZMod p) ≃* B) : False := by
  let U := B.map a.fixedSubgroup.subtype
  have hU : IsComponentIn U a.fixedSubgroup := fixed_component_in a B hB
  rcases hn with rfl | rfl
  · exact alternatingGroup.SmallFixedComponents.six_model_no_component e a ha U hU
  · obtain ⟨f⟩ := alternatingGroup.SmallFixedComponents.seven_component_equiv e a ha U hU
    exact prime_pslTwo_not_alternating hp hp7 (Or.inl rfl)
      ⟨(eB.trans (B.equivMapOfInjective a.fixedSubgroup.subtype
        a.fixedSubgroup.subtype_injective)).trans f⟩

theorem source_alternating_quotient_exclusion
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hnK : ¬ (K.subgroupOf H).Normal)
    {E : Type*} [Group E] [Group.IsPerfect E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : (E ⧸ center E) ≃* alternatingGroup (Fin n)) : False := by
  obtain ⟨hc,haq,hD,⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eKB
  let b := quotientAut (center E) a
  let D := B.map (MulAut.fixedSubgroupMap a b (QuotientGroup.mk' (center E)) hc)
  let U := D.map b.fixedSubgroup.subtype
  have hU : IsComponentIn U b.fixedSubgroup := fixed_component_in b D hD
  rcases hn with rfl | rfl
  · exact alternatingGroup.SmallFixedComponents.six_model_no_component e b haq U hU
  · obtain ⟨f⟩ := alternatingGroup.SmallFixedComponents.seven_component_equiv e b haq U hU
    exact source_not_small_alternating c hG hempty hgen hb hnK (Or.inl rfl)
      ⟨eD.trans ((D.equivMapOfInjective b.fixedSubgroup.subtype
        b.fixedSubgroup.subtype_injective).trans f)⟩

theorem source_hs_quotient_exclusion
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hnK : ¬ (K.subgroupOf H).Normal)
    {E : Type*} [Group E] [IsQuasisimple E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B) (e : (E ⧸ center E) ≃* _root_.Sporadic.LeechRelated.HS.Carrier) : False := by
  let : IsSimpleGroup (E ⧸ center E) := IsQuasisimple.simple
  let : IsSimpleGroup _root_.Sporadic.LeechRelated.HS.Carrier := e.symm.isSimpleGroup
  let : Group.IsPerfect _root_.Sporadic.LeechRelated.HS.Carrier :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨hc,haq,hD,⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eKB
  let b := quotientAut (center E) a
  let D := B.map (MulAut.fixedSubgroupMap a b (QuotientGroup.mk' (center E)) hc)
  let u := MulAut.congr e b
  let f := MulAut.fixedSubgroupCongr e b
  let C := D.map f.toMonoidHom
  have hC : IsComponent u.fixedSubgroup C := hD.map_equiv f
  have hu : orderOf u = 2 := ((MulAut.congr e).orderOf_eq b).trans haq
  let eKC : K ≃* C := eD.trans (f.subgroupMap D)
  by_cases hi : ∃ g, u = MulAut.conj g
  · obtain ⟨v⟩ := Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.inner_component_equiv u hu hi C hC
    exact source_not_small_alternating c hG hempty hgen hb hnK (Or.inr (Or.inl rfl))
      ⟨eKC.trans v⟩
  · obtain ⟨v⟩ := Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.outer_component_equiv u hu hi C hC
    exact source_not_small_alternating c hG hempty hgen hb hnK (Or.inr (Or.inr (Or.inr rfl)))
      ⟨eKC.trans v⟩


private theorem eleven_thirteen_not_fermat_mersenne {p : ℕ} (hp : p = 11 ∨ p = 13) :
    ¬ IsFermatOrMersennePrime p := by
  intro h
  have hpow (k : ℕ) : 2 ^ k ≠ p - 1 ∧ 2 ^ k ≠ p + 1 := by
    by_cases hk : k < 4
    · interval_cases k <;> rcases hp with rfl | rfl <;> norm_num
    · have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 4 ≤ k by omega)
      norm_num at hh
      rcases hp with rfl | rfl <;> omega
  rcases h.2 with ⟨k,hk⟩ | ⟨k,hk⟩
  · exact (hpow (2 ^ k)).1 (by omega)
  · exact (hpow k).2 hk.symm

/-- Exact orders eliminate the two small Mathieu models and PSL₃(3) as
containing groups for the actual nonnormal source component. -/
theorem fermat_mersenne_pslTwo_no_injective_small_order
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    {D : Type*} [Group D]
    (hcard : Nat.card D = 7920 ∨ Nat.card D = 95040 ∨ Nat.card D = 5616)
    (f : PSL(2,ZMod p) →* D) (hf : Function.Injective f) : False := by
  let : Fact p.Prime := ⟨hp.1⟩
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
    (F := ZMod p) (by simpa using hp.1.odd_of_ne_two (by omega))
  rw [Nat.card_zmod] at hc
  have hpc : p ∣ Nat.card PSL(2,ZMod p) := by
    have hd : p ∣ Nat.card PSL(2,ZMod p) * 2 := by rw [hc]; exact dvd_mul_right _ _
    rcases hp.1.dvd_mul.mp hd with h | h
    · exact h
    · have := Nat.le_of_dvd (by decide : 0 < 2) h
      omega
  have hd : p ∣ Nat.card D := hpc.trans (Subgroup.card_dvd_of_injective f hf)
  have hprime : p = 11 ∨ p = 13 := by
    rcases hcard with hc | hc | hc
    all_goals
      rw [hc] at hd
      have hfac := Nat.mem_primeFactors.mpr ⟨hp.1,hd,by omega⟩
    · have hh : Nat.primeFactors 7920 = {2,3,5,11} := by decide +kernel
      rw [hh] at hfac
      simp only [Finset.mem_insert, Finset.mem_singleton] at hfac
      omega
    · have hh : Nat.primeFactors 95040 = {2,3,5,11} := by decide +kernel
      rw [hh] at hfac
      simp only [Finset.mem_insert, Finset.mem_singleton] at hfac
      omega
    · have hh : Nat.primeFactors 5616 = {2,3,13} := by decide +kernel
      rw [hh] at hfac
      simp only [Finset.mem_insert, Finset.mem_singleton] at hfac
      omega
  exact eleven_thirteen_not_fermat_mersenne hprime hp

theorem source_small_order_no_injective
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hnK : ¬ (K.subgroupOf H).Normal)
    {D : Type*} [Group D]
    (hcard : Nat.card D = 7920 ∨ Nat.card D = 95040 ∨ Nat.card D = 5616)
    (f : K →* D) (hf : Function.Injective f) : False := by
  obtain ⟨p,hp,hp7,⟨e⟩⟩ :=
    MathieuSourceSetup.nonnormal_component_prime_model c hG hempty hgen hb hnK
  exact fermat_mersenne_pslTwo_no_injective_small_order hp hp7 hcard
    (f.comp e.symm.toMonoidHom) (hf.comp e.symm.injective)

/-- The literal central-quotient descent consumes the exact order exclusions,
including perfect covers of each small model. -/
theorem source_small_quotient_order_exclusion
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hnK : ¬ (K.subgroupOf H).Normal)
    {E : Type*} [Group E] [Group.IsPerfect E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B)
    (hcard : Nat.card (E ⧸ center E) = 7920 ∨
      Nat.card (E ⧸ center E) = 95040 ∨ Nat.card (E ⧸ center E) = 5616) : False := by
  obtain ⟨hc,haq,hD,⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eKB
  let b := quotientAut (center E) a
  let D := B.map (MulAut.fixedSubgroupMap a b (QuotientGroup.mk' (center E)) hc)
  exact source_small_order_no_injective c hG hempty hgen hb hnK hcard
    (b.fixedSubgroup.subtype.comp (D.subtype.comp eD.toMonoidHom))
    (b.fixedSubgroup.subtype_injective.comp (D.subtype_injective.comp eD.injective))


/-- Every involution of prime-field PSL₂ has solvable fixed subgroup. The
outer row uses the actual PGL₂ actor and its odd dihedral centralizer. -/
theorem prime_field_fixed_solvable {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (a : MulAut PSL(2,ZMod p)) (ha : orderOf a = 2) :
    Group.IsSolvable a.fixedSubgroup := by
  have hs : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  by_cases hi : a ∈ (MulAut.conj : PSL(2,ZMod p) →* MulAut PSL(2,ZMod p)).range
  · obtain ⟨g,rfl⟩ := hi
    have hg : orderOf g = 2 := (orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot (ZMod p))) g).symm.trans ha
    rw [MulAut.fixedSubgroup_conj]
    apply Theory.PSL2.involution_centralizer_isSolvable
      (show GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) from
        ⟨p,1,Fact.out,(Fact.out : p.Prime).odd_of_ne_two (by omega),by decide,by simp⟩)
    exact ⟨by intro h; simp [h] at hg, by simpa only [hg] using pow_orderOf_eq_one g⟩
  · obtain ⟨n,_,_,⟨e⟩⟩ := Theory.PSL2.prime_outer_fixed_dihedral hp (MulEquiv.refl _) a hs hi
    let := GLS3.Chapter5.dihedralGroup_isSolvable n
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

private theorem no_component_of_solvable {D : Type*} [Group D] [Group.IsSolvable D]
    (B : Subgroup D) (hB : IsComponent D B) : False := by
  let : IsQuasisimple B := hB.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  exact Group.IsPerfect.not_isSolvable B inferInstance

/-- A source odd-prime PSL₂ model admits no fixed component, for every
involutory actor, independently of the actor in the original model catalogue. -/
theorem prime_linear_model_fixed_no_component
    {E : Type*} [Group E] {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (e : E ≃* PSL(2,ZMod p)) (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) : False := by
  let b := MulAut.congr e a
  let : Group.IsSolvable b.fixedSubgroup :=
    prime_field_fixed_solvable hp b (((MulAut.congr e).orderOf_eq a).trans ha)
  let : Group.IsSolvable a.fixedSubgroup := Group.isSolvable_of_isSolvable_injective
    (f := (MulAut.fixedSubgroupCongr e a).toMonoidHom) (MulAut.fixedSubgroupCongr e a).injective
  exact no_component_of_solvable B hB


open BinaryLinear.OuterCyclic

private noncomputable def binaryLinearEquiv {D : Type*} [Group D] {n : ℕ}
    (hn : 0 < n) (hm : ClassicalGroup.IsPSL D n 2) : D ≃* LinearGroup n := Classical.choice <| by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hcard
  exact ⟨(e.trans (Atlas.fieldEquivPSL n (FiniteField.ringEquivOfCardEq hc))).trans
    (projectiveEquivLinear hn)⟩

private noncomputable def fixedEquivOfConjugate {D : Type*} [Group D]
    (a b : MulAut D) (h : IsConj a b) : a.fixedSubgroup ≃* b.fixedSubgroup := Classical.choice <| by
  obtain ⟨c,hc⟩ := isConj_iff.mp h
  have he : MulAut.congr c a = b := by
    have hh : MulAut.congr c a = c * a * c⁻¹ := by ext x; rfl
    exact hh.trans hc
  exact ⟨(MulAut.fixedSubgroupCongr c a).trans
    (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup he))⟩

private theorem binary_centerless {n : ℕ} (hn : 0 < n) :
    center (LinearGroup n) = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  have hh : (slEquivLinear n).symm g ∈ center SL(n,ZMod 2) := by
    apply mem_center_iff.mpr
    intro x
    apply (slEquivLinear n).injective
    simpa only [map_mul,MulEquiv.apply_symm_apply] using
      mem_center_iff.mp hg (slEquivLinear n x)
  rw [binary_center_eq_bot hn,mem_bot] at hh
  exact mem_bot.mpr ((slEquivLinear n).symm.injective (hh.trans (map_one _).symm))

/-- The genuine binary actors in degrees four and five have no fixed prime
component of characteristic at least seven. -/
theorem binary_fixed_no_prime_component {n p : ℕ} (hn : n = 4 ∨ n = 5)
    (hp : p.Prime) (hp7 : 7 ≤ p)
    (a : MulAut (LinearGroup n)) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : PSL(2,ZMod p) ≃* B) : False := by
  by_cases hi : a ∈ MulAut.innerSubgroup (LinearGroup n)
  · obtain ⟨t,rfl⟩ := hi
    have ht : orderOf t = 2 := (orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot (binary_centerless (by omega))) t).symm.trans ha
    exact BinaryLinear.inner_involution_no_component t
      (by simpa only [ht] using pow_orderOf_eq_one t)
      (by intro he; simp [he] at ht) B hB
  · have hex : Nat.card a.fixedSubgroup = 48 ∨ Nat.card a.fixedSubgroup = 720 := by
      rcases hn with rfl | rfl
      · rcases BinaryNaturalDual.FourActors.outer_involution_conjugacy a ha hi with ht | ht
        · let f := (fixedEquivOfConjugate a _ ht).trans
            BinaryNaturalDual.FourActors.PermutationCatalogue.transpositionFixedEquiv
          right
          rw [Nat.card_congr f.toEquiv]
          norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
        · let f := (fixedEquivOfConjugate a _ ht).trans
            BinaryNaturalDual.FourActors.PermutationCatalogue.tripleTranspositionFixedEquiv
          left
          rw [Nat.card_congr f.toEquiv,Nat.card_prod]
          norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
      · obtain ⟨m⟩ := BinaryLinear.SixSylowActors.Five.exists_fixedModel a
          (by simpa only [ha] using pow_orderOf_eq_one a) hi
        right
        rw [Nat.card_congr m.equiv.toEquiv]
        norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    apply prime_pslTwo_no_injective_small_fixed hp hp7 (D := a.fixedSubgroup)
      (hex.imp_right (fun h => Or.inr (Or.inl h)))
      (B.subtype.comp eB.toMonoidHom) (B.subtype_injective.comp eB.injective)

/-- Transport the binary calculation through the actual field-and-group
model, preserving the original fixed component. -/
theorem binary_model_fixed_no_prime_component
    {E : Type*} [Group E] {n p : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL E n 2) (hp : p.Prime) (hp7 : 7 ≤ p)
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : PSL(2,ZMod p) ≃* B) : False := by
  let e := binaryLinearEquiv (by omega : 0 < n) hm
  let f := MulAut.fixedSubgroupCongr e a
  exact binary_fixed_no_prime_component hn hp hp7 (MulAut.congr e a)
    (((MulAut.congr e).orderOf_eq a).trans ha) (B.map f.toMonoidHom) (hB.map_equiv f)
    (eB.trans (f.subgroupMap B))

/-- Literal central-quotient descent removes both binary-four/five catalogue
families for the original nonnormal source component. -/
theorem source_binary_quotient_exclusion
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hnK : ¬ (K.subgroupOf H).Normal)
    {E : Type*} [Group E] [Group.IsPerfect E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (E ⧸ center E) n 2) : False := by
  obtain ⟨p,hp,hp7,⟨eK⟩⟩ :=
    MathieuSourceSetup.nonnormal_component_prime_model c hG hempty hgen hb hnK
  obtain ⟨hc,haq,hD,⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eKB
  let b := quotientAut (center E) a
  let D := B.map (MulAut.fixedSubgroupMap a b (QuotientGroup.mk' (center E)) hc)
  let e := binaryLinearEquiv (by omega : 0 < n) hm
  let f := MulAut.fixedSubgroupCongr e b
  exact binary_fixed_no_prime_component hn hp.1 hp7 (MulAut.congr e b)
    (((MulAut.congr e).orderOf_eq b).trans haq) (D.map f.toMonoidHom) (hD.map_equiv f)
    ((eK.symm.trans eD).trans (f.subgroupMap D))

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
