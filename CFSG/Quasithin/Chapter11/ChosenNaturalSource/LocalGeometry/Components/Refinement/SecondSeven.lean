module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SecondCatalogue
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstSpecialLinear
public import Theory.SpecificGroups.AlternatingSeven.OddConjugacyClasses
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SecondSevenAction
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Alternating-seven exclusions at the second normalizer

The source cubic Cartan factor is absorbed by the relatively normal
containing component. Coprime fixed-point lifting gives a commuting element
of order five in the original L₂, retaining its smaller two-core. In A₇
this would give an element of order fifteen. In the central three-cover it
forces the cubic image into the center. The binary chief-factor degree
argument then makes that cubic trivial on the whole original V₂.

The literal Cartan consumer excludes both rows using its faithful plane
action. The Cartan cardinality and faithfulness, and the natural-plane map,
are preceding flag/model inputs of qt-d-1222-natural-flag-cartan, with final
discharge retained by qt-d-1222-natural-local-geometry. The remaining linear
and odd-radical rows and both triangle orientations stay with
qt-d-1222-natural-relative-components. SecondCartanCatalogue connects the
exclusions to the complete containing-component catalogue.

Source: Aschbacher--Smith 11.0.2--3 and 11.1.2, printed pp.759--765,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open Chapter1.Section02.LocalModels

private theorem seven_not_fifteen (g : alternatingGroup (Fin 7)) : orderOf g ≠ 15 := by
  intro hg
  have ht := alternatingGroup.SevenOddConjugacyClasses.cycleType_of_odd_order g
    (by rw [hg]; decide)
  have ho : (g : Equiv.Perm (Fin 7)).cycleType.lcm = 15 := by
    rw [Equiv.Perm.lcm_cycleType,orderOf_coe,hg]
  rcases ht with h | h | h | h | h <;> rw [h] at ho <;> norm_num at ho

private theorem fixed_five {G : Type*} [Group G] [Finite G] (A E : Subgroup G)
    (hE : IsPGroup 3 E) (hEA : E ≤ Closure.coreQuotientCentralizer A)
    (hcard : 5 ∣ Nat.card (A ⧸ pCore 2 A)) :
    ∃ y : G, y ∈ A ∧ y ∈ centralizer (E : Set G) ∧ orderOf y = 5 := by
  have hcop : ¬ 3 ∣ Nat.card (pCore 2 A) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
    rw [hn]
    exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hEN : E ≤ normalizer (A : Set G) := hEA.trans (map_subtype_le _)
  let t := (QuotientGroup.mk' (pCore 2 A)).comp
    (inclusion (show A ⊓ centralizer (E : Set G) ≤ A from inf_le_left))
  have ht : Function.Surjective t := centralizer_quotient_surjective_of_prime_fixed
    A E (pCore 2 A) hE hEN hcop (fun e he a ha =>
      Closure.coreQuotientCentralizer_commutator (hEA he) ha)
  have hd : 5 ∣ Nat.card (A ⊓ centralizer (E : Set G) : Subgroup G) :=
    hcard.trans (Subgroup.card_dvd_of_surjective t ht)
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' 5 hd
  exact ⟨y,y.property.1,y.property.2,(orderOf_coe y).trans hy⟩

variable {G : Type*} [Group G] [Finite G]

private theorem seven_cubic_mem
    {H K : Subgroup G} (hK : Source.NormalComponentIn H K)
    (hm : IsAlternating (K ⧸ pCore 2 K) 7 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 7)
    (hH : primeRank 3 H ≤ 2) {x : G} (hxH : x ∈ H) (hx : orderOf x = 3) : x ∈ K := by
  let B := K.subgroupOf H
  let e : (B ⧸ pCore 2 B) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1.1) (pCore_map_iso 2 _)
  let : B.Normal := hK.2
  have hx' : orderOf (⟨x,hxH⟩ : H) = 3 := (orderOf_coe _).symm.trans hx
  rcases hm with hm | ⟨hq,hz,⟨a⟩⟩
  · let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv (e.trans hm.some).symm
    exact SevenCComponentTheta.order_three_mem_of_quotient_seven B hK.1.2 (e.trans hm.some) hH hx'
  · let := hq
    let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
    exact SevenCComponentTheta.order_three_mem_of_central_quotient_seven B hK.1.2
      ((QuotientGroup.congr _ _ e (by
        apply le_antisymm
        · rintro _ ⟨z,hz,rfl⟩
          exact ((centerCongr e) ⟨z,hz⟩).property
        · intro z hz
          exact ⟨e.symm z, ((centerCongr e).symm ⟨z,hz⟩).property, e.apply_symm_apply z⟩)).trans a) hH hx'

private theorem cubic_central_of_commuting_five
    {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ center A) ≃* alternatingGroup (Fin 7))
    (hc : Nat.card (center A) = 3)
    (x y : A) (hx : orderOf x = 3) (hy : orderOf y = 5) (hxy : Commute x y) :
    x ∈ center A := by
  let q := QuotientGroup.mk' (center A)
  by_contra hxc
  have hxq : orderOf (q x) = 3 := orderOf_eq_prime
    (by rw [←map_pow,←hx,pow_orderOf_eq_one,map_one])
    (fun hh => hxc ((QuotientGroup.eq_one_iff _).mp hh))
  have hker : IsPGroup 3 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.of_card (n := 1) (by simpa using hc)
  have hyq : orderOf (q y) = 5 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hker y (by rw [hy]; decide)).trans hy
  have ho : orderOf (q x * q y) = 15 := by
    rw [(hxy.map q).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hxq,hyq]; decide),hxq,hyq]
  exact seven_not_fifteen (e (q x * q y)) ((e.orderOf_eq _).trans ho)

variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The ordinary A₇ row contradicts the original cubic quotient-centralizer. -/
theorem second_not_alternating_seven
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {K E : Subgroup G} (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K) (hEN : E ≤ normalizer (f.Vi 1 : Set G))
    (hE : Nat.card E = 3) (hEC : E ≤ Closure.coreQuotientCentralizer (f.Li 1)) :
    ¬ IsAlternating (K ⧸ pCore 2 K) 7 := by
  intro hmodel
  have hn := Embedding.small_finite_parameters hLK S.nonbinary hm (.inl hmodel)
  have hd : 5 ∣ Nat.card (f.Li 1 ⧸ pCore 2 (f.Li 1)) := by
    rw [ChapterC.Section05.NormalizerControl.EmbeddingSelection.binary_card hm,hn]
    decide
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 1) (by simpa using hE)
  obtain ⟨y,hyA,hyC,hy⟩ := fixed_five (f.Li 1) E hEp hEC hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card E by rw [hE])
  have hxG : orderOf (x : G) = 3 := (orderOf_coe x).trans hx
  have hxK := seven_cubic_mem hK (.inl hmodel)
    ((S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 1)).stronglyQuasithin
      3 Nat.prime_three (by decide)) (hEN x.property) hxG
  let q := QuotientGroup.mk' (pCore 2 K)
  let xK : K := ⟨x,hxK⟩
  let yK : K := ⟨y,hLK hyA⟩
  have hxK3 : orderOf xK = 3 := (orderOf_coe xK).symm.trans hxG
  have hyK5 : orderOf yK = 5 := (orderOf_coe yK).symm.trans hy
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hqx : orderOf (q xK) = 3 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk xK (by rw [hxK3]; decide)).trans hxK3
  have hqy : orderOf (q yK) = 5 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk yK (by rw [hyK5]; decide)).trans hyK5
  have hxy : Commute xK yK := Subtype.ext (hyC x x.property)
  have ho : orderOf (q xK * q yK) = 15 := by
    rw [(hxy.map q).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hqx,hqy]; decide),hqx,hqy]
  exact seven_not_fifteen (hmodel.some (q xK * q yK))
    ((hmodel.some.orderOf_eq _).trans ho)

/-- Coprime lifting and the actual A₇ central quotient force every cubic
in the second Cartan factor into the center of the triple-cover quotient. -/
theorem second_seven_cover_cubic_central
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {K E : Subgroup G} (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K) (hEN : E ≤ normalizer (f.Vi 1 : Set G))
    (hE : Nat.card E = 3) (hEC : E ≤ Closure.coreQuotientCentralizer (f.Li 1))
    (hmodel : IsAlternatingCover (K ⧸ pCore 2 K) 7)
    (x : E) (hx : orderOf x = 3) :
    ∃ hxK : (x : G) ∈ K, QuotientGroup.mk' (pCore 2 K) ⟨x,hxK⟩ ∈
      center (K ⧸ pCore 2 K) := by
  have hn := Embedding.small_finite_parameters hLK S.nonbinary hm (.inr (.inl hmodel))
  have hd : 5 ∣ Nat.card (f.Li 1 ⧸ pCore 2 (f.Li 1)) := by
    rw [ChapterC.Section05.NormalizerControl.EmbeddingSelection.binary_card hm,hn]
    decide
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 1) (by simpa using hE)
  obtain ⟨y,hyA,hyC,hy⟩ := fixed_five (f.Li 1) E hEp hEC hd
  have hxG : orderOf (x : G) = 3 := (orderOf_coe x).trans hx
  have hxK := seven_cubic_mem hK (.inr hmodel)
    ((S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 1)).stronglyQuasithin
      3 Nat.prime_three (by decide)) (hEN x.property) hxG
  let q := QuotientGroup.mk' (pCore 2 K)
  let xK : K := ⟨x,hxK⟩
  let yK : K := ⟨y,hLK hyA⟩
  have hxK3 : orderOf xK = 3 := (orderOf_coe xK).symm.trans hxG
  have hyK5 : orderOf yK = 5 := (orderOf_coe yK).symm.trans hy
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hqx : orderOf (q xK) = 3 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk xK (by rw [hxK3]; decide)).trans hxK3
  have hqy : orderOf (q yK) = 5 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk yK (by rw [hyK5]; decide)).trans hyK5
  obtain ⟨hq,⟨z⟩,⟨a⟩⟩ := hmodel
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 := by
    rw [Nat.card_congr z.toEquiv]; norm_num
  exact ⟨hxK,cubic_central_of_commuting_five a hc (q xK) (q yK) hqx hqy
    ((show Commute xK yK from Subtype.ext (hyC x x.property)).map q)⟩

/-- In the triple-cover row the original second Cartan factor fixes all
of V₂, including the retained fixed layer C_V(L). -/
theorem second_seven_cover_cartan_centralizes
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {K E : Subgroup G} (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K) (hEN : E ≤ normalizer (f.Vi 1 : Set G))
    (hE : Nat.card E = 3) (hEC : E ≤ Closure.coreQuotientCentralizer (f.Li 1))
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G))
    (hmodel : IsAlternatingCover (K ⧸ pCore 2 K) 7) :
    E ≤ centralizer (f.Vi 1 : Set G) := by
  have hn := Embedding.small_finite_parameters hLK S.nonbinary hm (.inr (.inl hmodel))
  have hd : Module.finrank (ZMod 2) (Additive (f.Vi 1)) ≤ 6 := by
    have h := second_cover_finrank_le D S f p hp hk
    rw [hn] at h
    exact h
  intro x hx
  by_cases he : x = 1
  · simpa only [he] using (one_mem (centralizer (f.Vi 1 : Set G)))
  let xE : E := ⟨x,hx⟩
  have hx3 : orderOf xE = 3 := by
    have hh : orderOf xE ∣ 3 := hE ▸ orderOf_dvd_natCard xE
    exact ((Nat.dvd_prime Nat.prime_three).mp hh).resolve_left
      (fun h => he (congrArg Subtype.val (orderOf_eq_one_iff.mp h)))
  obtain ⟨hxK,hz⟩ := second_seven_cover_cubic_central D S f hm hK hLK hEN hE hEC hmodel xE hx3
  obtain ⟨hq,⟨z⟩,⟨a⟩⟩ := hmodel
  let := hq
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 := by
    rw [Nat.card_congr z.toEquiv]; norm_num
  let ρ := (flagAction f 1).comp (inclusion hK.1.1)
  have ha : ρ ⟨x,hxK⟩ = 1 := SecondSevenAction.central_cubic_trivial a hc ρ hd ⟨x,hxK⟩
    ((orderOf_coe (⟨x,hxK⟩ : K)).symm.trans ((orderOf_coe xE).trans hx3)) hz
  have hmem : (⟨x,hEN hx⟩ : normalizer (f.Vi 1 : Set G)) ∈ (flagAction f 1).ker := ha
  rw [flagAction_ker] at hmem
  exact hmem

/-- Both ordinary and triple-covered A₇ are excluded by the original
faithful cubic Cartan factor; no action assumption on K is added. -/
theorem second_not_seven_of_cubic
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {K E : Subgroup G} (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K) (hEN : E ≤ normalizer (f.Vi 1 : Set G))
    (hE : Nat.card E = 3) (hEC : E ≤ Closure.coreQuotientCentralizer (f.Li 1))
    (hfaith : E ⊓ centralizer (f.Vi 1 : Set G) = ⊥)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    ¬ (IsAlternating (K ⧸ pCore 2 K) 7 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 7) := by
  rintro (h | h)
  · exact second_not_alternating_seven D S f hm hK hLK hEN hE hEC h
  · have hle := second_seven_cover_cartan_centralizes D S f hm hK hLK hEN hE hEC p hp hk h
    have hb : E = ⊥ := by simpa only [inf_eq_left.mpr hle] using hfaith
    have hc : Nat.card E = 1 := card_eq_one.mpr hb
    omega

/-- The actual Cartan quotient-centralizer at the original second flag
normalizer discharges both alternating-seven rows of 11.1.1. -/
theorem second_not_seven_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K) (hLK : f.Li 1 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) ⊓ centralizer (f.Vi 1 : Set G) = ⊥)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    ¬ (IsAlternating (K ⧸ pCore 2 K) 7 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 7) := by
  intro hmodel
  have hn := Embedding.small_finite_parameters hLK S.nonbinary hm
    (hmodel.elim Or.inl (fun h => Or.inr (Or.inl h)))
  exact second_not_seven_of_cubic D S f hm hK hLK
    (inf_le_left.trans (f.cartan_normalizes hu hX 1))
    (hXcard.trans (by rw [hn]; decide)) inf_le_right hfaith p hp hk hmodel

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
