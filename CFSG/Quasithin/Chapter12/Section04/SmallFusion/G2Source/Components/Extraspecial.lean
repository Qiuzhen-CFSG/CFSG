module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components.Classification
public import Theory.GroupTheory.RankTwoDisjointAction
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.SpecificGroups.PSL2.PrimeCubicRank

/-!
# The extraspecial stabilizer branch of the original G₂ cover

An exponent-three subgroup of order twenty-seven contains an elementary
nine. If its action on the original hyperplane is faithful, this nine is
disjoint from the hyperplane centralizer and normalizes that centralizer.
The three-rank bound in the actual hyperplane normalizer therefore makes
the centralizer three-prime. The Fermat/Mersenne component list has no
three-prime member, excluding every ordinary component.

Source: Aschbacher--Smith, 12.4.8, printed p.815, the extraspecial
stabilizer case; the rank obstruction is A.1.27, printed p.26.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem exponent_three_twentySeven_has_plane
    {Y : Type*} [Group Y] [Finite Y]
    (hc : Nat.card Y = 27) (hpow : ∀ y : Y, y ^ 3 = 1) :
    ∃ E : Subgroup Y, Nat.card E = 3 ^ 2 ∧ IsElementaryAbelian 3 E := by
  have h3 : IsPGroup 3 Y := IsPGroup.of_card (n := 3) (by simpa using hc)
  have hn : ¬ IsCyclic Y := by
    intro hi
    let := hi
    have hd : Nat.card Y ∣ 3 := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow
    norm_num [hc] at hd
  obtain ⟨E,_,he,hE⟩ :=
    IsPGroup.exists_normal_elementary_prime_sq_of_odd_not_isCyclic h3 (by decide) hn
  exact ⟨E,he,hE⟩

/-- The literal hyperplane centralizer is three-prime in the faithful
order-twenty-seven branch; no component or model premise is used here. -/
theorem centralizer_coprime_three_of_faithful_twentySeven
    (U Y : Subgroup G) (hYN : Y ≤ normalizer (U : Set G))
    (hc : Nat.card Y = 27) (hpow : ∀ y : Y, y ^ 3 = 1)
    (hfaith : Y ⊓ centralizer (U : Set G) = ⊥)
    (hr : primeRank 3 (normalizer (U : Set G)) ≤ 2) :
    Nat.Coprime 3 (Nat.card (centralizer (U : Set G))) := by
  let N := normalizer (U : Set G)
  let C := (centralizer (U : Set G)).subgroupOf N
  let : C.Normal := normal_subgroupOf_centralizer_normalizer (U : Set G)
  obtain ⟨E,he,hE⟩ := exponent_three_twentySeven_has_plane hc hpow
  let := hE
  let j : Y →* N := inclusion hYN
  let P : Subgroup N := E.map j
  let : IsElementaryAbelian 3 P := IsElementaryAbelian.map j
  have hP : Nat.card P = 3 ^ 2 := by
    rw [card_map_of_injective (inclusion_injective hYN),he]
  have hd : Disjoint P C := by
    apply disjoint_def.mpr
    intro x hxP hxC
    obtain ⟨y,hy,rfl⟩ := hxP
    have hyC : (y : G) ∈ centralizer (U : Set G) := hxC
    have hy1 : (y : G) = 1 := by
      have hm : (y : G) ∈ Y ⊓ centralizer (U : Set G) := ⟨y.property,hyC⟩
      simpa only [hfaith,mem_bot] using hm
    exact Subtype.ext hy1
  have h := coprime_card_of_normalized_disjoint_plane hr P C hP
    le_normalizer_of_normal hd
  rwa [Nat.card_congr (subgroupOfEquivOfLe
    (centralizer_le_normalizer (U : Set G))).toEquiv] at h

private theorem fermatMersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  rintro rfl
  rcases hp.2 with ⟨k,hk⟩ | ⟨k,hk⟩
  · have hh : 2 ≤ 2^(2^k) := Nat.le_pow (by positivity)
    omega
  · have hk0 : k ≠ 0 := by intro he; simp [he] at hk
    have hh := dvd_pow_self 2 hk0
    rw [← hk] at hh
    norm_num at hh

/-- An actual faithful exponent-three stabilizer of order twenty-seven
excludes ordinary components of the original cover centralizer. -/
theorem LocalData.no_component_of_faithful_twentySeven
    {T : Sylow 2 G} {V U : Subgroup G} (c : LocalData T V U)
    (Y : Subgroup G) (hYN : Y ≤ normalizer (U : Set G))
    (hc : Nat.card Y = 27) (hpow : ∀ y : Y, y ^ 3 = 1)
    (hfaith : Y ⊓ centralizer (U : Set G) = ⊥)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G))) : False := by
  let _ := c.hypothesisE.elementary
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le c.member.1
  have hN : IsSQTK KnownSimple.IsKnownSimple (normalizer (U : Set G)) :=
    c.hypothesisE.simpleQTKE.twoLocal_sqtk
      ⟨U,c.member.2.1,IsElementaryAbelian.isPGroup 2 U,rfl⟩
  have hcop := centralizer_coprime_three_of_faithful_twentySeven U Y hYN hc hpow hfaith
    (hN.stronglyQuasithin 3 Nat.prime_three (by decide))
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 (by rw [hc]; decide)
  have hyG : orderOf (y : G) = 3 := (orderOf_coe y).trans hy
  have hyC : (y : G) ∉ centralizer (U : Set G) := by
    intro hh
    have hy1 : (y : G) = 1 := by
      have hm : (y : G) ∈ Y ⊓ centralizer (U : Set G) := ⟨y.property,hh⟩
      simpa only [hfaith,mem_bot] using hm
    norm_num [hy1] at hyG
  obtain ⟨p,hp,F,_,_,hF,⟨e⟩⟩ :=
    c.component_fermatMersenne hK hyG (hYN y.property) hyC
  exact Nat.prime_three.coprime_iff_not_dvd.mp hcop
    ((Theory.PSL2.prime_model_three_dvd_card hp.1 (fermatMersenne_odd hp) hF e).trans
      (card_dvd_of_le hK.1))

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components
