module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.LocalGeometry
public import Theory.GroupTheory.SolvableThreePartCore
public import Theory.GroupTheory.PCoreImage

/-!
# From the S₃ shadow to a core of the component intersection

Let J be the literal component intersection and let N = O^{3′}(J).
The source identifies its embedded image with Y₊*. Adjoin the actual
component Sylow Q to N. The resulting H embeds in (Y₊S)*, so it is
solvable with primes two and three; the source shadow bounds its three-core
by three. A two-part divisible by four supplies O₂(H) ≠ 1.

The model input says such an H has characteristic two. Its nontrivial
solvable normal subgroup N then has nontrivial two-core. Characteristicity
in N and normality of N in J supply the required normality in all of J.
The final G₂ adapters discharge both model inputs.

Source: Aschbacher–Smith, 15.3.26–28, printed pp.1130–1131.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.G2TwoCore
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

private theorem shadow_data (a : Input d I c) :
    Group.IsSolvable (d.starImage I (d.Yplus ⊔ d.S)) ∧
    (∀ p : ℕ, p.Prime → p ∣ Nat.card (d.starImage I (d.Yplus ⊔ d.S)) →
      p = 2 ∨ p = 3) := by
  let W := d.Yplus ⊔ d.S
  have hWI : W ≤ I := sup_le (a.yplus_le_intersection.trans inf_le_right) a.sylow_le
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  obtain ⟨e⟩ := a.facts.shadow
  let : Group.IsSolvable (W ⧸ pCore 2 W) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let := (pCore_isPGroup (p := 2) (G := W)).isNilpotent
  let : Group.IsSolvable W :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 W)).mpr
      ⟨inferInstance, inferInstance⟩
  let j := subgroupOfEquivOfLe hWI
  let : Group.IsSolvable (W.subgroupOf I) :=
    Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective
  have hs : Group.IsSolvable (d.starImage I W) :=
    Group.isSolvable_of_surjective ((d.starMap I).subgroupMap_surjective (W.subgroupOf I))
  have hd : Nat.card (d.starImage I W) ∣ Nat.card W := by
    have h := (W.subgroupOf I).card_map_dvd (d.starMap I)
    rwa [Nat.card_congr j.toEquiv] at h
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := W)).exists_card_eq
  have hc : Nat.card W = 2 ^ n * 6 := by
    rw [← (pCore 2 W).card_mul_index, hn, index_eq_card, Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  refine ⟨hs, fun p hp hdiv => ?_⟩
  have hm : p ∣ 2 ^ n * 6 := hc ▸ hdiv.trans hd
  rcases hp.dvd_mul.mp hm with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow h))
  · rcases hp.dvd_mul.mp (show p ∣ 2 * 3 from h) with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)

/-- Source assembly from characteristic two of model Sylow overgroups.
Both model premises are discharged in the full and binary-derived adapters. -/
theorem intersection_twoCore_of_sylow_overgroups (a : Input d I c)
    (hfour : ∀ Q : Sylow 2 (d.starImage I c.L), 4 ∣ Nat.card Q)
    (hchar : ∀ (Q : Sylow 2 (d.starImage I c.L))
      (H : Subgroup (d.starImage I c.L)), (Q : Subgroup (d.starImage I c.L)) ≤ H →
      pCore 2 H ≠ ⊥ → centralizer (pCore 2 H : Set H) ≤ pCore 2 H) :
    pCore 2 ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) ≠ ⊥ := by
  let L := d.starImage I c.L
  let P := d.starImage I (d.M ⊓ c.L)
  let J := P.subgroupOf L
  let N := primeToResidual 3 J
  let R := N.map J.subtype
  have hPL : P ≤ L := a.componentIntersectionStar_lt.le
  have hPJ : J.map L.subtype = P := map_subgroupOf_eq_of_le hPL
  have hR : R.map L.subtype = d.starImage I d.Yplus := by
    change ((primeToResidual 3 J).map J.subtype).map L.subtype = _
    rw [map_embedded_primeToResidual_of_hom, hPJ]
    exact a.componentIntersectionStar_residual
  have hRJ : R ≤ J := map_subtype_le _
  have hnJ : J ≤ normalizer (R : Set L) := by
    intro j hj
    apply N.le_normalizer_map J.subtype
    exact ⟨⟨j, hj⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  obtain ⟨Q, hQ⟩ := a.exists_componentSylow
  have hQJ : (Q : Subgroup L) ≤ J := by
    change (Q : Subgroup L) ≤ (d.starImage I (d.M ⊓ c.L)).subgroupOf L
    rw [hQ, a.intersectionStar_eq_inf]
    intro x hx
    exact ⟨x.property, (map_mono (comap_mono
      (le_inf (inf_le_left.trans d.sylow_le) a.sylow_le))) hx⟩
  let H := R ⊔ (Q : Subgroup L)
  have hHJ : H ≤ J := sup_le hRJ hQJ
  have hRH : R ≤ H := le_sup_left
  have hQH : (Q : Subgroup L) ≤ H := le_sup_right
  have hHS : H.map L.subtype ≤ d.starImage I (d.Yplus ⊔ d.S) := by
    rw [show H.map L.subtype = R.map L.subtype ⊔ (Q : Subgroup L).map L.subtype from
      Subgroup.map_sup R (Q : Subgroup L) L.subtype]
    apply sup_le
    · rw [hR]
      exact map_mono (comap_mono le_sup_left)
    · rw [hQ, subgroupOf_map_subtype]
      exact inf_le_left.trans (map_mono (comap_mono le_sup_right))
  obtain ⟨hsS, hpS⟩ := shadow_data a
  let := hsS
  let f : H →* d.starImage I (d.Yplus ⊔ d.S) :=
    (L.subtype.comp H.subtype).codRestrict _ (fun h => hHS (mem_map_of_mem _ h.property))
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : d.starImage I (d.Yplus ⊔ d.S) =>
      (z : d.Star I)) h))
  have hsH : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective hf
  have hpH (p : ℕ) (hp : p.Prime) (hd : p ∣ Nat.card H) : p = 2 ∨ p = 3 :=
    hpS p hp (hd.trans (card_dvd_of_injective f hf))
  have hsmall : Nat.card (pCore 3 H) ≤ 3 := by
    let g : H →* d.Star I := L.subtype.comp H.subtype
    have hg : Function.Injective g := L.subtype_injective.comp H.subtype_injective
    have hle : (pCore 3 H).map g ≤ d.starImage I (d.MI I) := by
      rintro _ ⟨x, _, rfl⟩
      have hx : (x.val : d.Star I) ∈ P := hHJ x.property
      change (x.val : d.Star I) ∈ d.starImage I (d.M ⊓ c.L) at hx
      rw [a.intersectionStar_eq_inf] at hx
      exact hx.2
    have hb := a.star_three_subgroup_card_le_three _ hle (pCore_isPGroup.map g)
    rwa [card_map_of_injective hg] at hb
  have hcoreH : pCore 2 H ≠ ⊥ :=
    Theory.GroupTheory.twoCore_ne_bot_of_solvable_threeCore_le_three hsH hpH hsmall
      ((hfour Q).trans (card_dvd_of_le hQH))
  have hcH := hchar Q H hQH hcoreH
  let NR := R.subgroupOf H
  let : NR.Normal := normal_subgroupOf_of_le_normalizer (hHJ.trans hnJ)
  let := hsH
  have h3J : 3 ∣ Nat.card J := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPL).toEquiv]
    exact a.componentIntersectionStar_three_dvd
  have h3N : 3 ∣ Nat.card N := by
    have hd : 3 ∣ Nat.card N * N.index := N.card_mul_index.symm ▸ h3J
    exact (Nat.prime_three.dvd_mul.mp hd).resolve_right
      ((Nat.prime_three.coprime_iff_not_dvd).mp (primeToResidual_index_coprime 3))
  have hNne : N ≠ ⊥ := by
    intro hb
    rw [hb, card_bot] at h3N
    norm_num at h3N
  have hNRne : NR ≠ ⊥ := by
    intro hb
    have hRb : R = ⊥ := by
      have hm : NR.map H.subtype = R := map_subgroupOf_eq_of_le hRH
      rw [← hm, hb, Subgroup.map_bot]
    exact hNne ((N.map_eq_bot_iff_of_injective J.subtype_injective).mp hRb)
  have hNRcore : pCore 2 NR ≠ ⊥ :=
    Theory.GroupTheory.pCore_ne_bot_of_solvable_normal_of_characteristic 2 hcH NR hNRne
  let e : NR ≃* N := (subgroupOfEquivOfLe hRH).trans
    (equivMapOfInjective N J.subtype J.subtype_injective).symm
  have hNcore : pCore 2 N ≠ ⊥ := by
    rw [← pCore_map_iso 2 e]
    exact fun h => hNRcore (((pCore 2 NR).map_eq_bot_iff_of_injective e.injective).mp h)
  intro hJcore
  have he : (pCore 2 N).map N.subtype = ⊥ := by
    apply le_bot_iff.mp
    have hn : ((pCore 2 N).map N.subtype).Normal := by
      apply normalizer_eq_top_iff.mp
      apply top_unique
      simpa only [normalizer_eq_top] using
        normalizer_le_normalizer_characteristic_image N (pCore 2 N)
    exact (le_sSup ⟨hn, pCore_isPGroup.map N.subtype⟩ :
      (pCore 2 N).map N.subtype ≤ pCore 2 J).trans_eq hJcore
  exact hNcore (((pCore 2 N).map_eq_bot_iff_of_injective N.subtype_injective).mp he)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.G2TwoCore
