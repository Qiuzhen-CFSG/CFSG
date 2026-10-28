module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.LiftTransport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SylowBorel
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.QuotientIntersection

/-!
# The source Borel, its normalization and three-rank

The Sylow intersection in the normal orbit image chooses the actual Borel.
Solvability of L₁T places L₁ in that Borel, and the invariant Sylow intersection
makes T normalize it. Lifting through H → H/O₂(H) and applying the universal
solvable exclusion puts B₀ in M. The two-group kernel preserves three-rank;
the earlier theta identity transfers rank two back to L₁.

The earlier residual identity and universal solvable exclusion remain explicit
inputs. No Borel containment or normalization is assumed by exists_source_borel.
Source: Aschbacher–Smith, 13.7.3(9) and proof of 13.8.16(1), printed pp.936,952.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo
variable {G : Type*} [Group G]

def liftToBorel (H K₀ : Subgroup G) (hK : K₀ ≤ H)
    (Bstar : Subgroup (Source.Hstar H)) : borelLift H K₀ hK Bstar →* Bstar :=
  (orbitStarMap H (borelLift H K₀ hK Bstar) ((borelLift_le H K₀ hK Bstar).trans hK)).codRestrict
    Bstar (by
      intro x
      obtain ⟨hx, hh⟩ := (mem_borelLift_iff H K₀ hK Bstar x).mp x.property
      exact hh)

theorem liftToBorel_surjective (H K₀ : Subgroup G) (hK : K₀ ≤ H)
    (Bstar : Subgroup (Source.Hstar H)) (hB : Bstar ≤ Source.starImage H K₀) :
    Function.Surjective (liftToBorel H K₀ hK Bstar) := by
  intro b
  have hb : (b : Source.Hstar H) ∈ Source.starImage H (borelLift H K₀ hK Bstar) := by
    rw [borelLift_starImage H K₀ hK Bstar hB]
    exact b.property
  obtain ⟨x, hx, he⟩ := hb
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

theorem liftToBorel_ker (H K₀ : Subgroup G) (hK : K₀ ≤ H)
    (Bstar : Subgroup (Source.Hstar H)) :
    (liftToBorel H K₀ hK Bstar).ker = (pCore 2 H).comap
      (inclusion ((borelLift_le H K₀ hK Bstar).trans hK)) := by
  ext x
  change (⟨QuotientGroup.mk' (pCore 2 H) _, _⟩ : Bstar) = 1 ↔ _
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

theorem liftToBorel_ker_two (H K₀ : Subgroup G) (hK : K₀ ≤ H)
    (Bstar : Subgroup (Source.Hstar H)) : IsPGroup 2 (liftToBorel H K₀ hK Bstar).ker := by
  rw [liftToBorel_ker]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)

variable [Finite G]

theorem borelLift_threeRank (H K₀ : Subgroup G) (hK : K₀ ≤ H)
    (Bstar : Subgroup (Source.Hstar H)) (hB : Bstar ≤ Source.starImage H K₀) :
    primeRank 3 (borelLift H K₀ hK Bstar) = primeRank 3 Bstar := by
  let f := liftToBorel H K₀ hK Bstar
  obtain ⟨a, ha⟩ := (liftToBorel_ker_two H K₀ hK Bstar).exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    rw [ha]
    exact (by decide : Nat.Coprime 3 2).pow_right a
  have hk : primeRank 3 f.ker = 0 :=
    PrimeRank.eq_zero_iff_not_dvd_card.mpr ((Nat.prime_three.coprime_iff_not_dvd).mp hcop)
  have hu := Theory.GroupTheory.primeRank_le_ker_add (p := 3) f
  rw [hk, zero_add] at hu
  exact le_antisymm hu (primeRank_le_of_surjective_of_coprime 3 f
    (liftToBorel_surjective H K₀ hK Bstar hB) hcop)

theorem star_sylow_in_normal_orbit (H K₀ T : Subgroup G)
    [(K₀.subgroupOf H).Normal] (hT : Chapter1.IsSylowIn 2 T H) :
    ∃ S : Sylow 2 (Source.starImage H K₀),
      (S : Subgroup (Source.starImage H K₀)).map (Source.starImage H K₀).subtype =
        Source.starImage H T ⊓ Source.starImage H K₀ := by
  obtain ⟨P, hP⟩ := hT
  have hPH : T.subgroupOf H = (P : Subgroup H) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  let q := QuotientGroup.mk' (pCore 2 H)
  let P' := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hPS : (P' : Subgroup (Source.Hstar H)) = Source.starImage H T := by
    rw [Source.starImage, hPH]
    rfl
  let _ : (Source.starImage H K₀).Normal :=
    (inferInstance : (K₀.subgroupOf H).Normal).map q (QuotientGroup.mk'_surjective _)
  obtain ⟨S, hS⟩ := P'.exists_subgroupOf_eq_of_normal (Source.starImage H K₀)
  exact ⟨S, by rw [hS, subgroupOf_map_subtype, hPS]⟩

/-- Theta contains every elementary three-subgroup of its overgroup. -/
theorem threeRank_le_of_contains_threes (X Y : Subgroup G)
    (h : ∀ x ∈ X, orderOf x = 3 → x ∈ Y) : primeRank 3 X ≤ primeRank 3 Y := by
  apply (primeRank_le_iff_elementary_card_le X).mpr
  intro E hE
  let _ := hE
  let D := E.map X.subtype
  let _ : IsElementaryAbelian 3 D := IsElementaryAbelian.map X.subtype
  have hDY : D ≤ Y := by
    rintro _ ⟨x, hx, rfl⟩
    have hp : (x : G) ^ 3 = 1 := by
      have he := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 E) (⟨x, hx⟩ : E)
      exact congrArg (fun z : E => ((z : X) : G)) he
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hp) with ho | ho
    · change (x : G) ∈ Y
      rw [orderOf_eq_one_iff.mp ho]
      exact Y.one_mem
    · exact h x x.property ho
  let _ := IsElementaryAbelian.subgroupOf (p := 3) hDY
  have hc := (primeRank_le_iff_elementary_card_le (p := 3) Y).mp le_rfl (D.subgroupOf Y) inferInstance
  rw [Nat.card_congr (subgroupOfEquivOfLe hDY).toEquiv,
    card_map_of_injective X.subtype_injective] at hc
  exact hc

/-- The source's nontrivial two-perfect, two-by-three group has three in its order. -/
theorem marked_three_dvd (L₁ : Subgroup G) (hL : IsPPerfect 2 L₁)
    (hq : IsPGroup 3 (L₁ ⧸ pCore 2 L₁)) (hne : L₁ ≠ ⊥) : 3 ∣ Nat.card L₁ := by
  by_contra hnot
  have hgen := three_generated_of_twoPerfect (pCore 2 L₁) pCore_isPGroup hq hL
  have hle := primeToResidual_le_ker (MonoidHom.id L₁)
    (Nat.prime_three.coprime_iff_not_dvd.mpr hnot)
  rw [hgen, MonoidHom.ker_id] at hle
  apply hne
  apply eq_bot_iff.mpr
  intro x hx
  exact congrArg Subtype.val (mem_bot.mp (hle (mem_top (⟨x, hx⟩ : L₁))))

/-- The constructed lift has three-rank two, and theta transfers this exact
rank to L₁. Evenness comes from its nontrivial three-elements. -/
theorem chosen_borel_even_and_rank {Q : Type*} [Group Q] [Finite Q]
    (H K₀ M L₁ : Subgroup G) (hK : K₀ ≤ H)
    (e : Source.starImage H K₀ ≃* Q × Q) (S : Sylow 2 (Source.starImage H K₀))
    {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (hL : IsPPerfect 2 L₁) (hq : IsPGroup 3 (L₁ ⧸ pCore 2 L₁)) (hne : L₁ ≠ ⊥)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (hLB : L₁ ≤ borelLift H K₀ hK (SylowBorel.relativeBorel (Source.starImage H K₀) S))
    (hBM : borelLift H K₀ hK (SylowBorel.relativeBorel (Source.starImage H K₀) S) ≤ M) :
    Even n ∧
      primeRank 3 (borelLift H K₀ hK (SylowBorel.relativeBorel (Source.starImage H K₀) S)) = 2 ∧
      primeRank 3 L₁ = 2 := by
  let Bstar := SylowBorel.relativeBorel (Source.starImage H K₀) S
  let B₀ := borelLift H K₀ hK Bstar
  have hB := SylowBorel.relativeBorel_le (Source.starImage H K₀) S
  have hr := borelLift_threeRank H K₀ hK Bstar hB
  have hle : primeRank 3 L₁ ≤ primeRank 3 B₀ :=
    Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hLB) (inclusion_injective hLB)
  have hpos : primeRank 3 L₁ ≠ 0 := by
    intro hz
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz (marked_three_dvd L₁ hL hq hne)
  have hthree : 3 ∣ Nat.card Bstar := by
    by_contra hh
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
    rw [hr, hz] at hle
    exact hpos (Nat.eq_zero_of_le_zero hle)
  have heven := SylowBorel.even_of_three_dvd (Source.starImage H K₀) e S hn hmodel hthree
  have hrank : primeRank 3 B₀ = 2 := hr.trans
    (SylowBorel.threeRank (Source.starImage H K₀) e S hn hmodel heven)
  have hlower : primeRank 3 B₀ ≤ primeRank 3 L₁ :=
    threeRank_le_of_contains_threes B₀ L₁ (by
      intro x hx ho
      rw [htheta]
      exact Subgroup.subset_closure ⟨⟨hK (borelLift_le H K₀ hK Bstar hx), hBM hx⟩, ho⟩)
  exact ⟨heven, hrank, (le_antisymm hle hlower).trans hrank⟩

theorem exists_source_borel
    {Q : Type*} [Group Q] [Finite Q]
    (H K₀ L₁ T G₁ M : Subgroup G) (hK : K₀ ≤ H) (hLH : L₁ ≤ H)
    [(K₀.subgroupOf H).Normal] (hT : Chapter1.IsSylowIn 2 T H)
    (e : Source.starImage H K₀ ≃* Q × Q)
    {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (hL : IsPPerfect 2 L₁) (hq : IsPGroup 3 (L₁ ⧸ pCore 2 L₁))
    (hres : (primeToResidual 3 H).map H.subtype = K₀)
    [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (hKG : K₀ ≤ G₁) (hbase : L₁ ⊔ T ≤ G₁)
    (hex : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ → Group.IsSolvable J → J ≤ M) :
    ∃ S : Sylow 2 (Source.starImage H K₀),
      let Bstar := SylowBorel.relativeBorel (Source.starImage H K₀) S
      let B₀ := borelLift H K₀ hK Bstar
      (S : Subgroup (Source.starImage H K₀)).map (Source.starImage H K₀).subtype =
          Source.starImage H T ⊓ Source.starImage H K₀ ∧
      Source.starImage H B₀ = Bstar ∧
      Group.IsSolvable B₀ ∧ L₁ ≤ B₀ ∧ B₀ ≤ M ∧
      L₁ ⊔ T ≤ normalizer (B₀ : Set G) := by
  have hLK := marked_le_orbit H K₀ L₁ hLH hL hq hres
  have hTH : T ≤ H := by
    obtain ⟨P, hP⟩ := hT
    rw [← hP]
    exact map_subtype_le _
  have hAH : L₁ ⊔ T ≤ H := sup_le hLH hTH
  have hnK : L₁ ⊔ T ≤ normalizer (K₀ : Set G) :=
    hAH.trans ((normal_subgroupOf_iff_le_normalizer hK).mp inferInstance)
  let Kstar := Source.starImage H K₀
  let J := Source.starImage H L₁
  let U := Source.starImage H T
  have hJU : Source.starImage H (L₁ ⊔ T) = J ⊔ U := starImage_sup H L₁ T hLH hTH
  let _ : Kstar.Normal := (inferInstance : (K₀.subgroupOf H).Normal).map
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  let _ : Group.IsSolvable ((L₁ ⊔ T).subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hAH).toMonoidHom)
      (subgroupOfEquivOfLe hAH).injective
  let _ : Group.IsSolvable (J ⊔ U : Subgroup (Source.Hstar H)) := by
    rw [← hJU, Source.starImage]
    exact Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _)
  obtain ⟨S, hS⟩ := star_sylow_in_normal_orbit H K₀ T hT
  let Bstar := SylowBorel.relativeBorel Kstar S
  have hB : Bstar ≤ Kstar := SylowBorel.relativeBorel_le Kstar S
  let _ : Group.IsSolvable Bstar := SylowBorel.solvable Kstar e S hn hmodel
  obtain ⟨hJB, hnB⟩ := SylowBorel.contains_and_normalized Kstar J U e S hn hmodel
    (map_mono (subgroupOf_mono H hLK)) le_normalizer_of_normal hS
  have hnBS : Source.starImage H (L₁ ⊔ T) ≤ normalizer (Bstar : Set (Source.Hstar H)) := by
    rw [hJU]
    exact hnB
  refine ⟨S, hS, borelLift_starImage H K₀ hK Bstar hB,
    borelLift_solvable H K₀ hK Bstar, ?_,
    borelLift_le_M_of_star_normalized H K₀ L₁ T G₁ M hK hAH Bstar hnK hnBS hKG hbase hex,
    borelLift_normalized H K₀ (L₁ ⊔ T) hK hAH Bstar hnK hnBS⟩
  intro x hx
  apply (mem_borelLift_iff H K₀ hK Bstar x).mpr
  exact ⟨hLK hx, hJB (mem_map_of_mem (QuotientGroup.mk' (pCore 2 H))
    (show (⟨x, hLH hx⟩ : H) ∈ L₁.subgroupOf H from hx))⟩


omit [Finite G] in
/-- The quotient intersection really is the image of T ∩ K₀: O₂(H) lies in T. -/
theorem starImage_inf_sylow (H K₀ T : Subgroup G)
    (hT : Chapter1.IsSylowIn 2 T H) :
    Source.starImage H (T ⊓ K₀) = Source.starImage H T ⊓ Source.starImage H K₀ := by
  obtain ⟨P, hP⟩ := hT
  have hPH : T.subgroupOf H = (P : Subgroup H) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hk : (QuotientGroup.mk' (pCore 2 H)).ker ≤ T.subgroupOf H := by
    rw [QuotientGroup.ker_mk', hPH]
    exact pCore_isPGroup.le_sylow_of_normal P
  have he : (T ⊓ K₀).subgroupOf H = K₀.subgroupOf H ⊓ T.subgroupOf H := by
    ext x
    exact and_comm
  rw [Source.starImage, he, map_inf_of_ker_le _ _ _ hk]
  exact inf_comm _ _

omit [Finite G] in
/-- Theta is normalized by every element of its defining subgroup. -/
theorem theta_normalized (J : Subgroup G) :
    J ≤ normalizer (closure {x : G | x ∈ J ∧ orderOf x = 3} : Set G) := by
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  apply Subgroup.subset_closure
  refine ⟨J.mul_mem (J.mul_mem hg hx.1) (J.inv_mem hg), ?_⟩
  exact (MulAut.conj g).orderOf_eq x |>.trans hx.2

omit [Finite G] in
/-- The theta identity makes L₁ normal relative to the actual overlap. -/
theorem marked_normal_in_overlap (H M L₁ : Subgroup G)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3}) :
    (L₁.subgroupOf (H ⊓ M)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [htheta]
  exact theta_normalized (H ⊓ M)

/-- An actual cubic quotient above the two-core bounds the three-rank by one. -/
theorem rank_le_one_of_cubic_core_quotient (A : Subgroup G)
    (hcard : Nat.card (A ⧸ pCore 2 A) = 3) : primeRank 3 A ≤ 1 := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : IsCyclic (A ⧸ pCore 2 A) := isCyclic_of_prime_card hcard
  let P : Sylow 3 (A ⧸ pCore 2 A) := Classical.choice inferInstance
  have ht : primeRank 3 (A ⧸ pCore 2 A) ≤ 1 := P.primeRank_le_one_of_isCyclic inferInstance
  have hk : primeRank 3 (QuotientGroup.mk' (pCore 2 A)).ker = 0 := by
    rw [QuotientGroup.ker_mk']
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨a, ha⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
    rw [ha]
    exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hu := Theory.GroupTheory.primeRank_le_ker_add (p := 3) (QuotientGroup.mk' (pCore 2 A))
  rw [hk, zero_add] at hu
  exact hu.trans ht


/-- The source construction with even parameter and both exact three-ranks.
The Sylow placement, Borel containment, and normalization are conclusions. -/
theorem exists_source_borel_even_rank
    {Q : Type*} [Group Q] [Finite Q]
    (H K₀ L₁ T G₁ M : Subgroup G) (hK : K₀ ≤ H) (hLH : L₁ ≤ H)
    [(K₀.subgroupOf H).Normal] (hT : Chapter1.IsSylowIn 2 T H)
    (e : Source.starImage H K₀ ≃* Q × Q)
    {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (hL : IsPPerfect 2 L₁) (hq : IsPGroup 3 (L₁ ⧸ pCore 2 L₁)) (hne : L₁ ≠ ⊥)
    (hres : (primeToResidual 3 H).map H.subtype = K₀)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (hKG : K₀ ≤ G₁) (hbase : L₁ ⊔ T ≤ G₁)
    (hex : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ → Group.IsSolvable J → J ≤ M) :
    ∃ S : Sylow 2 (Source.starImage H K₀),
      let Bstar := SylowBorel.relativeBorel (Source.starImage H K₀) S
      let B₀ := borelLift H K₀ hK Bstar
      (S : Subgroup (Source.starImage H K₀)).map (Source.starImage H K₀).subtype =
          Source.starImage H (T ⊓ K₀) ∧
      Source.starImage H (T ⊓ K₀) ≤ Bstar ∧
      Source.starImage H B₀ = Bstar ∧
      Group.IsSolvable B₀ ∧ L₁ ≤ B₀ ∧ B₀ ≤ M ∧
      L₁ ⊔ T ≤ normalizer (B₀ : Set G) ∧
      Even n ∧ primeRank 3 B₀ = 2 ∧ primeRank 3 L₁ = 2 := by
  obtain ⟨S, hS, him, hsol, hLB, hBM, hnorm⟩ := exists_source_borel
    H K₀ L₁ T G₁ M hK hLH hT e hn hmodel hL hq hres hKG hbase hex
  have hT₀ : Source.starImage H (T ⊓ K₀) ≤
      SylowBorel.relativeBorel (Source.starImage H K₀) S := by
    rw [starImage_inf_sylow H K₀ T hT, ← hS]
    exact SylowBorel.sylow_le _ S
  exact ⟨S, hS.trans (starImage_inf_sylow H K₀ T hT).symm, hT₀, him, hsol, hLB, hBM, hnorm,
    chosen_borel_even_and_rank H K₀ M L₁ hK e S hn hmodel hL hq hne htheta hLB hBM⟩


end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo

end
