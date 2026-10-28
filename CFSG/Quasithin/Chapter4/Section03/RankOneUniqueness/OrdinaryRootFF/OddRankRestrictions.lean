module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.OddRankSource
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootSecondary.Model
public import Theory.GroupTheory.PPrimeCorePGroupQuotient

/-!
# Odd-prime rank restrictions for the ordinary root component

Use the actual root-torus element in the normal split-prime theorem A.3.18.
The outside element excludes the residual and theta equalities. In case (3b),
the source fusion clause conjugates its cubic subgroup to the specified Singer
actor. The actual embedded SL₂ Levi centralizes the original torus. Its perfect
image in the cyclic Singer centralizer is trivial, so its order would divide
the prime-to-three core, contradicting the Levi's actual three-divisor. This
excludes (3b) without assuming a rank-three elementary subgroup.

Every Cartan prime therefore has rank one, except possibly the projective
linear/unitary-three alternative at three. The latter retains the literal
extension, prime-to-three core quotient and residual; its FF exclusion remains
with the ordinary-root classification owner. The proved A.3.18 producer has no
unproduced classification parameter in these applications.

Source: Aschbacher–Smith 4.3.6, printed p.615, and A.3.18, printed pp.51–53.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
open ChapterA.Section03.OddPrime.SourceModels

private theorem split_exclusion {H P : Type*} [Group H] [Finite H] [Group P]
    [Group.IsPerfect P] (K : Subgroup H) [K.Normal]
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤)
    (j : P →* H) (hjK : j.range ≤ K) (hc : ∀ b, Commute (j b) a)
    (hd : 3 ∣ Nat.card j.range) : ¬ SplitDiagonalAlternative (starComponent 3 K) := by
  let q := starMap 3 H
  let C := starComponent 3 K
  have hpa : IsPGroup 3 (zpowers a) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, ha, pow_one])
  have hcore : pPrimeCore 3 H ≤ K := pPrimeCore_le_of_isPGroup_quotient 3 K
    (isPGroup_quotient_of_sup_eq_top K (zpowers a) hpa hgen)
  have hout : q a ∉ C := by
    intro h
    have hh : a ∈ (K.map q).comap q := h
    rw [comap_map_eq] at hh
    have hk : q.ker ≤ K := by simpa only [q, starMap, QuotientGroup.ker_mk'] using hcore
    exact haK ((sup_le le_rfl hk) hh)
  have hqa : orderOf (q a) = 3 := by
    apply orderOf_eq_prime
    · have he : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
      rw [← map_pow, he, map_one]
    · intro he
      exact hout (he ▸ C.one_mem)
  rintro ⟨unitary, r, _, _, x, α, _, _, _, _, _, _, hcyc, _, hfuse⟩
  obtain ⟨l, hl⟩ := hfuse (zpowers (q a)) (by rw [Nat.card_zpowers, hqa])
    (fun h => hout (h (mem_zpowers _)))
  let f : P →* C := (q.comp j).codRestrict C (fun b => mem_map_of_mem q (hjK ⟨b,rfl⟩))
  let g : P →* C := (MulAut.conj l).toMonoidHom.comp f
  let X : Subgroup C := (centralizer ({x} : Set (Star 3 H))).comap C.subtype
  have hg : ∀ b, g b ∈ X := by
    intro b
    apply mem_centralizer_singleton_iff.mpr
    have hx : x ∈ (zpowers (q a)).map (MulAut.conj l.val).toMonoidHom :=
      hl.ge (mem_zpowers x)
    obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    have he := (((hc b).map q).zpow_right k).map (MulAut.conj l.val).toMonoidHom
    change Commute (l.val * q (j b) * l.val⁻¹)
      ((MulAut.conj l.val).toMonoidHom (q a ^ k)) at he
    rw [hxy] at he
    exact he.eq
  let z : P →* X := g.codRestrict X hg
  let : IsCyclic X := hcyc
  let : Group.IsPerfect z.range := Group.IsPerfect.range z
  have hz (b : P) : z b = 1 := by
    exact congrArg Subtype.val (Subsingleton.elim (⟨z b, ⟨b,rfl⟩⟩ : z.range) 1)
  have hkill (b : P) : q (j b) = 1 := by
    have hg1 : g b = 1 := congrArg Subtype.val (hz b)
    have hf1 : f b = 1 := (MulAut.conj l).injective (hg1.trans (map_one _).symm)
    exact congrArg Subtype.val hf1
  have hjcore : j.range ≤ pPrimeCore 3 H := by
    rintro _ ⟨b, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp (hkill b)
  have hnot := pPrimeCore_coprime_card (p := 3) (G := H)
  have he : 3 = 1 := Nat.eq_one_of_dvd_coprimes hnot dvd_rfl
    (hd.trans (card_dvd_of_le hjcore))
  norm_num at he

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

theorem not_splitDiagonal_of_cartan (hn : 1 < n)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hKN : KZ ≤ m.rootNormalizer)
    (a : G) (haY : a ∈ rootTorus m) (ha : orderOf a = 3) (haK : a ∉ KZ)
    (hd : 3 ∣ 2 ^ n - 1) :
    ¬ SplitDiagonalAlternative (starComponent 3 (KZ.subgroupOf (KZ ⊔ zpowers a))) := by
  let E := KZ ⊔ zpowers a
  let K := KZ.subgroupOf E
  have hEN : E ≤ m.rootNormalizer := sup_le hKN
    (zpowers_le.mpr (rootTorus_le_normalizer m haY))
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have ha' : orderOf a' = 3 := (orderOf_injective E.subtype E.subtype_injective a').symm.trans ha
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply map_injective E.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  let j : Matrix.SpecialLinearGroup (Fin 2) m.Field →* E :=
    m.leviEmbedding.codRestrict E (fun b =>
      (le_sup_left : KZ ≤ E) (hJK (m.leviEmbedding_range_le_second hn ⟨b,rfl⟩)))
  let := m.levi_perfect hn
  have hjK : j.range ≤ K := by
    rintro _ ⟨b,rfl⟩
    exact hJK (m.leviEmbedding_range_le_second hn ⟨b,rfl⟩)
  have hc : ∀ b, Commute (j b) a' := by
    intro b
    apply Subtype.ext
    exact m.cartan_centralizes_levi haY (m.leviEmbedding b) ⟨b,rfl⟩
  have hjrange : j.range.map E.subtype = m.leviEmbedding.range := by
    rw [← MonoidHom.range_comp]
    rfl
  have hdj : 3 ∣ Nat.card j.range := by
    rw [← card_map_of_injective E.subtype_injective, hjrange]
    exact m.scalar_prime_dvd_levi hd
  exact split_exclusion K a' ha' haK hgen j hjK hc hdj

theorem exists_cartan_prime_actor (KZ : Subgroup G)
    (hK : KZ ≤ centralizer (m.root : Set G)) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) :
    ∃ a : G, a ∈ rootTorus m ∧ orderOf a = p ∧ a ∉ KZ := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := rootTorus m) p
    (by rwa [rootTorus_card m])
  refine ⟨a, a.property, ?_, ?_⟩
  · simpa only [orderOf_submonoid] using ha
  · intro hk
    have h1 : a = 1 := Subtype.ext (mem_bot.mp
      ((rootTorus_inf_centralizer m).le ⟨a.property, hK hk⟩))
    rw [h1, orderOf_one] at ha
    exact hp.ne_one ha.symm

theorem projective_alternative_of_high_rank
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ rootTorus m ∧ orderOf a = p ∧ a ∉ KZ ∧
      ProjectiveAlternative p (KZ.subgroupOf (KZ ⊔ zpowers a)) := by
  obtain ⟨a, haY, ha, haK⟩ := exists_cartan_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hKN : KZ ≤ m.rootNormalizer := hK.trans (Subgroup.centralizer_le_normalizer _)
  have hEN : E ≤ m.rootNormalizer := sup_le hKN
    (zpowers_le.mpr (rootTorus_le_normalizer m haY))
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply map_injective E.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have ha' : orderOf a' = p :=
    (orderOf_injective E.subtype E.subtype_injective a').symm.trans ha
  have halt := NormalSplitPrime.normal_split_prime E hsq K inferInstance
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    inferInstance p hp ho hpK a' ha' haK hgen
  rcases (NormalSplitPrime.alternatives_iff a' ha' haK).mp halt with hproj | ⟨hp3, _, hs⟩
  · exact ⟨a, haY, ha, haK, hproj⟩
  · rw [hp3] at hd hs
    exact (not_splitDiagonal_of_cartan m hn KZ hJK hnormal hKN a haY
      (ha.trans hp3) haK hd hs).elim

theorem primeRank_le_one_of_ne_three
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3) :
    primeRank p KZ ≤ 1 := by
  by_contra! hrank
  obtain ⟨a, _, _, _, hproj⟩ := projective_alternative_of_high_rank m hn h KZ hK hJK
    hcomp hquasi hnormal p hp ho hd hrank
  exact hp3 hproj.1

theorem one_le_secondary_primeRank (hn : 1 < n)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    (p : ℕ) (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) : 1 ≤ primeRank p KZ := by
  let : Fact p.Prime := ⟨hp⟩
  have hdiv : p ∣ Nat.card KZ := (m.scalar_prime_dvd_levi hd).trans
    (card_dvd_of_le ((m.leviEmbedding_range_le_second hn).trans hJK))
  by_contra! hz
  exact (PrimeRank.eq_zero_iff_not_dvd_card.mp (by omega : primeRank p KZ = 0)) hdiv

theorem primeRank_eq_one_of_ne_three
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3) :
    primeRank p KZ = 1 :=
  le_antisymm (primeRank_le_one_of_ne_three m hn h KZ hK hJK hcomp hquasi hnormal
    p hp ho hd hp3) (one_le_secondary_primeRank m hn KZ hJK p hp hd)

theorem primeRank_eq_one_or_projective
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    primeRank p KZ = 1 ∨
      ∃ a : G, a ∈ rootTorus m ∧ orderOf a = p ∧ a ∉ KZ ∧
        ProjectiveAlternative p (KZ.subgroupOf (KZ ⊔ zpowers a)) := by
  by_cases hr : primeRank p KZ ≤ 1
  · exact Or.inl (le_antisymm hr (one_le_secondary_primeRank m hn KZ hJK p hp hd))
  · exact Or.inr (projective_alternative_of_high_rank m hn h KZ hK hJK hcomp hquasi hnormal
      p hp ho hd (by omega))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
