module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.Overgroups
public import Theory.Alternating.Aut
public import Theory.SpecificGroups.Alternating.SevenPartitionOvergroups

/-!
# Excluding the alternating-seven component in the rank-one branch

The S₃ shadow makes |Y₊S| equal to six times a power of two. Conjugation
on the relatively normal component, transported through Aut(A₇) = S₇,
therefore puts (Y₊S)* in a proper point or 4+3 partition stabilizer. The
action contains A₇ in its range, so the full stabilizer preimage is proper
and its permutation image contains the stabilizer's elementary nine.

The proper-overgroup theorem bounds the preimage's three-rank by one.
Its Sylow three-subgroups are consequently cyclic, and cyclicity passes
to the actual image. This contradicts the elementary nine. No faithfulness
of conjugation on I* and no general quotient-rank monotonicity are assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the first
paragraph of the proof of 15.3.28, printed p.1131 (PDF p.1148).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics

private noncomputable def sevenAutEquiv :
    Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))

private noncomputable def sevenAction {H : Type*} [Group H]
    (K : Subgroup H) [K.Normal] (e : K ≃* alternatingGroup (Fin 7)) :
    H →* Equiv.Perm (Fin 7) :=
  sevenAutEquiv.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)

private theorem sevenAction_on_component {H : Type*} [Group H]
    (K : Subgroup H) [K.Normal] (e : K ≃* alternatingGroup (Fin 7)) (k : K) :
    sevenAction K e k = e k := by
  apply sevenAutEquiv.injective
  change sevenAutEquiv (sevenAutEquiv.symm _) = MulAut.conjNormal (e k).val
  rw [sevenAutEquiv.apply_symm_apply]
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  change (e (k * e.symm y * k⁻¹)).val = (e k).val * y.val * (e k).val⁻¹
  simp

private theorem sevenAction_range {H : Type*} [Group H]
    (K : Subgroup H) [K.Normal] (e : K ≃* alternatingGroup (Fin 7)) :
    alternatingGroup (Fin 7) ≤ (sevenAction K e).range := by
  intro a ha
  refine ⟨e.symm ⟨a, ha⟩, ?_⟩
  rw [sevenAction_on_component, e.apply_symm_apply]

variable {G : Type*} [Group G]

/-- The actual S₃ shadow determines the order of Y₊S up to a power of two. -/
theorem shadow_join_card [Finite G] (d : LocalData G) {I : Subgroup G}
    (h : RankOneFacts d I) : ∃ n : ℕ, Nat.card (d.Yplus ⊔ d.S : Subgroup G) = 6 * 2 ^ n := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := (d.Yplus ⊔ d.S : Subgroup G)))
  obtain ⟨e⟩ := h.shadow
  refine ⟨n, ?_⟩
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 (d.Yplus ⊔ d.S : Subgroup G)),
    Nat.card_congr e.toEquiv, hn]
  congr 1
  simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

private theorem image_order [Finite G] (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.HplusMinimal) (h : RankOneFacts d I)
    (f : d.Star I →* Equiv.Perm (Fin 7)) :
    ∃ n : ℕ, Nat.card ((d.starImage I (d.Yplus ⊔ d.S)).map f) ∣ 6 * 2 ^ n := by
  obtain ⟨n, hn⟩ := shadow_join_card d h
  refine ⟨n, ?_⟩
  have hd := ((d.starImage I (d.Yplus ⊔ d.S)).card_map_dvd f).trans
    (((d.Yplus ⊔ d.S).subgroupOf I).card_map_dvd (d.starMap I))
  rw [Nat.card_congr (subgroupOfEquivOfLe hI.1.1.2).toEquiv, hn] at hd
  exact hd

private theorem five_seven_not_dvd {n m : ℕ} (hd : m ∣ 6 * 2 ^ n) : ¬ 5 ∣ m ∧ ¬ 7 ∣ m := by
  constructor
  · intro h
    have hh := (Nat.prime_five.dvd_mul).mp (h.trans hd)
    rcases hh with h | h
    · norm_num at h
    · have := Nat.prime_five.dvd_of_dvd_pow h
      norm_num at this
  · intro h
    have hh := (Nat.prime_seven.dvd_mul).mp (h.trans hd)
    rcases hh with h | h
    · norm_num at h
    · have := Nat.prime_seven.dvd_of_dvd_pow h
      norm_num at this

/-- The rank bound remains valid in any permutation image of a proper overgroup. -/
private theorem proper_overgroup_image_rank [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.HplusMinimal)
    (h : RankOneFacts d I) (hr : primeRank 3 d.Yplus = 1)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (f : d.Star I →* Equiv.Perm (Fin 7)) (K : Subgroup (d.Star I))
    (hYK : d.starImage I (d.Yplus ⊔ d.S) ≤ K) (hK : K ≠ ⊤) :
    primeRank 3 (K.map f) ≤ 1 := by
  let Q : Sylow 3 K := Sylow.nonempty.some
  have hQ : IsCyclic Q := Q.isCyclic_of_odd_of_primeRank_le_one (by decide)
    (proper_star_overgroup_three_rank_le_one d hI h hr P hP K hYK hK)
  exact Q.primeRank_le_one_of_surjective hQ (f.subgroupMap K) (f.subgroupMap_surjective K)

/-- The A₇ branch of 15.3.28 is impossible, using only the genuine inherited
rank-one facts, relative component normality, minimality, and the common Sylow witness. -/
theorem component_star_not_alternating_seven [Finite G]
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hI : I ∈ d.HplusMinimal) (h : RankOneFacts d I) (hr : primeRank 3 d.Yplus = 1)
    (hn : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) :
    ¬ Nonempty (d.starImage I c.L ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  let : (c.L.subgroupOf I).Normal := hn
  let : (d.starImage I c.L).Normal :=
    hn.map (d.starMap I) (QuotientGroup.mk'_surjective _)
  let f := sevenAction (d.starImage I c.L) e
  have hAf : alternatingGroup (Fin 7) ≤ f.range := sevenAction_range _ e
  obtain ⟨n, hn⟩ := image_order d hI h f
  obtain ⟨h5, h7⟩ := five_seven_not_dvd hn
  obtain ⟨K, hBK, hAK, hrK⟩ :=
    Theory.SpecificGroups.Alternating.SevenPartitionOvergroups.exists_overgroup _ h5 h7
  have hpre : K.comap f ≠ ⊤ := by
    intro he
    apply hAK
    intro a ha
    obtain ⟨x, rfl⟩ := hAf ha
    exact show x ∈ K.comap f from he ▸ mem_top x
  have hBpre : d.starImage I (d.Yplus ⊔ d.S) ≤ K.comap f :=
    (map_le_iff_le_comap).mp hBK
  have hbound := proper_overgroup_image_rank d hI h hr P hP f (K.comap f) hBpre hpre
  have hle : K ⊓ alternatingGroup (Fin 7) ≤ (K.comap f).map f := by
    intro a ha
    obtain ⟨x, hx⟩ := hAf ha.2
    exact ⟨x, show f x ∈ K from hx.symm ▸ ha.1, hx⟩
  have hlow := hrK.trans (Theory.GroupTheory.primeRank_le_of_injective 3
    (inclusion hle) (inclusion_injective hle))
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
