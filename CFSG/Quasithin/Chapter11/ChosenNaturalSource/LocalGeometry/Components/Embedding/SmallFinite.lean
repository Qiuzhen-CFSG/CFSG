module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.RankOne
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SurvivingParameters

/-!
# Field matching in the small finite carrier rows

For a binary PSL₂ section in A₇ or its central three-cover, the order's
2-part bounds the degree by three. In degree three the smaller two-core
would make sixteen divide the carrier order, so it is trivial. The
resulting actual PSL₂(8) subgroup contradicts two-rank two. For J₁ the
order bound leaves degrees two and three, and 504 does not divide its
order. Hence all three rows force the original field to have order four.

The argument uses the actual image of B inside K/O₂(K), with its
intrinsic quotient marking transported through the restricted two-group
kernel. It does not identify O₂(B) with B intersect O₂(K), or assume that
the smaller component image is quasisimple. Both flag-normalizer and
arbitrary-subspace applications are included. The preceding quotient
models belong to qt-d-1222-natural-flag-cartan, with final discharge in
qt-d-1222-natural-local-geometry. Refinement.SmallFinite gives the
first-normalizer consumer without an exhaustive embedding-list premise.

Source: Aschbacher--Smith A.3.12, A.3.14 and 11.1.1--11.1.2,
printed pp.47--50,761--762, combined manuscript of 1 March 2004.
The existing J₁ carrier and order certificate retain their source license.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem section_parameter_of_small_two_part
    (h16 : ¬ 16 ∣ Nat.card G) (hr : primeRank 2 G ≤ 2)
    (B : Subgroup G) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : n = 2 := by
  have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
  have hp : 2^n ∣ Nat.card G := (dvd_mul_right _ _).trans ((binary_card hm) ▸ hd)
  have hnle : n ≤ 3 := by
    by_contra! h
    exact h16 ((show 16 ∣ 2^n from pow_dvd_pow 2 (by omega : 4 ≤ n)).trans hp)
  have hn23 : n = 2 ∨ n = 3 := by omega
  rcases hn23 with h | rfl
  · exact h
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
  have hk0 : k = 0 := by
    by_contra hk0
    obtain ⟨m,hmul⟩ := (show 2 ∣ 2^k from pow_dvd_pow 2 (by omega : 1 ≤ k))
    apply h16
    apply dvd_trans _ B.card_subgroup_dvd_card
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B),binary_card hm,hk,hmul]
    refine ⟨63*m,?_⟩
    ring
  have hz : pCore 2 B = ⊥ := card_eq_one.mp (by simpa [hk0] using hk)
  let e : (B ⧸ pCore 2 B) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  have hl := binary_rank_lower (hm.of_mulEquiv e.symm)
  have hu := (Theory.GroupTheory.primeRank_le_of_injective 2 B.subtype B.subtype_injective).trans hr
  omega

private theorem small_finite_section_parameter
    (B : Subgroup G) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hmodel : IsAlternating G 7 ∨ IsAlternatingCover G 7 ∨ Nonempty (G ≃* Janko1.Model)) :
    n = 2 := by
  rcases hmodel with h | h | h
  · obtain ⟨e⟩ := h
    apply section_parameter_of_small_two_part _ _ B hn hm
    · rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    · rw [primeRank_equiv 2 e,
        Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_alternating]
  · obtain ⟨_,⟨z⟩,⟨e⟩⟩ := h
    apply section_parameter_of_small_two_part _ _ B hn hm
    · rw [card_eq_card_quotient_mul_card_subgroup (center G),
        Nat.card_congr e.toEquiv,Nat.card_congr z.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    · have hz : primeRank 2 (center G) = 0 :=
        PrimeRank.eq_zero_iff_not_dvd_card.mpr (by rw [Nat.card_congr z.toEquiv]; norm_num)
      have hr := primeRank_le_ker_add (p := 2) (QuotientGroup.mk' (center G))
      rw [QuotientGroup.ker_mk',hz,zero_add,primeRank_equiv 2 e,
        Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_alternating] at hr
      exact hr
  · obtain ⟨e⟩ := h
    have hd : Nat.card (B ⧸ pCore 2 B) ∣ 175560 := by
      rw [← Janko1.card_model,← Nat.card_congr e.toEquiv]
      exact (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
    have hp : 2^n ∣ 175560 := (dvd_mul_right _ _).trans ((binary_card hm) ▸ hd)
    have hnle : n ≤ 3 := by
      by_contra! h
      have h16 : 16 ∣ 175560 := (show 16 ∣ 2^n from pow_dvd_pow 2 (by omega : 4 ≤ n)).trans hp
      norm_num at h16
    have hn23 : n = 2 ∨ n = 3 := by omega
    rcases hn23 with h | h
    · exact h
    · rw [binary_card hm,h] at hd
      norm_num at hd

/-- The three surviving small finite carriers, with the central cover explicit. -/
@[expose] public def SmallFiniteCarrier (A : Type*) [Group A] : Prop :=
  IsAlternating A 7 ∨ IsAlternatingCover A 7 ∨ Nonempty (A ≃* Janko1.Model)

/-- A binary rank-one section inside any of these actual two-core quotient
carriers has precisely field four. No triviality of the smaller two-core
or ambient-normality assumption is required. -/
public theorem small_finite_parameters {B K : Subgroup G} (hBK : B ≤ K)
    {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : SmallFiniteCarrier (K ⧸ pCore 2 K)) : n = 2 := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let D := B.subgroupOf K
  let C := D.map q
  have hk : IsPGroup 2 (q.subgroupMap D).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let d := subgroupOfEquivOfLe hBK
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  let e := (q.subgroupMap D).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective D) hk
  exact small_finite_section_parameter C hn (hsmall.of_mulEquiv (e.symm.trans dq)) hmodel

/-- The actual field-four alternative of 11.1.1 for A₇, 3.A₇ and J₁. -/
public theorem component_alternative_of_small_finite {B K : Subgroup G} (hBK : B ≤ K)
    {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : SmallFiniteCarrier (K ⧸ pCore 2 K)) : ComponentAlternative B K n := by
  have hn2 := small_finite_parameters hBK hn hsmall hmodel
  apply ComponentAlternative.four hn2
  rcases hmodel with h | h | h
  · exact .alternating h
  · exact .alternatingCover h
  · exact .j1 h

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Both source flag normalizers with their literal relative components. -/
public theorem flag_component_alternative_of_small_finite (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (_hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hmodel : SmallFiniteCarrier (K ⧸ pCore 2 K)) :
    ComponentAlternative (f.Li i) K S.field.degree :=
  component_alternative_of_small_finite hLK S.nonbinary hm hmodel

/-- The arbitrary-U source setting retains its original full Sylow condition.
The stronger section argument needs only the already supplied containment. -/
public theorem subspace_component_alternative_of_small_finite
    (U : Subgroup G) (_hU : U ≠ ⊥) (_hUV : U ≤ f.Vi 0)
    (_hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (_hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) (hmodel : SmallFiniteCarrier (K ⧸ pCore 2 K)) :
    ComponentAlternative (f.Li 0) K S.field.degree :=
  component_alternative_of_small_finite hLK S.nonbinary hm hmodel

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
