module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry.Basic
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry.FourObstruction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.XCensus.Projection
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple


/-!
# Intermediate subgroups in Janko's reflection geometry

For the actual common order-three actor, every subgroup between B = E⟨w⟩
and X = N(F)' is B, B ⊔ F, or X. The actor fixes only the identity on F,
so an invariant intersection containing E ∩ F has order four or sixteen.
The product B ⊔ F has order 192 and index five in X; consequently adjoining
F to an intermediate subgroup gives either B ⊔ F or X. In the order-four
intersection case, the latter possibility has order 240 and is excluded by
the existing order-ten obstruction.

The normalizer of B ⊔ F preserves its unique subgroup EF of order 64.
The normalizer of X preserves F because the image of any normal conjugate
of F in the literal simple A5 quotient is trivial. These structural arguments
discharge the normalizer exclusions without assuming two-core identities.
Applying the trichotomy to X ∩ Xᶻ proves the exact source intersection B for
any supplied reflection. Only the local analysis and element-order spectrum
are needed; the ambient simplicity and order hypotheses are unnecessary here.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 8, Lemma 17, p.17;
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The fixed-point-free common actor restricts the intersection with F to order four or sixteen. -/
public theorem intermediate_inf_F_card (L : LocalAnalysisData D k)
    (w : FusedNineIntersectionActor D k) (U : Subgroup G)
    (hBU : B D k w ≤ U) :
    Nat.card (U ⊓ CaseII.F D k : Subgroup G) = 4 ∨
      Nat.card (U ⊓ CaseII.F D k : Subgroup G) = 16 := by
  let V := U ⊓ CaseII.F D k
  have hwU : w.actor ∈ U :=
    hBU ((show zpowers w.actor ≤ B D k w from le_sup_right) (mem_zpowers w.actor))
  have hn : w.actor ∈ normalizer (V : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨U.le_normalizer hwU, w.normalizes_F⟩
  have hp : IsPGroup 3 (zpowers w.actor) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, w.actor_order]; rfl)
  have hmod := card_modEq_card_inf_centralizer (zpowers w.actor) V hp (zpowers_le.mpr hn)
  have hfix : V ⊓ centralizer (zpowers w.actor : Set G) = ⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    exact F_three_fixed_point_free D k L w.actor w.normalizes_F w.actor_order x hx.1.2
      ((mem_centralizer_iff.mp hx.2) w.actor (mem_zpowers w.actor))
  rw [hfix, card_bot] at hmod
  change Nat.card V % 3 = 1 % 3 at hmod
  have hd : Nat.card V ∣ 16 := (card_dvd_of_le (show V ≤ CaseII.F D k from inf_le_right)).trans
    ((CaseII.F_card D k).dvd)
  have hlo : 4 ≤ Nat.card V := by
    rw [← E_inf_F_card D k]
    exact card_le_of_le (inf_le_inf (le_sup_left.trans hBU) le_rfl)
  have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : 16 ≠ 0)⟩
  rw [show Nat.divisors 16 = {1, 2, 4, 8, 16} from by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  change Nat.card V = 4 ∨ Nat.card V = 16
  omega

/-- The actual product B F has order 192, hence index five in X. -/
public theorem B_sup_F_card (w : FusedNineIntersectionActor D k) :
    Nat.card (B D k w ⊔ CaseII.F D k : Subgroup G) = 192 := by
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (CaseII.F D k) (B D k w) (B_le_normalizer_F D k w)
  rw [inf_comm, B_inf_F, E_inf_F_card, sup_comm, B_card, CaseII.F_card] at h
  omega

private theorem card_eq_of_192_dvd_dvd_960 (n : ℕ) (hlo : 192 ∣ n) (hhi : n ∣ 960) :
    n = 192 ∨ n = 960 := by
  obtain ⟨a, rfl⟩ := hlo
  have ha : a ∣ 5 := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 192)).mp hhi
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp ha with h | h <;> simp [h]

/-- Adjoining F to an intermediate subgroup gives B F or X, by the prime index. -/
public theorem intermediate_sup_F_eq (L : LocalAnalysisData D k)
    (w : FusedNineIntersectionActor D k) (U : Subgroup G)
    (hBU : B D k w ≤ U) (hUX : U ≤ X D k) :
    U ⊔ CaseII.F D k = B D k w ⊔ CaseII.F D k ∨ U ⊔ CaseII.F D k = X D k := by
  have hlo : B D k w ⊔ CaseII.F D k ≤ U ⊔ CaseII.F D k := sup_le_sup_right hBU _
  have hhi : U ⊔ CaseII.F D k ≤ X D k := sup_le hUX (F_le_X D k L w)
  have hcardlo : 192 ∣ Nat.card (U ⊔ CaseII.F D k : Subgroup G) := by
    rw [← B_sup_F_card D k w]
    exact card_dvd_of_le hlo
  have hcardhi : Nat.card (U ⊔ CaseII.F D k : Subgroup G) ∣ 960 := by
    rw [← X_card D k L w]
    exact card_dvd_of_le hhi
  rcases card_eq_of_192_dvd_dvd_960 _ hcardlo hcardhi with hc | hc
  · exact Or.inl (eq_of_le_of_card_ge hlo (by rw [hc, B_sup_F_card])).symm
  · exact Or.inr (eq_of_le_of_card_ge hhi (by rw [hc, X_card D k L w]))

/-- Janko's intermediate-subgroup classification, with the forbidden order-ten branch discharged. -/
public theorem intermediate_subgroup_trichotomy (L : LocalAnalysisData D k)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ))
    (w : FusedNineIntersectionActor D k) (U : Subgroup G)
    (hBU : B D k w ≤ U) (hUX : U ≤ X D k) :
    U = B D k w ∨ U = B D k w ⊔ CaseII.F D k ∨ U = X D k := by
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (CaseII.F D k) U (hUX.trans (X_le_normalizer_F D k))
  rw [inf_comm, sup_comm, CaseII.F_card] at hc
  rcases intermediate_inf_F_card D k L w U hBU with hfour | hsixteen
  · have hUF : U ⊓ CaseII.F D k = CaseII.E D k ⊓ CaseII.F D k :=
      (eq_of_le_of_card_ge (inf_le_inf (le_sup_left.trans hBU) le_rfl)
        (by rw [hfour, E_inf_F_card])).symm
    have hfive := five_not_dvd_intermediate_card D k horders U hUX hUF
    rcases intermediate_sup_F_eq D k L w U hBU hUX with h | h
    · rw [hfour, h, B_sup_F_card] at hc
      exact Or.inl (eq_of_le_of_card_ge hBU (by rw [B_card]; omega)).symm
    · rw [hfour, h, X_card D k L w] at hc
      have hU : Nat.card U = 240 := by omega
      exact (hfive (by rw [hU]; decide)).elim
  · have hFU : CaseII.F D k ≤ U := by
      have he : U ⊓ CaseII.F D k = CaseII.F D k := eq_of_le_of_card_ge inf_le_right
        (by rw [hsixteen, CaseII.F_card])
      exact he.symm.le.trans inf_le_left
    rcases intermediate_sup_F_eq D k L w U hBU hUX with h | h
    · exact Or.inr (Or.inl (by simpa only [sup_eq_left.mpr hFU] using h))
    · exact Or.inr (Or.inr (by simpa only [sup_eq_left.mpr hFU] using h))

/-- The actual product E F has order 64. -/
public theorem E_sup_F_card : Nat.card (CaseII.E D k ⊔ CaseII.F D k : Subgroup G) = 64 := by
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (CaseII.E D k) (CaseII.F D k)
    ((CaseII.F_le_caseIISylow D k).trans (CaseII.caseIISylow_le_normalizer_E D k))
  rw [CaseII.E_card, CaseII.F_card, E_inf_F_card] at h
  omega

private theorem sixtyfour_eq_of_normal_in_192
    (H K J : Subgroup G) (hHK : H ≤ K) (hJK : J ≤ K)
    (hH : Nat.card H = 64) (hK : Nat.card K = 192) (hJ : Nat.card J = 64)
    (hn : K ≤ normalizer (H : Set G)) : J = H := by
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes H J (hJK.trans hn)
  rw [hH, hJ] at hp
  have hd1 : Nat.card (H ⊔ J : Subgroup G) ∣ 192 := hK ▸ card_dvd_of_le (sup_le hHK hJK)
  have hd2 : Nat.card (H ⊔ J : Subgroup G) ∣ 4096 :=
    ⟨Nat.card (H ⊓ J : Subgroup G), by nlinarith [hp]⟩
  have hd64 : Nat.card (H ⊔ J : Subgroup G) ∣ 64 := Nat.dvd_gcd hd1 hd2
  have he : H = H ⊔ J := eq_of_le_of_card_ge le_sup_left
    (by rw [hH]; exact Nat.le_of_dvd (by decide) hd64)
  exact eq_of_le_of_card_ge (le_sup_right.trans he.symm.le) (by rw [hH, hJ])

/-- Every normalizer of B F preserves its unique subgroup E F of order 64. -/
public theorem normalizer_B_sup_F_le_normalizer_E_sup_F (w : FusedNineIntersectionActor D k) :
    normalizer ((B D k w ⊔ CaseII.F D k : Subgroup G) : Set G) ≤
      normalizer ((CaseII.E D k ⊔ CaseII.F D k : Subgroup G) : Set G) := by
  let H := CaseII.E D k ⊔ CaseII.F D k
  let K := B D k w ⊔ CaseII.F D k
  have hHK : H ≤ K := sup_le_sup_right le_sup_left _
  have hn : K ≤ normalizer (H : Set G) := by
    apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
    apply le_inf
    · exact sup_le (B_le_normalizer_E D k w)
        ((CaseII.F_le_caseIISylow D k).trans (CaseII.caseIISylow_le_normalizer_E D k))
    · exact sup_le (B_le_normalizer_F D k w) le_normalizer
  intro z hz
  have hzK := mem_normalizer_iff_map_conj_eq.mp hz
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply sixtyfour_eq_of_normal_in_192 H K (H.map (MulAut.conj z).toMonoidHom) hHK
    ((map_mono hHK).trans_eq hzK) (E_sup_F_card D k) (B_sup_F_card D k w) _ hn
  rw [card_map_of_injective (MulAut.conj z).injective]
  exact E_sup_F_card D k

/-- The source reflection cannot normalize the middle intermediate subgroup B F. -/
public theorem reflection_not_normalizes_B_sup_F (w : FusedNineIntersectionActor D k) (z : G)
    (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzF : z ∉ normalizer (CaseII.F D k : Set G)) :
    z ∉ normalizer ((B D k w ⊔ CaseII.F D k : Subgroup G) : Set G) :=
  fun hz => reflection_not_normalizes_E_sup_F D k z hzE hzF
    (normalizer_B_sup_F_le_normalizer_E_sup_F D k w hz)

/-- A normalizer of X preserves the literal kernel F of its simple A5 quotient. -/
public theorem normalizer_X_le_normalizer_F (L : LocalAnalysisData D k) :
    normalizer (X D k : Set G) ≤ normalizer (CaseII.F D k : Set G) := by
  obtain ⟨w⟩ := exists_intersectionActor D k L
  obtain ⟨π, s, hs, hker⟩ := exists_XSplitProjection D k L
  have hsurj : Function.Surjective π := fun a => ⟨s a, hs a⟩
  intro z hz
  let f := (MulAut.conj z).toMonoidHom
  let H := (CaseII.F D k).map f
  have hzX : (X D k).map f = X D k := mem_normalizer_iff_map_conj_eq.mp hz
  have hHX : H ≤ X D k := (map_mono (F_le_X D k L w)).trans_eq hzX
  have hn : X D k ≤ normalizer (H : Set G) := by
    rw [← hzX]
    exact (map_mono (X_le_normalizer_F D k)).trans ((CaseII.F D k).le_normalizer_map f)
  have hHcard : Nat.card H = 16 := by
    rw [card_map_of_injective (MulAut.conj z).injective, CaseII.F_card]
  let J := H.subgroupOf (X D k)
  have hJcard : Nat.card J = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hHX).toEquiv).trans hHcard
  have hJn : J.Normal := normal_subgroupOf_of_le_normalizer hn
  have hmapn : (J.map π).Normal := hJn.map π hsurj
  have hmapbot : J.map π = ⊥ := by
    rcases hmapn.eq_bot_or_eq_top with h | h
    · exact h
    · have hd := J.card_map_dvd π
      rw [h, card_top, nat_card_alternatingGroup, hJcard] at hd
      norm_num at hd
  have hJker : J ≤ π.ker := by
    intro x hx
    exact mem_bot.mp (hmapbot ▸ mem_map_of_mem π hx)
  have hHF : H ≤ CaseII.F D k := by
    intro x hx
    have hh := hJker (show (⟨x, hHX hx⟩ : X D k) ∈ J from hx)
    rw [hker] at hh
    exact hh
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact eq_of_le_of_card_ge hHF (by
    change Nat.card (CaseII.F D k) ≤ Nat.card H
    rw [hHcard, CaseII.F_card])

/-- The exact intersection in Janko's Lemma 17, for any supplied source reflection. -/
public theorem conjugate_intersection_eq_B (L : LocalAnalysisData D k)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ))
    (w : FusedNineIntersectionActor D k) (z : G) (hz2 : orderOf z = 2)
    (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzQ : z ∈ normalizer (zpowers w.actor : Set G))
    (hzF : z ∉ normalizer (CaseII.F D k : Set G)) :
    X D k ⊓ (X D k).map (MulAut.conj z).toMonoidHom = B D k w := by
  have hn := reflection_normalizes_conjugate_intersection D k z hz2
  rcases intermediate_subgroup_trichotomy D k L horders w
    (X D k ⊓ (X D k).map (MulAut.conj z).toMonoidHom)
    (B_le_conjugate_intersection D k w L z hzE hzQ) inf_le_left with h | h | h
  · exact h
  · rw [h] at hn
    exact (reflection_not_normalizes_B_sup_F D k w z hzE hzF hn).elim
  · rw [h] at hn
    exact (hzF (normalizer_X_le_normalizer_F D k L hn)).elim

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
