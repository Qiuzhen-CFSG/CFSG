module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.PPrimeCore
public import Theory.Mathieu.M22.Properties.Order

/-!
# The order-32 A₆ section in the A.3.12 catalogue

The shape |O₂(B)| = 32 and B/O₂(B) ≅ A₆ forces |B| = 11520.
Orders and normal two-kernel containment then exclude all twenty-two
proper embedding rows. In the last two rows an odd kernel preserves
divisibility by 64, whereas the possible prime-field SL₂ images fail it.

This is a catalogue sieve, conditional on an actual A.3.12 embedding
or conclusion. It does not prove that the source hypotheses produce
that embedding. Source: Aschbacher–Smith A.3.12, pp.47–48, and the
M₂₂-code application in 8.2.13, pp.722–723, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels

namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
open scoped MatrixGroups
variable {G : Type*} [Group G]

private theorem card_cover {n : ℕ} [Nontrivial (Fin n)] (h : IsAlternatingCover G n) :
    Nat.card G = n.factorial / 2 * 3 := by
  obtain ⟨_, ⟨ez⟩, ⟨eq⟩⟩ := h
  rw [card_eq_card_quotient_mul_card_subgroup (center G),
    Nat.card_congr eq.toEquiv, Nat.card_congr ez.toEquiv, nat_card_alternatingGroup]
  simp

private theorem card_linear_three (h : ClassicalGroup.IsPSL G 3 2) : Nat.card G = 168 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact hc

private theorem card_elementary {p r : ℕ} [NeZero p] (h : ElementaryModel p r G) : Nat.card G = p ^ r := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp

private theorem elementary_two {r : ℕ} (h : ElementaryModel 2 r G) : IsPGroup 2 G :=
  IsPGroup.of_card (card_elementary h)

private theorem extraspecial_two {r : ℕ} (h : ExtraspecialModel 2 r G) : IsPGroup 2 G :=
  IsPGroup.of_card h.2

private theorem cyclicCentral_two {r : ℕ} (h : CyclicFourCentralProduct r G) : IsPGroup 2 G := by
  obtain ⟨C, E, ⟨eC⟩, hE, hgen, hcomm, _⟩ := h
  have hC : IsPGroup 2 C := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_congr eC.toEquiv]; norm_num)
  have h := hC.to_sup_of_normal_right' (extraspecial_two hE)
    ((commutator_eq_bot_iff_le_centralizer.mp hcomm).trans (centralizer_le_normalizer _))
  rw [hgen] at h
  exact h.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)

private theorem section_dvd_quotient {m : ℕ} (hc : Nat.card (G ⧸ pCore 2 G) = m)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N) : m ∣ Nat.card (G ⧸ N) := by
  have hle : N ≤ pCore 2 G := le_sSup ⟨inferInstance, hN⟩
  rw [← hc, ← index_eq_card, ← index_eq_card]
  exact index_dvd_of_le hle

private theorem card_sl_two {q : ℕ} (h : IsSL G 2 q) : Nat.card G = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, hF]

private theorem card_psl_two {q : ℕ} (h : ClassicalGroup.IsPSL G 2 q) :
    Nat.card G * Nat.gcd 2 (q - 1) = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, ← hF]
  have hz := Atlas.ExceptionalSupport.card_sl_center (ι := Fin 2) (F := F)
  simp only [Fintype.card_fin] at hz
  rw [← hz, ← card_eq_card_quotient_mul_card_subgroup (center SL(2,F)), Atlas.card_sl_two]

private theorem sixtyFour_dvd_odd_quotient_image (H N : Subgroup G) [N.Normal]
    (hN : Nat.Coprime 2 (Nat.card N)) (hH : 64 ∣ Nat.card H) :
    64 ∣ Nat.card (H.map (QuotientGroup.mk' N)) := by
  let f := (QuotientGroup.mk' N).comp H.subtype
  let i : f.ker →* N := {
    toFun := fun x => ⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : N => z.val) h))
  have hker : Nat.Coprime 64 (Nat.card f.ker) := by
    exact (Nat.Coprime.of_dvd_right (card_dvd_of_injective i hi) hN).pow_left 6
  have hc := f.ker.card_mul_index
  rw [index_ker] at hc
  have hr : f.range = H.map (QuotientGroup.mk' N) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [← hr]
  exact hker.dvd_mul_left.mp (hc.symm ▸ hH)

private theorem oddCore_image_top {X : Type*} [Group X] {B K : Subgroup X} (hBK : B ≤ K)
    (hgen : B ⊔ (pPrimeCore 2 K).map K.subtype = K) :
    (B.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 K)) = ⊤ := by
  have hg : B.subgroupOf K ⊔ pPrimeCore 2 K = ⊤ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hBK, ← MonoidHom.range_eq_map, range_subtype]
    exact hgen
  have hh := congrArg (map (QuotientGroup.mk' (pPrimeCore 2 K))) hg
  simpa only [Subgroup.map_sup, ← QuotientGroup.ker_mk' (pPrimeCore 2 K),
    Subgroup.map_ker_self, sup_bot_eq, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] using hh

private theorem eq_twoCore_of_quotient_card [Finite G] (N : Subgroup G) [N.Normal]
    (hN : IsPGroup 2 N) (hc : Nat.card (G ⧸ N) = Nat.card (G ⧸ pCore 2 G)) :
    N = pCore 2 G := by
  have hle : N ≤ pCore 2 G := le_sSup ⟨inferInstance, hN⟩
  apply eq_of_le_of_card_ge hle
  have h1 := card_eq_card_quotient_mul_card_subgroup N
  have h2 := card_eq_card_quotient_mul_card_subgroup (pCore 2 G)
  rw [hc] at h1
  have hpos := Nat.card_pos (α := G ⧸ pCore 2 G)
  nlinarith

private theorem quotient_card {B : Type*} [Group B]
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) :
    Nat.card (B ⧸ pCore 2 B) = 360 := by
  obtain ⟨e⟩ := hA6
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem card_of_shape {B : Type*} [Group B] [Finite B]
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) :
    Nat.card B = 11520 := by
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B), quotient_card hA6, hcore]

private theorem prime_dvd_card_le_five {p : ℕ} (hp : p.Prime) (h : p ∣ 11520) : p ≤ 5 := by
  have hf : 11520 = 2^8 * 3^2 * 5 := by norm_num
  rw [hf] at h
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · exact (Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_pow h)).trans (by decide)
    · exact (Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_pow h)).trans (by decide)
  · exact Nat.le_of_dvd (by decide) h

private theorem no_sl_prime {B : Type*} [Group B]
    (hc : Nat.card B = 11520) {p : ℕ} (hp : p.Prime) : ¬ IsSL B 2 p := by
  intro h
  have hb := card_sl_two h
  have hd : p ∣ 11520 := by rw [←hc, hb]; exact dvd_mul_right _ _
  have hp5 := prime_dvd_card_le_five hp hd
  rw [hc] at hb
  interval_cases p <;> norm_num at hb

private theorem no_psl_prime {B : Type*} [Group B]
    (hc : Nat.card B = 11520) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL B 2 p := by
  intro h
  have hb := card_psl_two h
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hpg : ¬ p ∣ Nat.gcd 2 (p - 1) := by
    intro hh
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (dvd_trans hh (Nat.gcd_dvd_left _ _)))
  have hpB : p ∣ Nat.card B := (hp.dvd_mul.mp
    (hb.symm ▸ (dvd_mul_right p (p ^ 2 - 1)))).resolve_right hpg
  have hp5 := prime_dvd_card_le_five hp (hc ▸ hpB)
  rw [hc] at hb
  interval_cases p <;> norm_num at hb

private theorem no_odd_extension {B : Type*} [Group B]
    (hc : Nat.card B = 11520) {p : ℕ} (hp : p.Prime) :
    ¬ HasExtension B (ElementaryModel p 2) (fun Z _ => IsSL Z 2 p) := by
  rintro ⟨N, _, hN, hQ⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hb : Nat.card B = (p * (p ^ 2 - 1)) * p ^ 2 := by
    rw [card_eq_card_quotient_mul_card_subgroup N, card_sl_two hQ, card_elementary hN]
  have hpB : p ∣ Nat.card B := by rw [hb]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hp5 := prime_dvd_card_le_five hp (hc ▸ hpB)
  rw [hc] at hb
  interval_cases p <;> norm_num at hb

private theorem no_oddCore_supplement {Q : Type*} [Group Q] [Finite Q]
    {B K : Subgroup Q} (hBK : B ≤ K) (hc : Nat.card B = 11520)
    {p : ℕ} (hp : p.Prime)
    (hgen : B ⊔ (pPrimeCore 2 K).map K.subtype = K)
    (hmodel : IsSL (K ⧸ pPrimeCore 2 K) 2 p) : False := by
  have hH : Nat.card (B.subgroupOf K) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv
  have ht := oddCore_image_top hBK hgen
  have hcard := card_sl_two hmodel
  have hpB : p ∣ Nat.card B := by
    rw [← hH]
    have hh := card_map_dvd (H := B.subgroupOf K) (QuotientGroup.mk' (pPrimeCore 2 K))
    rw [ht, card_top, hcard] at hh
    exact dvd_trans (dvd_mul_right _ _) hh
  have hp5 := prime_dvd_card_le_five hp (hc ▸ hpB)
  have h64 : 64 ∣ Nat.card (B.subgroupOf K) := by rw [hH, hc]; norm_num
  have hi := sixtyFour_dvd_odd_quotient_image (B.subgroupOf K) (pPrimeCore 2 K)
    pPrimeCore_coprime_card h64
  rw [ht, card_top, hcard] at hi
  interval_cases p <;> first | (solve | norm_num at hp) | (solve | norm_num at hi)

private theorem no_oddCore_image_five {Q : Type*} [Group Q] [Finite Q]
    {B K : Subgroup Q} (hBK : B ≤ K) (hc : Nat.card B = 11520)
    (hmodel : IsSL ((B.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 K))) 2 5) :
    False := by
  have h64 : 64 ∣ Nat.card (B.subgroupOf K) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv, hc]
    norm_num
  have hi := sixtyFour_dvd_odd_quotient_image (B.subgroupOf K) (pPrimeCore 2 K)
    pPrimeCore_coprime_card h64
  rw [card_sl_two hmodel] at hi
  norm_num at hi

private theorem card_alternating {B : Type*} [Group B] {n : ℕ} [Nontrivial (Fin n)]
    (h : IsAlternating B n) : Nat.card B = n.factorial / 2 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]

private theorem card_linear_four {B : Type*} [Group B]
    (h : ClassicalGroup.IsPSL B 4 2) : Nat.card B = 20160 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact hc

private theorem card_linear_three_four {B : Type*} [Group B]
    (h : ClassicalGroup.IsPSL B 3 4) : Nat.card B = 20160 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  omega

private theorem no_binary_rank_one {B : Type*} [Group B] {n : ℕ}
    (hc : Nat.card B = 360) : ¬ ClassicalGroup.IsPSL B 2 (2^n) := by
  intro h
  have he := card_psl_two h
  rw [hc] at he
  have hg : Nat.gcd 2 (2^n - 1) ≤ 2 := Nat.gcd_le_left _ (by decide)
  have hn : n ≤ 3 := by
    by_contra hn
    have hpow : 16 ≤ 2^n := by
      exact (show 16 = 2^4 by norm_num).le.trans
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 4 ≤ n by omega))
    have hs : 255 ≤ (2^n)^2 - 1 :=
      Nat.sub_le_sub_right (Nat.pow_le_pow_left hpow 2) 1
    nlinarith
  interval_cases n <;> norm_num at he

private theorem no_small_model {B : Type*} [Group B] (hc : Nat.card B = 11520)
    (h : IsAlternating B 5 ∨ IsAlternating B 6 ∨ IsAlternatingCover B 6 ∨
      ClassicalGroup.IsPSL B 3 2) : False := by
  rcases h with h | h | h | h
  · have hh := card_alternating h; norm_num [hc] at hh
  · have hh := card_alternating h; norm_num [hc] at hh
  · have hh := card_cover h; norm_num [hc] at hh
  · have hh := card_linear_three h; omega

private theorem no_small_section {B : Type*} [Group B] (hc : Nat.card B = 360)
    (h : IsAlternating B 5 ∨ IsAlternatingCover B 6 ∨
      ClassicalGroup.IsPSL B 4 2 ∨ ClassicalGroup.IsPSL B 3 2) : False := by
  rcases h with h | h | h | h
  · have hh := card_alternating h; norm_num [hc] at hh
  · have hh := card_cover h; norm_num [hc] at hh
  · have hh := card_linear_four h; omega
  · have hh := card_linear_three h; omega

private theorem no_altFive_quotient {B : Type*} [Group B]
    (hc : Nat.card (B ⧸ pCore 2 B) = 360)
    (N : Subgroup B) [N.Normal] (hN : IsPGroup 2 N)
    (hQ : IsAlternating (B ⧸ N) 5) : False := by
  have hd := section_dvd_quotient hc N hN
  rw [card_alternating hQ] at hd
  norm_num at hd

private theorem no_small_quotient {B : Type*} [Group B] [Finite B]
    (hcore : Nat.card (pCore 2 B) = 32)
    (hc : Nat.card B = 11520) (hsec : Nat.card (B ⧸ pCore 2 B) = 360)
    (N : Subgroup B) [N.Normal] (hN : IsPGroup 2 N) (hne : Nat.card N ≠ 32)
    (hQ : IsAlternating (B ⧸ N) 5 ∨ IsAlternating (B ⧸ N) 6 ∨
      IsAlternating (B ⧸ N) 7 ∨ IsAlternatingCover (B ⧸ N) 6 ∨
      ClassicalGroup.IsPSL (B ⧸ N) 3 2 ∨ ClassicalGroup.IsPSL (B ⧸ N) 4 2) : False := by
  have hd := card_quotient_dvd_card N
  rw [hc] at hd
  rcases hQ with hQ | hQ | hQ | hQ | hQ | hQ
  · exact no_altFive_quotient hsec N hN hQ
  · have he := eq_twoCore_of_quotient_card N hN (by
      rw [card_alternating hQ, hsec]; norm_num)
    exact hne (he ▸ hcore)
  · rw [card_alternating hQ] at hd; norm_num at hd
  · rw [card_cover hQ] at hd; norm_num at hd
  · rw [card_linear_three hQ] at hd; norm_num at hd
  · rw [card_linear_four hQ] at hd; norm_num at hd

/-- The A.3.12 catalogue itself excludes the order-32, A₆-quotient shape
in every proper embedding. No ambient classification is assumed here. -/
theorem not_a312_embedding {Q : Type*} [Group Q] [Finite Q]
    {B K : Subgroup Q} (hBK : B < K)
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) :
    ¬ A312Embedding B K := by
  have hc := card_of_shape hcore hA6
  have hsec := quotient_card hA6
  have smallQ (N : Subgroup B) [N.Normal] (hN : IsPGroup 2 N)
      (hne : Nat.card N ≠ 32)
      (hQ : IsAlternating (B ⧸ N) 5 ∨ IsAlternating (B ⧸ N) 6 ∨
        IsAlternating (B ⧸ N) 7 ∨ IsAlternatingCover (B ⧸ N) 6 ∨
        ClassicalGroup.IsPSL (B ⧸ N) 3 2 ∨ ClassicalGroup.IsPSL (B ⧸ N) 4 2) : False :=
    no_small_quotient hcore hc hsec N hN hne hQ
  intro h
  cases h with
  | one eq => exact hBK.ne eq
  | two n hn small large residual => exact no_binary_rank_one hsec small
  | three m hm small large residual =>
      obtain ⟨f⟩ := small
      apply BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m hm
      rw [← Nat.card_congr f.toEquiv, hsec]
      norm_num
  | four small large residual => exact no_small_section hsec (by tauto)
  | five small large residual => exact no_small_section hsec (by tauto)
  | six small large => exact no_small_model hc (by tauto)
  | seven models =>
      rcases models with ⟨small, _⟩ | ⟨small, _⟩ <;> exact no_small_model hc (by tauto)
  | eight models =>
      rcases models with ⟨p, hp, ho, _, small, _⟩ | ⟨p, hp, small, _⟩
      · exact no_psl_prime hc hp ho small
      · exact no_small_model hc (by tauto)
  | nine models =>
      rcases models with ⟨p, _, hp, _, _, small, _⟩ | ⟨small, _⟩ | ⟨small, _⟩
      · exact no_sl_prime hc hp small
      · exact no_small_model hc (by tauto)
      · exact no_small_model hc (by tauto)
  | ten p hp ho hlarge small large => exact no_odd_extension hc hp small
  | eleven small large => exact no_small_model hc (by tauto)
  | twelve models =>
      rcases models with ⟨⟨N, _, hN, hQ⟩, _⟩ | ⟨⟨N, _, hN, hQ⟩, _⟩ <;>
        exact smallQ N (elementary_two hN) (by rw [card_elementary hN]; norm_num) (by tauto)
  | thirteen large small =>
      rcases small with hM22 | small | ⟨N, _, hN, hQ⟩ | ⟨N, _, hN, hQ⟩
      · obtain ⟨e⟩ := hM22
        have hM := Nat.card_congr e.toEquiv
        rw [Sporadic.Mathieu.m22_order, hc] at hM
        norm_num at hM
      · have hh := card_linear_three_four small
        omega
      · exact smallQ N (elementary_two hN) (by rw [card_elementary hN]; norm_num) (by tauto)
      · exact smallQ N (elementary_two hN) (by rw [card_elementary hN]; norm_num) (by tauto)
  | fourteen large small =>
      rcases small with ⟨N, _, hN, hQ⟩ | ⟨N, _, hN, hQ⟩ | ⟨N, _, hN, hQ⟩
      · exact smallQ N (elementary_two hN) (by rw [card_elementary hN]; norm_num) (by tauto)
      · exact smallQ N (elementary_two hN) (by rw [card_elementary hN]; norm_num) (by tauto)
      · exact smallQ N (extraspecial_two hN) (by rw [hN.2]; norm_num) (by tauto)
  | fifteen small large => exact no_small_model hc (by tauto)
  | sixteen small large =>
      obtain ⟨N, _, hN, hQ⟩ := small
      exact no_altFive_quotient hsec N (extraspecial_two hN) hQ
  | seventeen large small =>
      rcases small with ⟨N, _, hN, hQ⟩ | ⟨N, _, hN, hQ⟩ | hQ | hQ | hQ | hQ
      · have hd := N.card_subgroup_dvd_card
        rw [hN.2, hc] at hd
        norm_num at hd
      · have hd := N.card_subgroup_dvd_card
        rw [card_elementary hN, hc] at hd
        norm_num at hd
      all_goals exact no_small_section hsec (by tauto)
  | eighteen large small =>
      rcases small with ⟨N, _, hN, hQ⟩ | ⟨N, _, ⟨f⟩, hQ⟩
      · exact no_altFive_quotient hsec N (cyclicCentral_two hN) hQ
      · have hd := card_quotient_dvd_card N
        rw [card_linear_three hQ, hc] at hd
        norm_num at hd
  | nineteen large small =>
      rcases small with ⟨N, _, hN, hQ⟩ | ⟨N, _, hN, hQ⟩
      · exact smallQ N (extraspecial_two hN) (by rw [hN.2]; norm_num) (by tauto)
      · exact smallQ N (elementary_two hN) (by rw [card_elementary hN]; norm_num) (by tauto)
  | twenty large small kernel => omega
  | twenty_one p hp ho noncentral generation quotient =>
      exact no_oddCore_supplement hBK.le hc hp generation quotient
  | twenty_two p hp noncentral large image =>
      exact no_oddCore_image_five hBK.le hc image

/-- Apply the sieve to the exact unique-containment-and-embedding output
of A.3.12. The containing component is the supplied K. -/
theorem not_a312_conclusion {Q : Type*} [Group Q] [Finite Q]
    {B K : Subgroup Q} (hK : K.IsCComponent) (hBK : B < K)
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) :
    ¬ A312Conclusion B := by
  rintro ⟨D, hD, hBD, hu, hemb⟩
  have he : D = K := (hu K hK hBK.le).symm
  subst D
  exact not_a312_embedding hBK hcore hA6 hemb


end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
