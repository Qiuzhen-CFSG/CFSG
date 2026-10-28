module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.EmbeddingReduction.ModelSeparation
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.PPrimeCore
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.MathieuTwentyFourStabilizer
public import Theory.Mathieu.M22.Properties.Order


/-!
# The A₈ two-core section sieve for A.3.12

For the actual embedded pair B ≤ K, the full twenty-two-case embedding
classification leaves equality, the parabolic residual in PSL₅(2), the
E₁₆-by-PSL₄(2) subgroup of M₂₄, or K isomorphic to J₄.

The section forces |B| = 20160 · 2ⁿ. Small quotients by normal two-subgroups
and fixed small orders exclude most branches. Prime divisibility bounds
prime-field parameters; the Suzuki order is prime to three. In the equal-order
PSL₃(4) branch, O₂(B) is first proved trivial, after which the checked model
separation applies. For the odd-core branches the actual restricted quotient
map has an odd-order kernel, so its image still has order divisible by 64.
The existing M₂₄ selector retains the exact normal E₁₆ extension kernel.

This proves the exhaustive sieve with no stabilizer premises. The parent
retains the source-level component-placement and marked-action assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.12,
printed pp.47–48, as used in 15.3.32(3), printed p.1133.
-/

noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction.Cases
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G]

private theorem card_alt (h : IsAlternating G 8) : Nat.card G = 20160 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

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

private theorem section_card (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 8)) :
    Nat.card (G ⧸ pCore 2 G) = 20160 := card_alt ⟨e⟩

private theorem section_dvd (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 8)) :
    20160 ∣ Nat.card G := by
  rw [← section_card e]
  exact card_quotient_dvd_card _

variable [Finite G]

private theorem card_shape (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 8)) :
    ∃ n : ℕ, Nat.card G = 20160 * 2 ^ n := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
  exact ⟨n, by rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 G), section_card e, hn]⟩

omit [Finite G] in
private theorem section_dvd_quotient (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 8))
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N) : 20160 ∣ Nat.card (G ⧸ N) := by
  have hle : N ≤ pCore 2 G := le_sSup ⟨inferInstance, hN⟩
  rw [← section_card e, ← index_eq_card, ← index_eq_card]
  exact index_dvd_of_le hle

private theorem prime_le_seven {p n : ℕ} (hp : p.Prime) (h : p ∣ 20160 * 2 ^ n) : p ≤ 7 := by
  have hfactor : 20160 = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num
  rw [hfactor] at h
  simp only [hp.dvd_mul] at h
  have h2 : p ∣ 2 → p ≤ 7 := fun h => (Nat.le_of_dvd (by decide) h).trans (by decide)
  have h3 : p ∣ 3 → p ≤ 7 := fun h => (Nat.le_of_dvd (by decide) h).trans (by decide)
  have h5 : p ∣ 5 → p ≤ 7 := fun h => (Nat.le_of_dvd (by decide) h).trans (by decide)
  have h7 : p ∣ 7 → p ≤ 7 := fun h => Nat.le_of_dvd (by decide) h
  rcases h with (((h | h) | h) | h) | h
  · exact h2 (hp.dvd_of_dvd_pow h)
  · exact h3 (hp.dvd_of_dvd_pow h)
  · exact h5 h
  · exact h7 h
  · exact h2 (hp.dvd_of_dvd_pow h)

omit [Finite G] in
private theorem card_sl_two {q : ℕ} (h : IsSL G 2 q) : Nat.card G = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, hF]

omit [Finite G] in
private theorem card_psl_two {q : ℕ} (h : ClassicalGroup.IsPSL G 2 q) :
    Nat.card G * Nat.gcd 2 (q - 1) = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, ← hF]
  have hz := Atlas.ExceptionalSupport.card_sl_center (ι := Fin 2) (F := F)
  simp only [Fintype.card_fin] at hz
  rw [← hz,
    ← card_eq_card_quotient_mul_card_subgroup (center SL(2,F)), Atlas.card_sl_two]

omit [Finite G] in
private theorem not_psl_two_card (hc : Nat.card G = 20160) {q : ℕ} :
    ¬ ClassicalGroup.IsPSL G 2 q := by
  intro h
  have he := card_psl_two h
  rw [hc] at he
  have hdpos : 1 ≤ Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by decide)
  have hdle : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left _ (by decide)
  have hlo : 27 ≤ q := by
    by_contra hh
    have hq : q ≤ 26 := by omega
    have hs : q ^ 2 - 1 ≤ 675 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have := Nat.mul_le_mul hq hs
    nlinarith
  have hhi : q ≤ 35 := by
    by_contra hh
    have hq : 36 ≤ q := by omega
    have hs : 1295 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have := Nat.mul_le_mul hq hs
    nlinarith
  interval_cases q <;> norm_num at he

private theorem not_sl_prime (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 8))
    {p : ℕ} (hp : p.Prime) : ¬ IsSL G 2 p := by
  intro h
  obtain ⟨n, hn⟩ := card_shape e
  have hc := card_sl_two h
  have hpB : p ∣ Nat.card G := by rw [hc]; exact dvd_mul_right _ _
  have hp7 := prime_le_seven hp (hn ▸ hpB)
  have hbound : Nat.card G ≤ 336 := by
    rw [hc]
    exact Nat.mul_le_mul hp7 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hp7 2) 1)
  have := Nat.le_of_dvd (Nat.card_pos (α := G)) (section_dvd e)
  omega

private theorem not_psl_prime (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 8))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) : ¬ ClassicalGroup.IsPSL G 2 p := by
  intro h
  obtain ⟨n, hn⟩ := card_shape e
  have hc := card_psl_two h
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hpg : ¬ p ∣ Nat.gcd 2 (p - 1) := by
    intro hh
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (dvd_trans hh (Nat.gcd_dvd_left _ _)))
  have hpB : p ∣ Nat.card G := (hp.dvd_mul.mp
    (hc.symm ▸ (dvd_mul_right p (p ^ 2 - 1)))).resolve_right hpg
  have hp7 := prime_le_seven hp (hn ▸ hpB)
  have hdpos : 1 ≤ Nat.gcd 2 (p - 1) := Nat.gcd_pos_of_pos_left _ (by decide)
  have hbound : p * (p ^ 2 - 1) ≤ 336 :=
    Nat.mul_le_mul hp7 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hp7 2) 1)
  have := Nat.le_of_dvd (Nat.card_pos (α := G)) (section_dvd e)
  nlinarith

private theorem not_odd_extension (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 8))
    {p : ℕ} (hp : p.Prime) :
    ¬ HasExtension G (ElementaryModel p 2) (fun Z _ => IsSL Z 2 p) := by
  rintro ⟨N, _, hN, hQ⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨n, hn⟩ := card_shape e
  have hc : Nat.card G = (p * (p ^ 2 - 1)) * p ^ 2 := by
    rw [card_eq_card_quotient_mul_card_subgroup N, card_sl_two hQ, card_elementary hN]
  have hpB : p ∣ Nat.card G := by rw [hc]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hp7 := prime_le_seven hp (hn ▸ hpB)
  have hbound : Nat.card G ≤ 16464 := by
    rw [hc]
    exact Nat.mul_le_mul
      (Nat.mul_le_mul hp7 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hp7 2) 1))
      (Nat.pow_le_pow_left hp7 2)
  have := Nat.le_of_dvd (Nat.card_pos (α := G)) (section_dvd e)
  omega

omit [Finite G] in
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

private theorem not_oddCore_supplement {X : Type*} [Group X] [Finite X]
    {B K : Subgroup X} (hBK : B ≤ K)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 8))
    {p : ℕ} (hp : p.Prime)
    (hgen : B ⊔ (pPrimeCore 2 K).map K.subtype = K)
    (hmodel : IsSL (K ⧸ pPrimeCore 2 K) 2 p) : False := by
  obtain ⟨n, hn⟩ := card_shape e
  have hH : Nat.card (B.subgroupOf K) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv
  have ht := oddCore_image_top hBK hgen
  have hc := card_sl_two hmodel
  have hpB : p ∣ Nat.card B := by
    rw [← hH]
    have hh := card_map_dvd (H := B.subgroupOf K) (QuotientGroup.mk' (pPrimeCore 2 K))
    rw [ht, card_top, hc] at hh
    exact dvd_trans (dvd_mul_right _ _) hh
  have hp7 := prime_le_seven hp (hn ▸ hpB)
  have h64 : 64 ∣ Nat.card (B.subgroupOf K) := by
    rw [hH]
    exact dvd_trans (by norm_num : 64 ∣ 20160) (section_dvd e)
  have hi := sixtyFour_dvd_odd_quotient_image (B.subgroupOf K) (pPrimeCore 2 K)
    pPrimeCore_coprime_card h64
  rw [ht, card_top, hc] at hi
  interval_cases p <;> norm_num at *

private theorem not_oddCore_image_five {X : Type*} [Group X] [Finite X]
    {B K : Subgroup X} (hBK : B ≤ K)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 8))
    (hmodel : IsSL ((B.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 K))) 2 5) :
    False := by
  have h64 : 64 ∣ Nat.card (B.subgroupOf K) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv]
    exact dvd_trans (by norm_num : 64 ∣ 20160) (section_dvd e)
  have hi := sixtyFour_dvd_odd_quotient_image (B.subgroupOf K) (pPrimeCore 2 K)
    pPrimeCore_coprime_card h64
  rw [card_sl_two hmodel] at hi
  norm_num at hi

omit [Finite G] in
private theorem no_small_model (hd : 20160 ∣ Nat.card G)
    (h : IsAlternating G 5 ∨ IsAlternating G 6 ∨ IsAlternating G 7 ∨
      IsAlternatingCover G 6 ∨ ClassicalGroup.IsPSL G 3 2) : False := by
  rcases h with h | h | h | h | h
  · obtain ⟨f⟩ := h
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup] at hd
    norm_num at hd
  · obtain ⟨f⟩ := h
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup] at hd
    norm_num at hd
  · obtain ⟨f⟩ := h
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup] at hd
    norm_num at hd
  · rw [card_cover h] at hd
    norm_num at hd
  · rw [card_linear_three h] at hd
    norm_num at hd

private theorem not_mathieu22 (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 8)) :
    ¬ Nonempty (G ≃* Sporadic.Mathieu.M22) := by
  rintro ⟨f⟩
  obtain ⟨n, hn⟩ := card_shape e
  have h11 : 11 ∣ 20160 * 2 ^ n := by
    rw [← hn, Nat.card_congr f.toEquiv, Sporadic.Mathieu.m22_order]
    norm_num
  have := prime_le_seven (by norm_num : Nat.Prime 11) h11
  omega

omit [Finite G] in
private theorem not_psl3_four (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 8)) :
    ¬ ClassicalGroup.IsPSL G 3 4 := by
  rintro ⟨F, _, _, hF, ⟨f⟩⟩
  have hc : Nat.card G = 20160 := by
    rw [Nat.card_congr f.toEquiv]
    have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    rw [hF] at h
    norm_num [Fin.prod_univ_succ] at h
    omega
  have hcore : pCore 2 G = ⊥ := Subgroup.card_eq_one.mp (by
    have h := card_eq_card_quotient_mul_card_subgroup (pCore 2 G)
    rw [hc, section_card e] at h
    omega)
  let q : (G ⧸ pCore 2 G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  exact ModelSeparation.alt8_not_equiv_psl3Card4 hF ⟨e.symm.trans (q.trans f)⟩

/-- The exhaustive A.3.12 sieve at the actual embedded A₈ two-core section.
The parabolic residual and the normal E₁₆ extension kernel are retained. -/
public theorem alternatives_of_alt8_section {X : Type*} [Group X] [Finite X]
    {B K : Subgroup X} (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 8))
    (h : A312Embedding B K) :
    B = K ∨
    (ClassicalGroup.IsPSL K 5 2 ∧ IsParabolicResidual B K false) ∨
    (Nonempty (K ≃* Sporadic.Mathieu.M24) ∧
      HasExtension B (ElementaryModel 2 4) (fun Z _ => ClassicalGroup.IsPSL Z 4 2)) ∨
    Nonempty (K ≃* Janko4.Model) := by
  have hd := section_dvd eB
  have hq : 20160 ∣ Nat.card (B ⧸ pCore 2 B) := by rw [section_card eB]
  cases h with
  | one eq => exact Or.inl eq
  | two n hn small large residual =>
      exact False.elim (not_psl_two_card (section_card eB) small)
  | three m hm small large residual =>
      obtain ⟨f⟩ := small
      have h3 : 3 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
        rw [← Nat.card_congr f.toEquiv, section_card eB]
        norm_num
      exact False.elim (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m hm h3)
  | four small large residual =>
      exact False.elim (no_small_model hq (by tauto))
  | five small large residual => exact Or.inr (Or.inl ⟨large, residual⟩)
  | six small large =>
      exact False.elim (no_small_model hd (by tauto))
  | seven models =>
      rcases models with ⟨small, _⟩ | ⟨small, _⟩
      · exact False.elim (no_small_model hd (by tauto))
      · exact False.elim (no_small_model hd (by tauto))
  | eight models =>
      rcases models with ⟨p, hp, ho, _, small, _⟩ | ⟨p, hp, small, _⟩
      · exact False.elim (not_psl_prime eB hp ho small)
      · exact False.elim (no_small_model hd (by tauto))
  | nine models =>
      rcases models with ⟨p, _, hp, _, _, small, _⟩ | ⟨small, _⟩ | ⟨small, _⟩
      · exact False.elim (not_sl_prime eB hp small)
      · exact False.elim (no_small_model hd (by tauto))
      · exact False.elim (no_small_model hd (by tauto))
  | ten p hp ho hlarge small large =>
      exact False.elim (not_odd_extension eB hp small)
  | eleven small large =>
      exact False.elim (no_small_model hd (by tauto))
  | twelve models =>
      rcases models with ⟨⟨N, _, hN, hQ⟩, _⟩ | ⟨⟨N, _, hN, hQ⟩, _⟩
      · exact False.elim (no_small_model (section_dvd_quotient eB N (elementary_two hN))
          (by tauto))
      · exact False.elim (no_small_model (section_dvd_quotient eB N (elementary_two hN))
          (by tauto))
  | thirteen large small =>
      rcases small with small | small | ⟨N, _, hN, hQ⟩ | ⟨N, _, hN, hQ⟩
      · exact False.elim (not_mathieu22 eB small)
      · exact False.elim (not_psl3_four eB small)
      · exact False.elim (no_small_model (section_dvd_quotient eB N (elementary_two hN))
          (by tauto))
      · exact False.elim (no_small_model (section_dvd_quotient eB N (elementary_two hN))
          (by tauto))
  | fourteen large small =>
      have hsection : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 :=
        ⟨ZMod 2, inferInstance, inferInstance, by simp,
          ⟨eB.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩
      exact Or.inr (Or.inr (Or.inl ⟨large,
        Chapter1.Terminal.LinearFourActions.MathieuTwentyFourStabilizer.extension_of_fourteen
          B hsection small⟩))
  | fifteen small large =>
      exact False.elim (no_small_model hd (by tauto))
  | sixteen small large =>
      obtain ⟨N, _, hN, hQ⟩ := small
      exact False.elim (no_small_model (section_dvd_quotient eB N (extraspecial_two hN))
        (by tauto))
  | seventeen large small => exact Or.inr (Or.inr (Or.inr large))
  | eighteen large small =>
      rcases small with ⟨N, _, hN, hQ⟩ | ⟨N, _, ⟨f⟩, hQ⟩
      · exact False.elim (no_small_model (section_dvd_quotient eB N (cyclicCentral_two hN))
          (by tauto))
      · have hN : IsPGroup 2 N := IsPGroup.of_card (n := 6) (by
          rw [Nat.card_congr f.toEquiv]
          norm_num)
        exact False.elim (no_small_model (section_dvd_quotient eB N hN) (by tauto))
  | nineteen large small =>
      rcases small with ⟨N, _, hN, hQ⟩ | ⟨N, _, hN, hQ⟩
      · exact False.elim (no_small_model (section_dvd_quotient eB N (extraspecial_two hN))
          (by tauto))
      · exact False.elim (no_small_model (section_dvd_quotient eB N (elementary_two hN))
          (by tauto))
  | twenty large small kernel =>
      exact False.elim (no_small_model hq (by tauto))
  | twenty_one p hp ho noncentral generation quotient =>
      exact False.elim (not_oddCore_supplement hBK eB hp generation quotient)
  | twenty_two p hp noncentral large image =>
      exact False.elim (not_oddCore_image_five hBK eB image)
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction.Cases
