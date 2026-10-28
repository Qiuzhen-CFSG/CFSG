module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.PPrimeCore
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.GroupTheory.PCoreSurjective.OddExtension
/-!
# Orders in the exceptional component lifting argument

The actual two-core quotient orders control all normal two-group quotients.
The arithmetic retains the full group order as the section order times a power
of two; it is used in the original A.3.12 sieve for 13.6.27, printed p.934.
-/
@[expose] public section
noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LiftingOrders
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G]
theorem card_alt (h : IsAlternating G 8) : Nat.card G = 20160 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

theorem card_cover {n : ℕ} [Nontrivial (Fin n)] (h : IsAlternatingCover G n) :
    Nat.card G = n.factorial / 2 * 3 := by
  obtain ⟨_, ⟨ez⟩, ⟨eq⟩⟩ := h
  rw [card_eq_card_quotient_mul_card_subgroup (center G),
    Nat.card_congr eq.toEquiv, Nat.card_congr ez.toEquiv, nat_card_alternatingGroup]
  simp

theorem card_linear_three (h : ClassicalGroup.IsPSL G 3 2) : Nat.card G = 168 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact hc

theorem card_elementary {p r : ℕ} [NeZero p] (h : ElementaryModel p r G) : Nat.card G = p ^ r := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp

theorem elementary_two {r : ℕ} (h : ElementaryModel 2 r G) : IsPGroup 2 G :=
  IsPGroup.of_card (card_elementary h)

theorem extraspecial_two {r : ℕ} (h : ExtraspecialModel 2 r G) : IsPGroup 2 G :=
  IsPGroup.of_card h.2

theorem cyclicCentral_two {r : ℕ} (h : CyclicFourCentralProduct r G) : IsPGroup 2 G := by
  obtain ⟨C, E, ⟨eC⟩, hE, hgen, hcomm, _⟩ := h
  have hC : IsPGroup 2 C := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_congr eC.toEquiv]; norm_num)
  have h := hC.to_sup_of_normal_right' (extraspecial_two hE)
    ((commutator_eq_bot_iff_le_centralizer.mp hcomm).trans (centralizer_le_normalizer _))
  rw [hgen] at h
  exact h.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)

theorem section_dvd {m : ℕ} (hc : Nat.card (G ⧸ pCore 2 G) = m) : m ∣ Nat.card G := by
  rw [← hc]
  exact card_quotient_dvd_card _

variable [Finite G]

theorem card_shape {m : ℕ} (hc : Nat.card (G ⧸ pCore 2 G) = m) :
    ∃ n : ℕ, Nat.card G = m * 2 ^ n := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
  exact ⟨n, by rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 G), hc, hn]⟩

omit [Finite G] in
theorem section_dvd_quotient {m : ℕ} (hc : Nat.card (G ⧸ pCore 2 G) = m)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N) : m ∣ Nat.card (G ⧸ N) := by
  have hle : N ≤ pCore 2 G := le_sSup ⟨inferInstance, hN⟩
  rw [← hc, ← index_eq_card, ← index_eq_card]
  exact index_dvd_of_le hle


/-- Exactly the quotient orders in the terminal exceptional list. -/
def ExceptionalOrder (m : ℕ) : Prop := m = 20160 ∨ m = 604800 ∨ m = 10200960

theorem common_divisor {m : ℕ} (hm : ExceptionalOrder m) : 20160 ∣ m := by
  rcases hm with rfl | rfl | rfl <;> norm_num

theorem prime_le_twentyThree {p m n : ℕ} (hp : p.Prime) (hm : ExceptionalOrder m)
    (h : p ∣ m * 2 ^ n) : p ≤ 23 := by
  have h2 : p ∣ 2 → p ≤ 23 := fun h => (Nat.le_of_dvd (by decide) h).trans (by decide)
  have h3 : p ∣ 3 → p ≤ 23 := fun h => (Nat.le_of_dvd (by decide) h).trans (by decide)
  have h5 : p ∣ 5 → p ≤ 23 := fun h => (Nat.le_of_dvd (by decide) h).trans (by decide)
  have h7 : p ∣ 7 → p ≤ 23 := fun h => (Nat.le_of_dvd (by decide) h).trans (by decide)
  have h11 : p ∣ 11 → p ≤ 23 := fun h => (Nat.le_of_dvd (by decide) h).trans (by decide)
  have h23 : p ∣ 23 → p ≤ 23 := fun h => Nat.le_of_dvd (by decide) h
  rcases hp.dvd_mul.mp h with h | h
  · rcases hm with rfl | rfl | rfl
    · have he : 20160 = 2^6 * 3^2 * 5 * 7 := by norm_num
      rw [he] at h
      rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · exact h2 (hp.dvd_of_dvd_pow h)
          · exact h3 (hp.dvd_of_dvd_pow h)
        · exact h5 h
      · exact h7 h
    · have he : 604800 = 2^7 * 3^3 * 5^2 * 7 := by norm_num
      rw [he] at h
      rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · exact h2 (hp.dvd_of_dvd_pow h)
          · exact h3 (hp.dvd_of_dvd_pow h)
        · exact h5 (hp.dvd_of_dvd_pow h)
      · exact h7 h
    · have he : 10200960 = 2^7 * 3^2 * 5 * 7 * 11 * 23 := by norm_num
      rw [he] at h
      rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · rcases hp.dvd_mul.mp h with h | h
            · rcases hp.dvd_mul.mp h with h | h
              · exact h2 (hp.dvd_of_dvd_pow h)
              · exact h3 (hp.dvd_of_dvd_pow h)
            · exact h5 h
          · exact h7 h
        · exact h11 h
      · exact h23 h
  · exact h2 (hp.dvd_of_dvd_pow h)

omit [Finite G] in
theorem card_sl_two {q : ℕ} (h : IsSL G 2 q) : Nat.card G = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, hF]

omit [Finite G] in
theorem card_psl_two {q : ℕ} (h : ClassicalGroup.IsPSL G 2 q) :
    Nat.card G * Nat.gcd 2 (q - 1) = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, ← hF]
  have hz := Atlas.ExceptionalSupport.card_sl_center (ι := Fin 2) (F := F)
  simp only [Fintype.card_fin] at hz
  rw [← hz, ← card_eq_card_quotient_mul_card_subgroup (center SL(2,F)), Atlas.card_sl_two]

omit [Finite G] in
theorem no_binary_rank_one {m n : ℕ} (hm : ExceptionalOrder m)
    (hc : Nat.card G = m) : ¬ ClassicalGroup.IsPSL G 2 (2^n) := by
  intro h
  have he := card_psl_two h
  rw [hc] at he
  have hg : Nat.gcd 2 (2^n - 1) ≤ 2 := Nat.gcd_le_left _ (by decide)
  have hn : n ≤ 8 := by
    by_contra hn
    have hpow : 512 ≤ 2^n := by
      exact (show 512 = 2^9 by norm_num).le.trans
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 9 ≤ n by omega))
    have hs : 262143 ≤ (2^n)^2 - 1 :=
      Nat.sub_le_sub_right (Nat.pow_le_pow_left hpow 2) 1
    rcases hm with rfl | rfl | rfl <;> nlinarith
  interval_cases n <;> rcases hm with rfl | rfl | rfl <;> norm_num at he

theorem no_sl_prime {m : ℕ} (hm : ExceptionalOrder m)
    (hc : Nat.card (G ⧸ pCore 2 G) = m) {p : ℕ} (hp : p.Prime) : ¬ IsSL G 2 p := by
  intro h
  obtain ⟨n, hn⟩ := card_shape hc
  have hb := card_sl_two h
  have hpB : p ∣ Nat.card G := by rw [hb]; exact dvd_mul_right _ _
  have hp23 := prime_le_twentyThree hp hm (hn ▸ hpB)
  have hbound : Nat.card G ≤ 12144 := by
    rw [hb]
    exact Nat.mul_le_mul hp23 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hp23 2) 1)
  have hd := Nat.le_of_dvd (Nat.card_pos (α := G)) ((common_divisor hm).trans (section_dvd hc))
  omega

theorem no_psl_prime {m : ℕ} (hm : ExceptionalOrder m)
    (hc : Nat.card (G ⧸ pCore 2 G) = m) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL G 2 p := by
  intro h
  obtain ⟨n, hn⟩ := card_shape hc
  have hb := card_psl_two h
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hpg : ¬ p ∣ Nat.gcd 2 (p - 1) := by
    intro hh
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (dvd_trans hh (Nat.gcd_dvd_left _ _)))
  have hpB : p ∣ Nat.card G := (hp.dvd_mul.mp
    (hb.symm ▸ (dvd_mul_right p (p ^ 2 - 1)))).resolve_right hpg
  have hp23 := prime_le_twentyThree hp hm (hn ▸ hpB)
  have hdpos : 1 ≤ Nat.gcd 2 (p - 1) := Nat.gcd_pos_of_pos_left _ (by decide)
  have hbound : p * (p ^ 2 - 1) ≤ 12144 :=
    Nat.mul_le_mul hp23 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hp23 2) 1)
  have hd := Nat.le_of_dvd (Nat.card_pos (α := G)) ((common_divisor hm).trans (section_dvd hc))
  nlinarith

theorem no_odd_extension {m : ℕ} (hm : ExceptionalOrder m)
    (hc : Nat.card (G ⧸ pCore 2 G) = m) {p : ℕ} (hp : p.Prime) :
    ¬ HasExtension G (ElementaryModel p 2) (fun Z _ => IsSL Z 2 p) := by
  rintro ⟨N, _, hN, hQ⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨n, hn⟩ := card_shape hc
  have hb : Nat.card G = (p * (p ^ 2 - 1)) * p ^ 2 := by
    rw [card_eq_card_quotient_mul_card_subgroup N, card_sl_two hQ, card_elementary hN]
  have hpB : p ∣ Nat.card G := by rw [hb]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hp23 := prime_le_twentyThree hp hm (hn ▸ hpB)
  have hd := (common_divisor hm).trans (section_dvd hc)
  rw [hb] at hd
  interval_cases p <;> first | (solve | norm_num at hp) | (solve | norm_num at hd)
omit [Finite G] in
theorem sixtyFour_dvd_odd_quotient_image (H N : Subgroup G) [N.Normal]
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

theorem oddCore_image_top {X : Type*} [Group X] {B K : Subgroup X} (hBK : B ≤ K)
    (hgen : B ⊔ (pPrimeCore 2 K).map K.subtype = K) :
    (B.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 K)) = ⊤ := by
  have hg : B.subgroupOf K ⊔ pPrimeCore 2 K = ⊤ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hBK, ← MonoidHom.range_eq_map, range_subtype]
    exact hgen
  have hh := congrArg (map (QuotientGroup.mk' (pPrimeCore 2 K))) hg
  simpa only [Subgroup.map_sup, ← QuotientGroup.ker_mk' (pPrimeCore 2 K),
    Subgroup.map_ker_self, sup_bot_eq, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] using hh

theorem not_oddCore_supplement {X : Type*} [Group X] [Finite X]
    {B K : Subgroup X} (hBK : B ≤ K)
    {m : ℕ} (hm : ExceptionalOrder m) (hcB : Nat.card (B ⧸ pCore 2 B) = m)
    {p : ℕ} (hp : p.Prime)
    (hgen : B ⊔ (pPrimeCore 2 K).map K.subtype = K)
    (hmodel : IsSL (K ⧸ pPrimeCore 2 K) 2 p) : False := by
  obtain ⟨n, hn⟩ := card_shape hcB
  have hH : Nat.card (B.subgroupOf K) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv
  have ht := oddCore_image_top hBK hgen
  have hc := card_sl_two hmodel
  have hpB : p ∣ Nat.card B := by
    rw [← hH]
    have hh := card_map_dvd (H := B.subgroupOf K) (QuotientGroup.mk' (pPrimeCore 2 K))
    rw [ht, card_top, hc] at hh
    exact dvd_trans (dvd_mul_right _ _) hh
  have hp23 := prime_le_twentyThree hp hm (hn ▸ hpB)
  have h64 : 64 ∣ Nat.card (B.subgroupOf K) := by
    rw [hH]
    exact dvd_trans (by norm_num : 64 ∣ 20160) ((common_divisor hm).trans (section_dvd hcB))
  have hi := sixtyFour_dvd_odd_quotient_image (B.subgroupOf K) (pPrimeCore 2 K)
    pPrimeCore_coprime_card h64
  rw [ht, card_top, hc] at hi
  interval_cases p <;> first | (solve | norm_num at hp) | (solve | norm_num at hi)

theorem not_oddCore_image_five {X : Type*} [Group X] [Finite X]
    {B K : Subgroup X} (hBK : B ≤ K)
    {m : ℕ} (hm : ExceptionalOrder m) (hcB : Nat.card (B ⧸ pCore 2 B) = m)
    (hmodel : IsSL ((B.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 K))) 2 5) :
    False := by
  have h64 : 64 ∣ Nat.card (B.subgroupOf K) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv]
    exact dvd_trans (by norm_num : 64 ∣ 20160) ((common_divisor hm).trans (section_dvd hcB))
  have hi := sixtyFour_dvd_odd_quotient_image (B.subgroupOf K) (pPrimeCore 2 K)
    pPrimeCore_coprime_card h64
  rw [card_sl_two hmodel] at hi
  norm_num at hi

omit [Finite G] in
theorem no_small_model (hd : 20160 ∣ Nat.card G)
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


/-- Equal orders of the two quotients identify a normal two-kernel with the full two-core. -/
theorem eq_twoCore_of_quotient_card (N : Subgroup G) [N.Normal]
    (hN : IsPGroup 2 N) (hc : Nat.card (G ⧸ N) = Nat.card (G ⧸ pCore 2 G)) :
    N = pCore 2 G := by
  have hle : N ≤ pCore 2 G := le_sSup ⟨inferInstance, hN⟩
  apply eq_of_le_of_card_ge hle
  have h1 := card_eq_card_quotient_mul_card_subgroup N
  have h2 := card_eq_card_quotient_mul_card_subgroup (pCore 2 G)
  rw [hc] at h1
  have hpos := Nat.card_pos (α := G ⧸ pCore 2 G)
  nlinarith

/-- A normal two-kernel does not change the intrinsic two-core quotient order. -/
theorem section_card_quotient {m : ℕ} (hc : Nat.card (G ⧸ pCore 2 G) = m)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N) :
    Nat.card ((G ⧸ N) ⧸ pCore 2 (G ⧸ N)) = m := by
  let e := MonoidHom.quotientPCoreEquivOfSurjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)
    (show IsPGroup 2 (QuotientGroup.mk' N).ker by rw [QuotientGroup.ker_mk']; exact hN)
  exact (Nat.card_congr e.toEquiv).symm.trans hc

theorem no_mathieu_small {m : ℕ} (hm : ExceptionalOrder m)
    (hc : Nat.card (G ⧸ pCore 2 G) = m)
    (hG : Nat.card G = 443520 ∨ Nat.card G = 244823040) : False := by
  obtain ⟨n, hn⟩ := card_shape hc
  have hmlo : 20160 ≤ m := Nat.le_of_dvd (by rcases hm with rfl | rfl | rfl <;> decide)
    (common_divisor hm)
  have hupper : Nat.card G ≤ 244823040 := by rcases hG with h | h <;> omega
  have hn13 : n ≤ 13 := by
    by_contra h
    have hp : 16384 ≤ 2^n :=
      (show 16384 = 2^14 by norm_num).le.trans
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 14 ≤ n by omega))
    nlinarith
  interval_cases n <;> rcases hm with rfl | rfl | rfl <;>
    rcases hG with hG | hG <;> norm_num at hn <;> omega

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LiftingOrders
