module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Structure.CubicParity.BlockCalculation
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Structure.ThetaImage
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.LocalData

/-!
# Surjectivity from the actual cubic quotient actor

Every cubic element of the four-plus-three stabilizer is even on each block.
Thus its cubic-generated subgroup lies in the image of A₄ × A₃. An even
actor has equal signs on the two blocks, so conjugation has one common
scalar on their cubic quotients. The block calculations express this as a
square-one discrepancy, uniformly on the whole cubic-generated subgroup.

For the actual map L₁ → H/O₂(H) → S₇, the kernel is a normal two-group.
A discrepancy whose image has square one therefore has square in O₂(L₁).
Since L₁/O₂(L₁) has exponent three, its quotient class is trivial. This
transports the scalar alternatives without identifying distinct two-cores
or identifying the source quotient lines with the coordinate lines.

The specified source actor fixes one nonzero cubic quotient line and
inverts the other. It cannot act by one scalar, so its seven-point image
is odd. An image containing A₇ and an odd element is S₇.

Source: Aschbacher–Smith, 13.8.24, printed pp.958–959, with the local
residual notation of 13.2.1, generation in 13.2.2(3), and the cubic quotient
action in the proof of 13.7.5(7), printed pp.877–878 and 938
(1 March 2004 manuscript).
-/

public section
open Equiv Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection.CubicParity

private def blockAlternating : Subgroup FourThree :=
  (alternatingGroup (Fin 4)).prod (alternatingGroup (Fin 3))

private theorem sign_of_cube {n : ℕ} (g : Perm (Fin n)) (h : g ^ 3 = 1) :
    g.sign = 1 := by
  have hs : g.sign ^ 3 = 1 := by rw [← map_pow, h, map_one]
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Int.units_sq, one_mul] at hs
  exact hs

private theorem theta_le_blockAlternating : fourThreeTheta ≤ blockAlternating.map fourThreeHom := by
  apply (closure_le _).mpr
  rintro x ⟨⟨c, rfl⟩, hc⟩
  refine mem_map.mpr ⟨c, ?_, rfl⟩
  have h3 : c ^ 3 = 1 := fourThreeHom_injective (by
    rw [map_pow, map_one]
    simpa only [hc] using pow_orderOf_eq_one (fourThreeHom c))
  exact ⟨sign_of_cube c.1 (congrArg Prod.fst h3),
    sign_of_cube c.2 (congrArg Prod.snd h3)⟩

private theorem product_sign (t : FourThree) :
    (fourThreeHom t).sign = t.1.sign * t.2.sign := by
  change (finSumFinEquiv.permCongr (Equiv.sumCongr t.1 t.2)).sign = _
  rw [Perm.sign_permCongr, Perm.sign_sumCongr]

/-- An even actor has the same scalar on both cubic coordinates, modulo
square-one discrepancies. This statement applies uniformly to all of theta. -/
theorem even_scalar_square (t : S7) (ht : t ∈ fourThreeStabilizer)
    (he : t.sign = 1) :
    (∀ c ∈ fourThreeTheta, (t * c * t⁻¹ * c⁻¹) ^ 2 = 1) ∨
    (∀ c ∈ fourThreeTheta, (t * c * t⁻¹ * c) ^ 2 = 1) := by
  obtain ⟨s, rfl⟩ := ht
  have hs : s.1.sign = s.2.sign := by
    rw [product_sign] at he
    have he' := mul_eq_one_iff_eq_inv.mp he
    simpa only [Int.units_inv_eq_self] using he'
  by_cases h : s.1.sign = 1
  · left
    intro c hc
    obtain ⟨x, hx, rfl⟩ := theta_le_blockAlternating hc
    have h1 := four_scalar_square s.1 x.1 hx.1
    have h2 := three_scalar s.2 x.2 hx.2
    rw [if_pos h] at h1
    rw [if_pos (hs ▸ h)] at h2
    have hp : (s * x * s⁻¹ * x⁻¹) ^ 2 = 1 := by
      refine Prod.ext h1 ?_
      change (s.2 * x.2 * s.2⁻¹ * x.2⁻¹) ^ 2 = 1
      rw [h2, one_pow]
    simpa only [map_pow, map_mul, map_inv, map_one] using congrArg fourThreeHom hp
  · right
    intro c hc
    obtain ⟨x, hx, rfl⟩ := theta_le_blockAlternating hc
    have h1 := four_scalar_square s.1 x.1 hx.1
    have h2 := three_scalar s.2 x.2 hx.2
    rw [if_neg h] at h1
    rw [if_neg (hs ▸ h)] at h2
    have hp : (s * x * s⁻¹ * x) ^ 2 = 1 := by
      refine Prod.ext h1 ?_
      change (s.2 * x.2 * s.2⁻¹ * x.2) ^ 2 = 1
      rw [h2, one_pow]
    simpa only [map_pow, map_mul, map_inv, map_one] using congrArg fourThreeHom hp

private theorem quotient_cube {D : Type*} [Group D]
    (e : D ⧸ pCore 2 D ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
    (z : D ⧸ pCore 2 D) : z ^ 3 = 1 := by
  apply e.injective
  rw [map_pow, map_one]
  have h (w : Multiplicative (ZMod 3)) : w ^ 3 = 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      using (pow_card_eq_one' (x := w))
  exact Prod.ext (h (e z).1) (h (e z).2)

private theorem quotient_eq_one_of_image_square {D : Type*} [Group D]
    (e : D ⧸ pCore 2 D ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
    (f : D →* S7) (hk : IsPGroup 2 f.ker) (x : D) (hx : (f x) ^ 2 = 1) :
    QuotientGroup.mk' (pCore 2 D) x = 1 := by
  have hle : f.ker ≤ pCore 2 D := le_sSup ⟨inferInstance, hk⟩
  have hmem : x ^ 2 ∈ pCore 2 D := hle (by
    change f (x ^ 2) = 1
    rwa [map_pow])
  have h2 : (QuotientGroup.mk' (pCore 2 D) x) ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  have h3 := quotient_cube e (QuotientGroup.mk' (pCore 2 D) x)
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul] at h3
  exact h3

/-- The scalar alternatives descend through any actual homomorphism with
two-group kernel; no equality between distinct two-cores is assumed. -/
theorem even_scalar_quotient {D : Type*} [Group D]
    (e : D ⧸ pCore 2 D ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
    (f : D →* S7) (hk : IsPGroup 2 f.ker) (hf : f.range ≤ fourThreeTheta)
    (τ : D →* D) (t : S7) (ht : t ∈ fourThreeStabilizer) (he : t.sign = 1)
    (ha : ∀ x, f (τ x) = t * f x * t⁻¹) :
    (∀ x, QuotientGroup.mk' (pCore 2 D) (τ x) = QuotientGroup.mk' (pCore 2 D) x) ∨
    (∀ x, QuotientGroup.mk' (pCore 2 D) (τ x) = (QuotientGroup.mk' (pCore 2 D) x)⁻¹) := by
  rcases even_scalar_square t ht he with h | h
  · left
    intro x
    have hx := h (f x) (hf ⟨x, rfl⟩)
    have hz := quotient_eq_one_of_image_square e f hk (τ x * x⁻¹) (by
      simpa only [map_mul, map_inv, ha] using hx)
    exact mul_inv_eq_one.mp (by simpa only [map_mul, map_inv] using hz)
  · right
    intro x
    have hx := h (f x) (hf ⟨x, rfl⟩)
    have hz := quotient_eq_one_of_image_square e f hk (τ x * x) (by
      simpa only [map_mul, ha] using hx)
    exact eq_inv_iff_mul_eq_one.mpr (by simpa only [map_mul] using hz)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection.CubicParity

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
open PairsBranch.LocalRank

private theorem exists_nontrivial_quotient_element {G : Type*} [Group G]
    (L₁ Y : Subgroup G)
    (hc : Nat.card ((Y.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))) = 3) :
    ∃ a : L₁, a.val ∈ Y ∧ QuotientGroup.mk' (pCore 2 L₁) a ≠ 1 := by
  rcases ((Y.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))).bot_or_exists_ne_one
      with hb | ⟨z, hz, hn⟩
  · rw [hb, Subgroup.card_bot] at hc
    norm_num at hc
  · obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, ha, hn⟩

/-- The genuine cubic quotient actor forces the seven-point image to be S₇.
The proof needs no permutation-factor marking and retains inversion only
modulo the intrinsic two-core of L₁. -/
theorem surjective_of_localResidualData {G : Type*} [Group G] [Finite G]
    (H L₁ L₀ X T : Subgroup G) (hbase : L₁ ⊔ T ≤ H)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hAlt : alternatingGroup (Fin 7) ≤ φ.range)
    (hP : Source.starImage H (L₁ ⊔ T) = fourThreeStabilizer.comap φ)
    (d : LocalResidualData L₁ L₀ X T)
    (hTheta : (Source.starImage H L₁).map φ = fourThreeTheta) :
    Function.Surjective φ := by
  let hLH : L₁ ≤ H := le_sup_left.trans hbase
  let q : H →* Source.Hstar H := QuotientGroup.mk' (pCore 2 H)
  let r := starRestriction H L₁ hLH
  let f := φ.comp r
  let τ := (L₁.normalizerMonoidHom d.actor).toMonoidHom
  let tH : H := ⟨d.actor.val, (le_sup_right.trans hbase) d.actor_mem⟩
  let t := φ (q tH)
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = r.ker := by
      ext x
      change φ (r x) = 1 ↔ r x = 1
      rw [← φ.map_one, hφ.eq_iff]
    rw [he]
    exact starRestriction_ker_isTwoGroup H L₁ hLH
  have hf : f.range ≤ fourThreeTheta := by
    change (φ.comp (starRestriction H L₁ hLH)).range ≤ _
    rw [MonoidHom.range_comp, starRestriction_range, hTheta]
  have ht : t ∈ fourThreeStabilizer := by
    change q tH ∈ fourThreeStabilizer.comap φ
    rw [← hP]
    exact ⟨tH, (show T ≤ L₁ ⊔ T from le_sup_right) d.actor_mem, rfl⟩
  have ha (x : L₁) : f (τ x) = t * f x * t⁻¹ := by
    have hx : inclusion hLH (τ x) = tH * inclusion hLH x * tH⁻¹ := Subtype.ext rfl
    change φ (q (inclusion hLH (τ x))) =
      φ (q tH) * φ (q (inclusion hLH x)) * (φ (q tH))⁻¹
    rw [hx]
    simp only [map_mul, map_inv]
  have hodd : t.sign ≠ 1 := by
    intro he
    have hn (a : L₁) (heq : QuotientGroup.mk' (pCore 2 L₁) a =
        (QuotientGroup.mk' (pCore 2 L₁) a)⁻¹) :
        QuotientGroup.mk' (pCore 2 L₁) a = 1 := by
      have h2 : (QuotientGroup.mk' (pCore 2 L₁) a) ^ 2 = 1 :=
        (pow_two _).trans (eq_inv_iff_mul_eq_one.mp heq)
      have h3 := CubicParity.quotient_cube d.quotient (QuotientGroup.mk' (pCore 2 L₁) a)
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul] at h3
      exact h3
    rcases CubicParity.even_scalar_quotient d.quotient f hk hf τ t ht he ha with hfix | hinv
    · obtain ⟨a, haX, hne⟩ := exists_nontrivial_quotient_element L₁ X d.second_card
      exact hne (hn a ((hfix a).symm.trans (d.inverts_second a haX)))
    · obtain ⟨a, haL, hne⟩ := exists_nontrivial_quotient_element L₁ L₀ d.first_card
      exact hne (hn a ((d.fixes_first a haL).symm.trans (hinv a)))
  rcases LocalGeometry.PermutationOvergroups.ambient_cases φ.range hAlt with h | h
  · exact MonoidHom.range_eq_top.mp h
  · have hm : t ∈ alternatingGroup (Fin 7) := h ▸ (show t ∈ φ.range from ⟨q tH, rfl⟩)
    exact (hodd (Perm.mem_alternatingGroup.mp hm)).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
