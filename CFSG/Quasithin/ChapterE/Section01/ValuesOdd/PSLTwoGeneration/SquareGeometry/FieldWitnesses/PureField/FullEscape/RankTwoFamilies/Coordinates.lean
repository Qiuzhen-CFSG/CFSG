module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.FieldCentralizer

/-!
# Marked coordinates for mixed rank-two actors

Projective Hilbert–90 straightens an involution with nontrivial field image
by conjugation in the actual PGL₂ subgroup. The marked field-centralizer
map then splits the actor into its fixed-field linear part and the pure
field factor. Cardinalities show that the linear part of a four-group has
order two, giving an actual involution in PGL₂ of the fixed field.

The result keeps the exact conjugating element and supplied field
involution, so `RankTwoFamilies` can transport the whole family, Sylow and
overgroup together. No local E-member or escape is asserted by this calculation.
It applies also in characteristics three and five.

Source: Aschbacher–Smith, A.2.3(2), E.1.2 and E.1.14(6), printed pp.33,
209–210 and 214. The Hilbert–90 input is the proved matrix theorem
`projective_semilinear_involution_conj_inr`.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies
variable {F : Type*} [Field F] [Finite F]

/-- An elementary actor containing the pure field involution splits over its
actual fixed-field linear preimage. -/
theorem pure_actor_split {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ 2)
    (σ : F ≃+* F) (hne : σ ≠ 1) (A : Subgroup (PGammaL2 F))
    (hA : IsElementaryAbelian 2 A) (hσA : SemidirectProduct.inr σ ∈ A) :
    A = (A.comap (subfieldEmbedding σ)).map (subfieldEmbedding σ) ⊔
      zpowers (SemidirectProduct.inr σ) := by
  let := hA
  have hCA : zpowers (SemidirectProduct.inr σ) ≤ A := zpowers_le.mpr hσA
  apply le_antisymm
  · intro x hx
    have hxc : x ∈ centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F)) :=
      ((Subgroup.le_centralizer A).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hσA))) hx
    obtain ⟨b, hb⟩ := (mem_fieldCentralizer_iff hp hF σ hne x).mp hxc
    have hr : (SemidirectProduct.inr x.right : PGammaL2 F) ∈
        zpowers (SemidirectProduct.inr σ) := by
      rcases fieldAut_eq_one_or hp hF σ hne x.right with h | h
      · rw [h, map_one]; exact one_mem _
      · rw [h]; exact mem_zpowers _
    have he : subfieldEmbedding σ b * SemidirectProduct.inr x.right = x := by
      change SemidirectProduct.inl _ * SemidirectProduct.inr x.right = x
      rw [hb, SemidirectProduct.inl_left_mul_inr_right]
    have hba : subfieldEmbedding σ b ∈ A := by
      rw [← he] at hx
      exact (A.mul_mem_cancel_right (hCA hr)).mp hx
    rw [← he]
    exact mul_mem_sup (mem_map_of_mem _ hba) hr
  · exact sup_le (map_comap_le _ _) hCA

variable [Finite (PGammaL2 F)]

/-- The fixed-field factor of a rank-two actor containing σ is generated
by an actual projective involution. -/
theorem pure_rank_two_coordinates {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ 2)
    (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1)
    (A : Subgroup (PGammaL2 F)) (hA : IsElementaryAbelian 2 A)
    (hσA : SemidirectProduct.inr σ ∈ A) (hr : Group.rank A = 2) :
    ∃ b : PGL2 (FixedPoints.subfield (zpowers σ) F), orderOf b = 2 ∧
      A = (zpowers b).map (subfieldEmbedding σ) ⊔
        zpowers (SemidirectProduct.inr σ) := by
  classical
  let := hA
  let B := A.comap (subfieldEmbedding σ)
  let D := B.map (subfieldEmbedding σ)
  let C : Subgroup (PGammaL2 F) := zpowers (SemidirectProduct.inr σ)
  have hDA : D ≤ A := map_comap_le _ _
  have hCA : C ≤ A := zpowers_le.mpr hσA
  have he : A = D ⊔ C := pure_actor_split hp hF σ hne A hA hσA
  have hCD : C ≤ centralizer (D : Set (PGammaL2 F)) :=
    hCA.trans ((Subgroup.le_centralizer A).trans (Subgroup.centralizer_le hDA))
  have hDC : Disjoint D C := by
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    rintro x ⟨hxD, hxC⟩
    have hxr : x.right = 1 := by
      obtain ⟨b, _, rfl⟩ := hxD
      rfl
    obtain ⟨z, rfl⟩ := mem_zpowers_iff.mp hxC
    have hz : σ ^ z = 1 := by
      simpa only [← map_zpow, SemidirectProduct.right_inr] using hxr
    apply mem_bot.mpr
    rw [← map_zpow, hz, map_one]
  have hsc : Nat.card C = 2 := by
    rw [Nat.card_zpowers, orderOf_injective SemidirectProduct.inr
      SemidirectProduct.inr_injective]
    exact (orderOf_eq_prime_iff (x := σ)).mpr ⟨hsq, hne⟩
  have hac : Nat.card A = 4 := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have hrn : Group.rank A = n := le_antisymm
      (IsElementaryAbelian.rank_le_of_card_le A hn.le)
      (IsElementaryAbelian.rank_ge_of_card hn)
    simpa [← hrn, hr] using hn
  have hdc : Nat.card D = 2 := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint D C
      (hCD.trans (centralizer_le_normalizer D)) hDC
    rw [← he, hac, hsc] at hh
    omega
  have hbc : Nat.card B = 2 :=
    (Nat.card_congr (B.equivMapOfInjective _ (subfieldEmbedding_injective σ)).toEquiv).trans hdc
  obtain ⟨b, hbne, huniq⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hbc
  have hbe : B = zpowers (b : PGL2 (FixedPoints.subfield (zpowers σ) F)) := by
    apply le_antisymm
    · intro x hx
      by_cases hx1 : (⟨x, hx⟩ : B) = 1
      · have hh : x = 1 := congrArg Subtype.val hx1
        rw [hh]; exact one_mem _
      · have hh : x = b := congrArg Subtype.val (huniq ⟨x, hx⟩ hx1)
        rw [hh]; exact mem_zpowers _
    · exact zpowers_le.mpr b.property
  refine ⟨b, ?_, ?_⟩
  · have hbpow : (b : PGL2 (FixedPoints.subfield (zpowers σ) F)) ^ 2 = 1 := by
      apply subfieldEmbedding_injective σ
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian _ b.property
    apply (orderOf_eq_prime_iff (x := (b : PGL2 (FixedPoints.subfield (zpowers σ) F)))).mpr
    exact ⟨hbpow, fun h => hbne (Subtype.ext h)⟩
  · simpa only [D, hbe] using he

/-- Every rank-two actor outside the linear kernel has these marked
coordinates after a projectively linear conjugation. The supplied σ is retained. -/
theorem mixed_rank_two_coordinates {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1)
    (A : Subgroup (PGammaL2 F)) (hA : IsElementaryAbelian 2 A)
    (hr : Group.rank A = 2) (hlinear : ¬ A ≤ pGammaL2PGLRange F) :
    ∃ (c : PGL2 F) (b : PGL2 (FixedPoints.subfield (zpowers σ) F)),
      orderOf b = 2 ∧
      A.map (MulAut.conj (SemidirectProduct.inl c : PGammaL2 F)⁻¹).toMonoidHom =
        (zpowers b).map (subfieldEmbedding σ) ⊔ zpowers (SemidirectProduct.inr σ) := by
  classical
  let := hA
  obtain ⟨x, hxA, hxL⟩ := SetLike.not_le_iff_exists.mp hlinear
  have hxfield : x.right ≠ 1 := by
    intro h
    apply hxL
    rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom]
    exact h
  have hxo : orderOf x = 2 := (orderOf_eq_prime_iff (x := x)).mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian x hxA,
      fun h => hxfield (by rw [h]; rfl)⟩
  have hxσ : x.right = σ := (fieldAut_eq_one_or hp hF σ hne x.right).resolve_left hxfield
  obtain ⟨c, hc⟩ := projective_semilinear_involution_conj_inr
    ⟨p, 2, hp, hodd, by decide, hF⟩ x hxo hxfield
  let e := MulAut.conj (SemidirectProduct.inl c : PGammaL2 F)⁻¹
  have hex : e x = SemidirectProduct.inr σ := by
    simpa only [e, MulAut.conj_apply, inv_inv, hxσ] using hc
  have hσB : SemidirectProduct.inr σ ∈ A.map e.toMonoidHom :=
    hex ▸ mem_map_of_mem e.toMonoidHom hxA
  have hrB : Group.rank (A.map e.toMonoidHom) = 2 :=
    (Group.rank_congr (A.equivMapOfInjective e.toMonoidHom e.injective)).symm.trans hr
  obtain ⟨b, hb, hB⟩ := pure_rank_two_coordinates hp hF σ hsq hne
    (A.map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom) hσB hrB
  exact ⟨c, b, hb, hB⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies
