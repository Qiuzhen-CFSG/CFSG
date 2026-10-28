module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneRank
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Suzuki.Ratios
public import Theory.Representation.BinaryOffender.InnerNormalizerActors
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module

/-!
# Fixed-space bounds for the full Suzuki normalizer

Suzuki involutory automorphisms are inner, with square-one representatives.
Binary Schur's lemma identifies every elementary actor of the full linear
normalizer with an elementary subgroup of the marked component. The natural
model's fixed codimension therefore applies to all normalizer actors, and
to each faithfully marked ambient automizer. This proves the Suzuki local
m-bound used before the ambient centralizer arguments in Section 7.3.

Source: Aschbacher--Smith, K.3.6 and Table 7.2.1, printed pp.457,698.
-/

open Subgroup Representation Representation.BinaryOffender
open BenderSuzuki BenderSuzuki.MatrixGroups

public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource
variable {G E : Type*} [Group G]
  [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) G E} {Q : Subgroup G}

private theorem suzuki_involutoryAut_inner {m : ℕ} (hm : 1 ≤ m)
    (M : ChapterK.RankOne.SuzukiModel m ρ Q)
    (a : MulAut Q) (ha : a ^ 2 = 1) :
    ∃ x : Q, x ^ 2 = 1 ∧ a = MulAut.conj x := by
  have hb : (MulAut.congr M.groupEquiv a) ^ 2 = 1 := by
    rw [← map_pow, ha, map_one]
  obtain ⟨x, hx, _⟩ := ZD.suzuki_involutoryAut_inner_and_twoRank m hm
    (MulAut.congr M.groupEquiv a) hb
  have hx2 := ZD.suzuki_conj_sq_eq_one m hm x (hx ▸ hb)
  refine ⟨M.groupEquiv.symm x, ?_, ?_⟩
  · rw [← map_pow, hx2, map_one]
  · apply (MulAut.congr M.groupEquiv).injective
    rw [MulAut.congr_conj, M.groupEquiv.apply_symm_apply]
    exact hx

/-- Every nontrivial elementary subgroup of the full linear normalizer has
the natural Suzuki fixed codimension. -/
theorem suzuki_normalizer_elementary_fixedCodim {m : ℕ} (hm : 1 ≤ m)
    (M : ChapterK.RankOne.SuzukiModel m ρ Q)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp Q.subtype))
    (A : Subgroup (linearNormalizer (ρ.comp Q.subtype))) (hA : IsElementaryTwo A) :
    fixedCodim (normalizerRepresentation (ρ.comp Q.subtype)) A = 2 * (2 * m + 1) := by
  let σ := ρ.comp Q.subtype
  obtain ⟨B, hB, hBA⟩ := elementary_normalizer_is_image σ
    (hf.comp Q.subtype_injective) hi (suzuki_involutoryAut_inner hm M) A hA
  have hC : IsElementaryTwo (B.map Q.subtype) := by
    let : IsElementaryAbelian 2 B := hB.2
    exact ⟨fun hz => hB.1 ((map_eq_bot_iff_of_injective B Q.subtype_injective).mp hz),
      IsElementaryAbelian.map _⟩
  have hd := fixedCodim_map_equivariant σ (normalizerRepresentation σ)
    (normalizerEmbedding σ) (LinearEquiv.refl _ _) (fun _ _ => rfl) B
  rw [hBA] at hd
  have he := fixedCodim_map_equivariant σ ρ Q.subtype
    (LinearEquiv.refl _ _) (fun _ _ => rfl) B
  exact hd.symm.trans (he.trans (M.elementary_fixedCodim hm hC (map_subtype_le B)))

variable {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]

/-- Transport the full-normalizer calculation through an injective marking
of the actual actor and its complete action. -/
theorem suzuki_fixedCodim_of_normalizer_marking {m : ℕ} (hm : 1 ≤ m)
    (M : ChapterK.RankOne.SuzukiModel m ρ Q)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp Q.subtype))
    (τ : Representation (ZMod 2) X W)
    (j : X →* linearNormalizer (ρ.comp Q.subtype)) (hj : Function.Injective j)
    (e : E ≃ₗ[ZMod 2] W)
    (he : ∀ a v, e (normalizerRepresentation (ρ.comp Q.subtype) (j a) v) = τ a (e v))
    (A : Subgroup X) (hA : IsElementaryTwo A) :
    fixedCodim τ A = 2 * (2 * m + 1) := by
  have hB : IsElementaryTwo (A.map j) := by
    let : IsElementaryAbelian 2 A := hA.2
    exact ⟨fun hz => hA.1 ((map_eq_bot_iff_of_injective A hj).mp hz),
      IsElementaryAbelian.map _⟩
  have hcoord (a : X) (v : W) :
      e.symm (τ a v) = normalizerRepresentation (ρ.comp Q.subtype) (j a) (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  exact (fixedCodim_map_equivariant τ (normalizerRepresentation (ρ.comp Q.subtype))
    j e.symm hcoord A).trans (suzuki_normalizer_elementary_fixedCodim hm M hf hi _ hB)

/-- The Suzuki local involution parameter is at least 2(2m+1). The odd-order
fallback in the definition is covered by the natural module dimension. -/
theorem suzuki_moduleM_of_normalizer_marking {m : ℕ} (hm : 1 ≤ m)
    (M : ChapterK.RankOne.SuzukiModel m ρ Q)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp Q.subtype))
    (τ : Representation (ZMod 2) X W)
    (j : X →* linearNormalizer (ρ.comp Q.subtype)) (hj : Function.Injective j)
    (e : E ≃ₗ[ZMod 2] W)
    (he : ∀ a v, e (normalizerRepresentation (ρ.comp Q.subtype) (j a) v) = τ a (e v)) :
    2 * (2 * m + 1) ≤ ChapterE.moduleM τ := by
  apply le_csInf ⟨_, Set.mem_insert _ _⟩
  rintro d (rfl | ⟨t, ht, rfl⟩)
  · rw [← e.finrank_eq, M.finrank_eq]
    omega
  · have hA : IsElementaryTwo (zpowers t) :=
      ⟨fun hb => by
          have ht1 := mem_bot.mp (hb ▸ mem_zpowers t)
          simp [ht1] at ht,
        IsElementaryAbelian.zpowers_of_pow_eq_one ((orderOf_eq_prime_iff.mp ht).1)⟩
    exact (suzuki_fixedCodim_of_normalizer_marking hm M hf hi τ j hj e he _ hA).ge

end CFSG.Quasithin.Chapter7.NormalizedSource
