module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockLinearThreeRadical
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockLinearThreeAction
public import Theory.SpecificGroups.SL3.RadicalPerfectNormalizer
/-!
# Recognition of the original L-image in the SL₃ block quotient

The original L-image is nontrivial and perfect. It normalizes the actual
radical intersection, whose full normalizer lies in the source local
intersection and therefore normalizes L. The intrinsic SL₃ radical theorem
then marks this normalizer and the L-image as a parabolic and its residual,
using one linear change of basis. All maps retain K ≤ H ≤ G and the full
quotient K/O₂(K), including its possible odd centre.

The large-order placement follows from the quotient isomorphism alone;
this also makes the marking available before the C.4.1 module classification.
The following block contradiction transports the natural module in this
same basis and discharges the formerly explicit placement premise.
Source: Aschbacher–Smith C.4.5–7 and original 4.3.7, pp.152–153,615–616.
-/

public section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC Chapter1.RadicalExclusions.ModelReduction
open FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
private theorem star_normalizes (K R A B : Subgroup G)
    (hAB : A ≤ normalizer (B : Set G)) :
    starImage K R A ≤ normalizer (starImage K R B : Set (StarQuotient K R)) := by
  exact (map_mono ((comap_mono hAB).trans (B.le_normalizer_comap (K ⊔ R).subtype))).trans
    ((B.subgroupOf (K ⊔ R)).le_normalizer_map _)

/-- The original L image normalizes the actual radical intersection in K*. -/
theorem SourceConfiguration.block_star_L_le_radical_normalizer
    (c : SourceConfiguration T L) :
    (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) L).subgroupOf
        (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)) ≤
      normalizer (((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.I.pCoreIn 2)).subgroupOf
        (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) :
          Set (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) := by
  have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  have hLR : L ≤ normalizer (c.I.pCoreIn 2 : Set G) := by
    simpa only [hs] using c.c28.span_normalizes_radical
  exact (comap_mono (star_normalizes _ _ _ _ hLR)).trans
    ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.I.pCoreIn 2)).le_normalizer_comap _)

omit [Finite G] in
/-- The actual local intersection normalizes the original L image, before
any model identification or parabolic classification. -/
theorem SourceConfiguration.block_star_local_normalizes_L
    (c : SourceConfiguration T L) :
    (starM (c.K.map c.H.subtype) (c.I.pCoreIn 2)
      (c.H ⊓ normalizer (L : Set G))).subgroupOf
        (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)) ≤
      normalizer (((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) L).subgroupOf
        (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) :
          Set (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) := by
  exact (comap_mono (star_normalizes _ _ _ _ (inf_le_left.trans inf_le_right))).trans
    ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) L).le_normalizer_comap _)
/-- In the full special-linear quotient, its actual order supplies the large
C.2.7 placement premise. No natural-module classification is needed here. -/
theorem SourceConfiguration.block_sl3_radical_placement_of_equiv
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2^n)
    (e₀ : (c.K ⧸ pCore 2 c.K) ≃* SL(3,F)) :
    IsPRadical 2
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.I.pCoreIn 2)).subgroupOf
        (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) ∧
      normalizer
        (((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.I.pCoreIn 2)).subgroupOf
          (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) :
          Set (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) ≤
        (starM (c.K.map c.H.subtype) (c.I.pCoreIn 2)
          (c.H ⊓ normalizer (L : Set G))).subgroupOf
            (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)) := by
  have he : (c.K.map c.H.subtype).subgroupOf c.H = c.K :=
    c.K.comap_map_eq_self_of_injective c.H.subtype_injective
  let : ((c.K.map c.H.subtype).subgroupOf c.H).Normal := he.symm ▸ c.component_normal
  apply C27Source.star_intersection_placement_of_large_order (c.block_source_input hf)
  rw [←Nat.card_congr (c.block_star_quotientEquiv hb).toEquiv,
    Nat.card_congr e₀.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  have h3 : 64 ≤ Nat.card F ^ 3 := by simpa using Nat.pow_le_pow_left hq 3
  have h2 : 16 ≤ Nat.card F ^ 2 := by simpa using Nat.pow_le_pow_left hq 2
  have hm := Nat.mul_le_mul
    (Nat.mul_le_mul h3 (Nat.sub_le_sub_right h3 1)) (Nat.sub_le_sub_right h2 1)
  exact lt_of_lt_of_le (by norm_num : 40320 < 64 * (64 - 1) * (16 - 1)) hm

/-- The full quotient model admits natural coordinates in which the original
L-image is a parabolic residual. No placement assumption is supplied. -/
theorem SourceConfiguration.block_linearThree_local_frame
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (hb : IsBlock c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2^n)
    (e₀ : (c.K ⧸ pCore 2 c.K) ≃* SL(3,F)) :
    ∃ e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F),
      c.componentQuotientL.map
          (e₀.trans (Matrix.HigherLinear.SubspaceTransport.slConj e)).toMonoidHom =
        Matrix.PSL3.LinearThree.pointLocalSL F ∨
      c.componentQuotientL.map
          (e₀.trans (Matrix.HigherLinear.SubspaceTransport.slConj e)).toMonoidHom =
        Matrix.PSL3.LinearThree.lineLocalSL F := by
  let C := starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)
  let R := (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.I.pCoreIn 2)).subgroupOf C
  let B := (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) L).subgroupOf C
  let E := (c.block_star_quotientEquiv hb).symm.trans e₀
  have hB : c.componentQuotientL.map (c.block_star_quotientEquiv hb).toMonoidHom = B :=
    c.componentQuotientL_star hb
  let : Group.IsPerfect c.componentQuotientL := c.componentQuotientL_perfect
  let : Group.IsPerfect B := hB ▸ Group.IsPerfect.map (c.block_star_quotientEquiv hb).toMonoidHom
  have hBne : B ≠ ⊥ := fun he => c.componentQuotientL_ne_bot
    ((map_eq_bot_iff_of_injective _ (c.block_star_quotientEquiv hb).injective).mp (hB.trans he))
  have hp := c.block_sl3_radical_placement_of_equiv hn hf hb hF e₀
  have hBN := c.block_star_L_le_radical_normalizer
  have hNB := hp.2.trans c.block_star_local_normalizes_L
  let B' := B.map E.toMonoidHom
  let R' := R.map E.toMonoidHom
  let : Group.IsPerfect B' := Group.IsPerfect.map E.toMonoidHom
  have hB' : B' ≠ ⊥ := fun he => hBne ((B.map_eq_bot_iff_of_injective E.injective).mp he)
  have hBR : B' ≤ normalizer (R' : Set SL(3,F)) := by
    rw [←map_equiv_normalizer_eq R E]
    exact map_mono hBN
  have hRB : normalizer (R' : Set SL(3,F)) ≤ normalizer (B' : Set SL(3,F)) := by
    rw [←map_equiv_normalizer_eq R E,←map_equiv_normalizer_eq B E]
    exact map_mono hNB
  obtain ⟨e,he⟩ := Matrix.PSL3.LinearThree.RadicalNormalizer.radical_perfect_normal_frame
    R' B' (hp.1.map_equiv E) hB' hBR hRB hn hF
  have hBE : B' = c.componentQuotientL.map e₀.toMonoidHom := by
    change B.map E.toMonoidHom = c.componentQuotientL.map e₀.toMonoidHom
    rw [←hB]
    have hhom : E.toMonoidHom.comp (c.block_star_quotientEquiv hb).toMonoidHom =
        e₀.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact congrArg e₀ ((c.block_star_quotientEquiv hb).symm_apply_apply x)
    rw [Subgroup.map_map, hhom]
  refine ⟨e,?_⟩
  have hh : c.componentQuotientL.map
      (e₀.trans (Matrix.HigherLinear.SubspaceTransport.slConj e)).toMonoidHom =
      B'.map (Matrix.HigherLinear.SubspaceTransport.slConj e).toMonoidHom := by
    rw [hBE]
    have hhom : (e₀.trans (Matrix.HigherLinear.SubspaceTransport.slConj e)).toMonoidHom =
        (Matrix.HigherLinear.SubspaceTransport.slConj e).toMonoidHom.comp e₀.toMonoidHom := rfl
    rw [hhom]
    exact (Subgroup.map_map c.componentQuotientL
      (Matrix.HigherLinear.SubspaceTransport.slConj e).toMonoidHom e₀.toMonoidHom).symm
  rw [hh]
  exact he.imp And.right And.right

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
