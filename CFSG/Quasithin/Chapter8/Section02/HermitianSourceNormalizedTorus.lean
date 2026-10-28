module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusBounds
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.NormalizedActor
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusBounds

/-!
# The selected torus needs no additional parabolic marking

The selected core actor has rank greater than 3n in the intermediate
range. It therefore lies in the original inner Hermitian image, and its
normalization by the selected torus supplies the natural parabolic exponent.
This removes the preserved-parabolic premise from the intermediate exclusion.
E.2.14's rank implication also forces k ≤ 2n from the actual automizer rank.
The rank-one module degree and the earlier E.2.14 inputs remain explicit.

Source: Aschbacher–Smith 8.2.3, printed pp.715–716 (1 March 2004
manuscript, refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

/-- The original selected actor and torus exclude the intermediate range.
Only the literal fixed-space and rank-one degree inputs remain. -/
theorem selected_not_intermediate_of_normalizing_torus
    (s : Selected H T M V I k i S) (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V)
    (x : Automizer V) (ho : orderOf x = 2^k-1)
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hx : x ∈ inducedAutomizer V (M ⊓ I))
    (hd : k ∣ rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) ∨ Odd k)
    (hnk : n < k) (hkn : k < 2*n) : False := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (selected_actor_normalizes s)
  have hrank : primeRank 2 (Automizer V) ≤ 4*n :=
    (primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n) ⟨FieldSections.centralizerEquiv n⟩)
  have hdim : rank V = 9*n := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hf := fixedGroup_rank (V := V) (zpowers x)
  rw [hfixed] at hf
  have hm : Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (zpowers x)) =
      Module.finrank (ZMod 2)
        (fixedSpace (overgroupAction n (binaryNormalizer n)) (zpowers (j x))) := by
    rw [← MonoidHom.map_zpowers,
      ← fixedSpace_map_equivariant (automizerRepresentation V)
        (overgroupAction n (binaryNormalizer n)) j e he,LinearEquiv.finrank_map_eq]
  have hlarge := selected_fixed_rank_gt_three_mul s n hdim hrank hkn x hfixed
  have hodd : Odd (orderOf x) := by
    rw [ho]
    exact Nat.Even.sub_odd (Nat.one_le_pow k 2 (by decide))
      (Nat.even_pow.mpr ⟨by decide,by omega⟩) odd_one
  have hoj : Odd (orderOf (j x)) := by rwa [orderOf_injective j hj]
  obtain ⟨hl,hdegree⟩ := largeOddFixedSpaceLinearity n (binaryNormalizer n) (j x)
    (j x).property hoj (hm ▸ hlarge)
  let f := (binaryNormalizer n).subtype.comp j
  let B := (inducedAutomizer V A).map f
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hsum := (selected_actor_fixedCodim_ge_five_mul s n e j hj he hr hkn).2
  change 5*n ≤ k + rank (inducedAutomizer V A) at hsum
  have hfi : Function.Injective f := (binaryNormalizer n).subtype_injective.comp hj
  have hBr : 2*n+1 < rank B := by
    rw [rank_map_injective f hfi]
    have hn := NeZero.pos n
    omega
  have hBN : B ≤ binaryNormalizer n := by
    rintro _ ⟨b,hb,rfl⟩
    exact (j b).property
  have hBL := Chapter7.NormalizedSource.NonMathieuHermitian.large_elementary_le_image n B hBN hBr
  have hnorm : (j x).val ∈ normalizer (B : Set (BinaryAut n)) :=
    (inducedAutomizer V A).le_normalizer_map f
      (mem_map_of_mem f (selected_normalizes_actor s hx))
  have hexd := odd_order_dvd_of_large_inner_actor n B hBL (by omega)
    (j x).val (j x).property (by rwa [Subgroup.orderOf_coe]) hl hnorm
  rw [Subgroup.orderOf_coe,orderOf_injective j hj,ho] at hexd
  have hkdiv := (Offenders.pow_sub_one_dvd_pow_sub_one_iff_dvd (by omega : 0 < k)).mp hexd
  rw [← hm,← hf] at hdegree
  have hid := selected_actor_rank_identity s
  rw [hdim] at hid
  have hsum : n ∣ rank (V ⊓ W) + (k + rank (inducedAutomizer V A)) := by
    rw [← Nat.add_assoc]
    exact hid ▸ dvd_mul_left n 9
  have hfixeddiv : n ∣ k + rank (inducedAutomizer V A) :=
    (Nat.dvd_add_iff_right hdegree).mpr hsum
  have hupper := (offender_rank_le_primeRank (inducedAutomizer V A)).trans hrank
  exact Nat.BinaryParabolicRank.false_of_intermediate_parameters hnk hkn hkdiv hupper
    (selected_actor_fixedCodim_ge_five_mul s n e j hj he hr hkn).2 hd hfixeddiv

/-- E.2.14's rank implication and the actual automizer bound already force
k ≤ 2n; no separate bound on the ambient generation parameter is needed. -/
theorem selected_parameter_le_two_mul
    (K : GroupClass) (eR : E214RankClause (G := G) K)
    (h28 : HypothesisE28 K H T M V) (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H M V) (s : Selected H T M V I k i S)
    (n : ℕ) [NeZero n]
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j) : k ≤ 2*n := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (selected_actor_normalizes s)
  have hrank : primeRank 2 (Automizer V) ≤ 4*n :=
    (primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n) ⟨FieldSections.centralizerEquiv n⟩)
  have hupper := (offender_rank_le_primeRank (inducedAutomizer V A)).trans hrank
  by_contra! hk
  have heq := eR H T M V I k h28 s.family hchar hTI i s.generate
    s.intersection_ne_bot s.quadraticRatio_gt_one (show rank (inducedAutomizer V A) ≤ 2*k by omega)
  change rank (inducedAutomizer V A) = 2*k at heq
  omega

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
