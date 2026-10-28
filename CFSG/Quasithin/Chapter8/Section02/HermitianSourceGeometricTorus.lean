module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceNormalizedTorus
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.FixedPlaneExponent
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusBounds

/-!
# The selected Hermitian torus has a split exponent

The original r-bound makes the selected core actor large, while its central
intersection makes the torus fixed space larger than 3n. The checked point
fixed-space bound forces the plane geometry. Fixed-field linearity and the
pointwise plane exponent now give 2^k-1 dividing 2^(2n)-1, contradicting
n < k < 2n. This removes both the actor-degree disjunction and the separate
torus-normalization premise from the intermediate exclusion.

The original selected pair and its torus fixed-space identity remain explicit.
The Chapter 12 application supplies the literal chosen action and r-bound.
Selection, earlier E.2.14 inputs and the field-four endgame are separate.

Source: Aschbacher–Smith 8.2.3, printed pp.715–716, using H.4.2–4
(1 March 2004 manuscript, refs/quasithin.pdf).
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

/-- The selected torus excludes the intermediate range directly from its
large fixed space, with no rank-one actor-degree premise. -/
theorem selected_not_intermediate_of_fixed_plane
    (s : Selected H T M V I k i S) (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V)
    (x : Automizer V) (ho : orderOf x = 2^k-1)
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hnk : n < k) (hkn : k < 2*n) : False := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (selected_actor_normalizes s)
  have hrank : primeRank 2 (Automizer V) ≤ 4*n :=
    (Theory.GroupTheory.primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n) ⟨FieldSections.centralizerEquiv n⟩)
  have hdim : rank V = 9*n := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hm : Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (zpowers x)) =
      Module.finrank (ZMod 2)
        (fixedSpace (overgroupAction n (binaryNormalizer n)) (zpowers (j x))) := by
    rw [←MonoidHom.map_zpowers,
      ←fixedSpace_map_equivariant (automizerRepresentation V)
        (overgroupAction n (binaryNormalizer n)) j e he,LinearEquiv.finrank_map_eq]
  have hlarge := selected_fixed_rank_gt_three_mul s n hdim hrank hkn x hfixed
  have hodd : Odd (orderOf x) := by
    rw [ho]
    exact Nat.Even.sub_odd (Nat.one_le_pow k 2 (by decide))
      (Nat.even_pow.mpr ⟨by decide,by omega⟩) odd_one
  have hoj : Odd (orderOf (j x)) := by rwa [orderOf_injective j hj]
  obtain ⟨hl,_⟩ := largeOddFixedSpaceLinearity n (binaryNormalizer n) (j x)
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
  have hmap (D : Subgroup (Automizer V)) :
      (fixedSpace (automizerRepresentation V) D).map e.toLinearMap =
        fixedSpace (UnipotentRadicals.ambientAction n) (D.map f) :=
    fixedSpace_map_equivariant _ _ f e he D
  have hX : (zpowers x).map f = zpowers (j x).val := MonoidHom.map_zpowers f x
  have hBX : 3*n < Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (j x).val)) := by
    rw [←hX,←hmap,LinearEquiv.finrank_map_eq]
    exact hlarge
  have hle : fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (j x).val) ≤
      fixedSpace (UnipotentRadicals.ambientAction n) B := by
    rw [←hX,←hmap,←hmap]
    exact Submodule.map_mono (selected_fixedSpace_le_actor s x hfixed)
  obtain ⟨g,hg⟩ := OddExponent.mem_congruenceImage_of_odd_of_isFixedFieldLinear n
    (j x).val (j x).property (by rwa [Subgroup.orderOf_coe]) hl
  have hd := odd_order_dvd_of_large_fixed_inside_inner_actor n B hBL (by omega) g
    (by rwa [hg,Subgroup.orderOf_coe]) (by rwa [hg]) (by rwa [hg])
  rw [hg,Subgroup.orderOf_coe,orderOf_injective j hj,ho] at hd
  have hkdiv := (Offenders.pow_sub_one_dvd_pow_sub_one_iff_dvd (by omega : 0 < k)).mp hd
  obtain ⟨d,hd⟩ := hkdiv
  have hlo : 2 ≤ d := by nlinarith
  nlinarith
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
