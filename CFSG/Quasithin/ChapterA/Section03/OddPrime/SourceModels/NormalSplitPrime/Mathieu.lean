module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.TwoCore
public import Theory.Mathieu.M22.TripleCoverLocalRank
public import Theory.GroupTheory.CComponent.HexacodeTheta.InnerAction
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Mathieu.TwentyTwoReduction
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage

/-!
# Excluding the actual Mathieu triple cover from the split domain

The preimage of the native hexad A₆ section has order 1080 and contains a
Sylow three-subgroup of the covering group. The checked exponent-three
calculation for arbitrary central cubic A₆ extensions excludes order nine
in this preimage, hence throughout the original cover by Sylow conjugacy.
Perfect central descent embeds its outer group in the two-group Out(M₂₂).
An outside cubic would therefore be inner; correcting its implementer gives
an outside centralizing cubic and an elementary group of order 27.

The final application uses the actual ordinary component in H/O₂(H), with
its center and quotient map retained. Neither recognition of the cover as a
particular ATLAS realization nor a full cover catalogue is needed. Source:
Aschbacher–Smith A.3.18, printed pp.52–53; A₆ and M₂₂ covering calculations
reuse their original GLS3 and ATLAS attribution in the imported modules.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Chapter1.Section02.LocalModels Sporadic.Mathieu
open GLS3.Chapter5.OddCentralCovers

private theorem mathieu_cover_cube_eq_one_of_ninth
    {E : Type*} [Group E] [Finite E]
    (e : E ⧸ center E ≃* M22) (hc : Nat.card (center E) = 3)
    (x : E) (hx : x ^ 9 = 1) : x ^ 3 = 1 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = center E := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  obtain ⟨P,q,hq,hqc,hqk⟩ := CubicCoverPreimage.exists_restriction f hf hker.le
    hexadAlternatingSixEmbedding hexadAlternatingSixEmbedding_injective
  have hk : Nat.card q.ker = 3 := hqk.trans (hker ▸ hc)
  have hPcard : Nat.card P = 1080 := by
    rw [q.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv,hk,
      nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  have hGcard : Nat.card E = 1330560 := by
    rw [f.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      hker, hc, m22_order]
  let T : Sylow 3 P := default
  let Q := (T : Subgroup P).map P.subtype
  have hQcard : Nat.card Q = 27 := by
    rw [card_map_of_injective P.subtype_injective,Sylow.card_eq_multiplicity,hPcard]
    decide +kernel
  have hQp : IsPGroup 3 Q := T.isPGroup'.map P.subtype
  let S : Sylow 3 E := hQp.toSylow (by
    have hh := Q.card_mul_index
    rw [hQcard,hGcard] at hh
    have hi : Q.index = 49280 := by omega
    rw [hi]
    decide)
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 2) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx)
  obtain ⟨T',hT'⟩ := hp.exists_le_sylow
  let y : T' := ⟨x,hT' (mem_zpowers x)⟩
  let e := T'.equiv S
  let z : P := ⟨e y,map_subtype_le _ (e y).property⟩
  have hz9 : z ^ 9 = 1 := by
    apply Subtype.ext
    exact congrArg (fun t : S => (t : E)) (show e y ^ 9 = 1 from by
      rw [←map_pow,show y ^ 9 = 1 from Subtype.ext hx,map_one])
  have hz3 := central_six_cube_eq_one_of_ninth q hq hqc hk z hz9
  have hy3 : y ^ 3 = 1 := e.injective (by
    rw [map_pow,map_one]
    exact Subtype.ext (congrArg (fun t : P => (t : E)) hz3))
  exact congrArg Subtype.val hy3
/-- The cubic Mathieu cover absorbs every cubic in the original rank-two
ambient group. The exponent bound is proved from the actual A₆ preimage. -/
theorem ordinary_not_mathieu_cover
    {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    (hr : 1 < primeRank 3 K)
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) : ¬ IsM22Cover K := by
  rintro ⟨_, ⟨ez⟩, ⟨e⟩⟩
  have hc : Nat.card (center K) = 3 := (Nat.card_congr ez.toEquiv).trans (by simp)
  have hout : IsPGroup 2 (MulAut.Outer K) :=
    (Chapter1.XiEmbedding.OuterModels.m22_outer_isPGroup_two_of_coverage
      m22DesignAutToAut_surjective).of_injective (MulAut.centralQuotientOuter e)
        (MulAut.centralQuotientOuter_injective e)
  apply haK
  apply HexacodeTheta.order_three_mem_of_normal K ?_
    (mathieu_cover_cube_eq_one_of_ninth e hc) hout (by omega)
    (hH.stronglyQuasithin 3 Nat.prime_three (by decide)) (ha ▸ pow_orderOf_eq_one a)
  intro z hz
  have hh : (⟨z, hz⟩ : center K) ^ Nat.card (center K) = 1 := pow_card_eq_one'
  rw [hc] at hh
  exact congrArg Subtype.val hh

/-- The literal two-core image cannot be the Mathieu triple cover in this
split domain. No centerless replacement of the cover is used. -/
theorem not_mathieu_twoCore_cover
    {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hr : 1 < primeRank 3 K)
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) : ¬ IsM22Cover (twoCoreComponent K) := by
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  have hr' : 1 < primeRank 3 (twoCoreComponent K) := by
    rwa [twoCore_rank hK (by decide : Odd 3)]
  have ha' := twoCore_actor Nat.prime_three (by decide) a ha haK
  exact ordinary_not_mathieu_cover (twoCore_sqtk hH) hr'
    (QuotientGroup.mk' (pCore 2 H) a) ha'.1 ha'.2

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
