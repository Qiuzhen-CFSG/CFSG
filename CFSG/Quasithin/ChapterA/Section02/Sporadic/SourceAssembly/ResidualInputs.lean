module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
public import Theory.GroupTheory.GeneralizedFitting.LayerImages
public import Theory.SpecificGroups.McLaughlin.Multiplier.FivePrimary.Source
public import Theory.SpecificGroups.ONan.ThreeCoverLocalLifts
public import Theory.SpecificGroups.ONan.E9A4.Embedding

/-!
# Exact model inputs for the remaining sporadic source branches

The ready Fi₂₂ quotient is composed with an actual Fi₂₃ or Fi₂₄′ centralizer
quotient. Semisimplicity of the fixed U₆(2) carrier is enough to apply the
original proper-section induction hypothesis in Case II. Case I instead uses
the two-group kernels and the proved U₆(2) ordinary three-rank.

The McL leaf consumes the actual permutation-to-matrix carrier comparison.
The O'Nan leaf consumes a homomorphism from the actual linear model commuting
with the original central projection; all word-table and rank premises are
proved here from their existing producers. The final two source applications
retain precisely those independent model inputs. They do not claim that the
remaining quotient maps, semisimplicity, comparison or lift have been proved.

Source: Aschbacher–Smith A.2.19, printed pp.40–41. Independent model owners:
`qt-a02-sporadic-centralizers-fischer`, `qt-i01-multiplier-mcl`, and
`qt-a02-sporadic-odd-cover-local` / `qt-a02-sporadic-onan-odd-cover`.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
universe u v w
variable {G : Type u} {H : Type v} {T : Type w} [Group G] [Group H] [Group T]

public theorem proper_semisimple_section_rank_bound [Finite G]
    {K : GroupClass.{u}} (ih : TheoremsOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    (hs : IsSemisimple T) {M : Subgroup G}
    (hM : M ≠ ⊤) (hlocal : IsTwoLocal M) (hT : IsSectionOf T M)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) : primeRank p T ≤ 2 := by
  let : Finite T := hT.finite
  obtain ⟨U,f,hf⟩ := hT
  let e : (U ⧸ f.ker) ≃* T := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hs' : IsSemisimple (U ⧸ f.ker) :=
    componentLayer_eq_top_of_surjective e.symm.toMonoidHom e.symm.surjective hs
  have hl : primeRank p M ≤ 2 := isQuasithin_iff_twoLocal.mp hG M hlocal p hp ho
  have hb := ((ih.subgroup M hM).1 (hG.subgroup M) (hK.subgroup M)
    (U ⧸ f.ker) (.quotient_subgroup U f.ker) hs' p hp ho).2 hl
  exact (primeRank_equiv p e).symm ▸ hb.trans hl

public theorem false_of_cover_semisimple_quotient [Finite G] [IsQuasisimple G]
    {K : GroupClass.{u}} (ih : TheoremsOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    (e : G ⧸ center G ≃* H) (d : InvolutionCentralizerQuotientData H T)
    (hs : IsSemisimple T) (hr : 2 < primeRank 3 T) : False := by
  let π := projection e
  have hπ : Function.Surjective π := projection_surjective e
  let : Finite H := Finite.of_surjective π hπ
  have hsection : IsSectionOf T (centralizer ({d.involution} : Set H)) := by
    let e' := subgroupOfEquivOfLe d.centralizes
    exact ⟨d.numerator.subgroupOf _, d.quotientMap.comp e'.toMonoidHom,
      d.surjective.comp e'.surjective⟩
  obtain ⟨M,hM,hl,_,hT⟩ := EvenLie.exists_proper_twoLocal_section_lift π hπ
    (d.proper_centralizer (center_eq_bot_of_central_quotient e))
    (isTwoLocal_involution_centralizer d.involution_order) hsection
  exact (not_le_of_gt hr) (proper_semisimple_section_rank_bound ih hG hK hs hM hl hT 3
    (by decide) (by decide))

private lemma fi22_unitary_data_nonempty :
    Nonempty (InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi22.Carrier
      Theory.SpecificGroups.U6Two.Carrier) := by
  obtain ⟨t,L,f,ht,hL,hf,_⟩ := _root_.Sporadic.Fischer.Fi22.exists_unitary_section
  exact ⟨⟨t,ht,L,hL,f,hf⟩⟩

public noncomputable def fi22_unitary_data :
    InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi22.Carrier
      Theory.SpecificGroups.U6Two.Carrier := Classical.choice fi22_unitary_data_nonempty

public theorem cover_fi22_of_semisimple [Finite G] [IsQuasisimple G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.Fischer.Fi22.Carrier)
    (hs : IsSemisimple Theory.SpecificGroups.U6Two.Carrier) : False := by
  exact false_of_cover_semisimple_quotient ih hG hK e fi22_unitary_data hs
    (by have hh := Theory.SpecificGroups.U6Two.three_le_primeRank; omega)

public noncomputable def fischer_unitary_data
    (d : InvolutionCentralizerQuotientData H _root_.Sporadic.Fischer.Fi22.Carrier) :
    InvolutionCentralizerQuotientData H Theory.SpecificGroups.U6Two.Carrier := by
  let d' := d.restrictTarget fi22_unitary_data.numerator
  exact { d' with
    quotientMap := fi22_unitary_data.quotientMap.comp d'.quotientMap
    surjective := fi22_unitary_data.surjective.comp d'.surjective }

public theorem cover_fischer_of_quotient_data [Finite G] [IsQuasisimple G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* H)
    (d : InvolutionCentralizerQuotientData H _root_.Sporadic.Fischer.Fi22.Carrier)
    (hs : IsSemisimple Theory.SpecificGroups.U6Two.Carrier) : False := by
  exact false_of_cover_semisimple_quotient ih hG hK e (fischer_unitary_data d) hs
    (by have hh := Theory.SpecificGroups.U6Two.three_le_primeRank; omega)

public theorem fi22_three_le_primeRank : 3 ≤ primeRank 3 _root_.Sporadic.Fischer.Fi22.Carrier := by
  obtain ⟨t,L,f,ht,hL,hf,hker⟩ := _root_.Sporadic.Fischer.Fi22.exists_unitary_section
  let d : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi22.Carrier
      Theory.SpecificGroups.U6Two.Carrier := ⟨t,ht,L,hL,f,hf⟩
  exact (Theory.SpecificGroups.U6Two.three_le_primeRank.trans
    (d.primeRank_le_twoLocalPrimeRank hker 3 (by decide))).trans
      (twoLocalPrimeRank_le_primeRank 3)

public theorem simple_fischer_of_quotient_data [Finite G] [Finite H]
    (e : G ≃* H) (hG : IsQuasithin G)
    (d : InvolutionCentralizerQuotientData H _root_.Sporadic.Fischer.Fi22.Carrier)
    (hk : IsPGroup 2 d.quotientMap.ker) : False :=
  d.not_quasithin_of_rank hk 3 (by decide) fi22_three_le_primeRank
    (isQuasithin_of_equiv e hG)

public theorem sporadic_caseI_of_fischer_data [Finite G] [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G) (hspor : KnownSimple.IsSporadicCarrier G)
    (d23 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi23.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier) (hk23 : IsPGroup 2 d23.quotientMap.ker)
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier) (hk24 : IsPGroup 2 d24.quotientMap.ker) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  rcases sporadic_simple_reduction ih hG hK hna hspor with h | h
  · exact ⟨.sporadic h, fun hs => theoremC_of_theoremBSporadicModel hs h⟩
  · rcases h with h | h
    · obtain ⟨e⟩ := h
      exact (simple_fischer_of_quotient_data e hG d23 hk23).elim
    · obtain ⟨e⟩ := h
      exact (simple_fischer_of_quotient_data e hG d24 hk24).elim

variable [Finite G] {S : Type u} [Group S] [Finite S] [IsQuasisimple G] {p : ℕ}

public theorem cover_mcl_of_comparison
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G))
    (e : G ⧸ center G ≃* _root_.Sporadic.LeechRelated.McL.Carrier)
    (comparison : _root_.Sporadic.LeechRelated.McL.Carrier ≃*
      Atlas.Sporadic.McLaughlin.Model) : False := by
  have h3 := Theory.SpecificGroups.McLaughlin.Multiplier.source_center_isThreeGroup
    comparison e h.2.2.2.2.1
    (by intro he; have ho := h.2.2.2.2.2.1; rw [he] at ho; norm_num at ho)
    hP (h.center_ne_bot ih.theoremA)
  exact cover_mcl_of_three_center h ih h3 e

public theorem cover_onan_of_compatible_lift
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G)) (e : G ⧸ center G ≃* ONan.Model)
    (F : ONan.Cover.linearSubgroup →* G)
    (hF : (projection e).comp F = ONan.Cover.projection) : False := by
  have hp3 := cover_onan_prime_three h.2.2.2.2.1 hP e h.1
  subst p
  obtain ⟨Q,f,hQ,hQp,hf,hn⟩ := ONan.ThreeCoverLocalLifts.exists_local_lift_of_linear_lift
    hP e F hF ONan.E9A4.linearGenerators_matrix ONan.E9A4.Data.table_mul_generator
    ONan.E9A4.normalForm_next ONan.E9A4.normalForm_injective
  exact ChapterI.sporadicCover_not_quasithin_of_e9_lift hP (h.center_ne_bot ih.theoremA)
    Q hQp hQ f hf hn h.1

public theorem sporadic_caseII_of_model_inputs
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G))
    (hspor : KnownSimple.IsSporadicCarrier (G ⧸ center G))
    (comparison : _root_.Sporadic.LeechRelated.McL.Carrier ≃*
      Atlas.Sporadic.McLaughlin.Model)
    (hs : IsSemisimple Theory.SpecificGroups.U6Two.Carrier)
    (d23 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi23.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (hlift : ∀ e : G ⧸ center G ≃* ONan.Model,
      ∃ F : ONan.Cover.linearSubgroup →* G, (projection e).comp F = ONan.Cover.projection) :
    False := by
  rcases sporadic_cover_reduction h ih hP hspor with hm | hr
  · obtain ⟨e⟩ := hm
    exact cover_mcl_of_comparison h ih hP e comparison
  · rcases hr with ho | hr
    · obtain ⟨_,⟨e⟩⟩ := ho
      obtain ⟨F,hF⟩ := hlift e
      exact cover_onan_of_compatible_lift h ih hP e F hF
    · rcases hr with h22 | hr
      · obtain ⟨e⟩ := h22
        exact cover_fi22_of_semisimple ih h.1 h.2.1 e hs
      · rcases hr with h23 | h24
        · obtain ⟨e⟩ := h23
          exact cover_fischer_of_quotient_data ih h.1 h.2.1 e d23 hs
        · obtain ⟨e⟩ := h24
          exact cover_fischer_of_quotient_data ih h.1 h.2.1 e d24 hs

end CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
