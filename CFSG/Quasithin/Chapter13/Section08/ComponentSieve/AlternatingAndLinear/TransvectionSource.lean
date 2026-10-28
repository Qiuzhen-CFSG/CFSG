module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableB18
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.SourceAssembly
public import Theory.Representation.HexacodeAction.Cover
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# The transvection input to the post-13.8.21 linear sieve

The source recognition theorem 13.8.5 constructs models of the whole literal
module U_H/V₁. Here those models are transported to the center-quotient action
used by the later sieve, including the two noncentral L₁-chief factors. The
matrix and linear actor markings in the four-dimensional alternative are
related by the canonical binary projective-linear equivalence.

A fixed-codimension-one actor is first given an actual transvection formula.
The seven-point sieve and the four-dimensional linear branch then consume
the resulting compatible models. No equality between a moved section and
the whole module is inferred from faithfulness.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.5,
13.8.24 and the first case of 13.8.25, printed pp.947–948 and 958–960.
The standing setup, earlier local results, 13.7.6 and G.6.4 remain explicit.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.TransvectionSource

open TransvectionRecognition TransvectionRecognition.Component.RecognitionStep
open TransvectionRecognition.Component.ModelExtension
open CriticalGeometry CriticalGeometry.AsymmetricPair CriticalGeometry.Reorientation
open FourStructure.ChiefFactors

private theorem transvection_of_codimension_one
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) A E) (a : A)
    (hc : fixedCodim ρ (zpowers a) = 1) : IsTransvection ρ a := by
  let e := LinearEquiv.ofBijective (ρ a) (ρ.apply_bijective a)
  have hr : Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) = 1 :=
    (fixedCodim_zpowers_eq_displacement_rank ρ a).symm.trans hc
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr hr.le
  have hformula (w : E) : ρ a w = w + f w • v :=
    congrArg (fun l : E →ₗ[ZMod 2] E => l w) he
  have hne : ρ a ≠ LinearMap.id := by
    intro hh
    have hz : e.toLinearMap - LinearMap.id = 0 := sub_eq_zero.mpr hh
    rw [hz, LinearMap.range_zero, finrank_bot] at hr
    omega
  have hf : f ≠ 0 := by
    intro hz
    apply hne
    ext w
    simpa only [hz, LinearMap.zero_apply, zero_smul, add_zero, LinearMap.id_apply] using hformula w
  have hv : v ≠ 0 := by
    intro hz
    apply hne
    ext w
    simpa only [hz, smul_zero, add_zero, LinearMap.id_apply] using hformula w
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with hz | ho
    · exact hz
    have hev : e v = 0 := by
      change ρ a v = 0
      rw [hformula, ho, one_smul, ZModModule.add_self]
    exact (hv (e.map_eq_zero_iff.mp hev)).elim
  exact ⟨f, v, hf, hv, hfv, hformula⟩

private theorem triple_cover_of_hex {A : Type*} [Group A]
    (e : A ≃* Atlas.Codes.HexEvenAutomorphisms) : SolvableExclusion.IsTripleCoverSix A := by
  let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  refine ⟨IsQuasisimple.of_mulEquiv e.symm,
    (Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card, ?_⟩
  have hm : (center A).map e.toMonoidHom = center Atlas.Codes.HexEvenAutomorphisms := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (centerCongr e ⟨y, hy⟩).property
    · intro hx
      exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
  exact ⟨(QuotientGroup.congr _ _ e hm).trans Hexacode.even_quotient_center_equiv⟩

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
  (localEarlier : Solvable.EarlierLocalInputs (G := G))
  (hG64 : G64SourceTheorem.{u} KnownSimple.IsKnownSimple)
  (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
  (hρ : IsSourceAction H V₃ V₁ ρ)

include hρ

omit [Finite G] in
private theorem literal_eq (Q : CenterQuotientAction H (Source.UH H V₃) V₁)
    (h : H) (v : SourceSpace H V₃ V₁) :
    literalRepresentation Q h v = ρ (QuotientGroup.mk' (pCore 2 H) h) v := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  exact (congrArg Additive.ofMul (Q.apply_mk h x)).trans (hρ h x).symm

omit [Finite G] in
private theorem star_model
    (Q : CenterQuotientAction H (Source.UH H V₃) V₁)
    {B E : Type*} [Group B] [AddCommGroup E] [Module (ZMod 2) E]
    {σ : Representation (ZMod 2) B E} (hm : HasActionModel ρ σ) :
    Nonempty (StarModuleModel Q σ) := by
  obtain ⟨eB, eE, he⟩ := hm
  refine ⟨⟨eB, eE, ?_⟩⟩
  intro h v
  rw [literal_eq ρ hρ Q]
  exact he _ _

include d earlier localEarlier hG64 hH

/-- The full 13.8.5 output at the literal action expected by 13.8.8 and
13.8.25. B.1.8 is discharged by its source theorem. -/
theorem full_model_conclusions
    (Q : CenterQuotientAction H (Source.UH H V₃) V₁)
    (a : Source.Hstar H) (hc : fixedCodim ρ (zpowers a) = 1) :
    FullModelConclusions L (sourceOne L T V₁) (T : Subgroup G)
      (le_sup_left.trans hH.1.2) Q := by
  obtain ⟨hcomponent, hm⟩ := SourceCompletion.transvection_recognition T d earlier
    localEarlier hG64 hH ρ hρ ⟨a, transvection_of_codimension_one ρ a hc⟩
  refine ⟨hcomponent, ?_⟩
  rcases hm with ⟨hm, hL, hchief⟩ | ⟨hm, ⟨eL⟩⟩
  · refine Or.inl ⟨?_, hL, ?_⟩
    · rcases hm with hnat | ⟨hcore, _⟩
      · exact Or.inl (star_model ρ hρ Q hnat)
      · exact Or.inr (star_model ρ hρ Q hcore)
    · rwa [← ChiefQuotient.loneQuotientRepresentation_eq_literal H V₃ V₁
        (sourceOne L T V₁) (le_sup_left.trans hH.1.2) ρ hρ Q]
  · refine Or.inr ⟨?_, triple_cover_of_hex eL⟩
    rcases hm with hseven | ⟨eA, eE, he⟩
    · exact Or.inl (star_model ρ hρ Q hseven)
    · refine Or.inr ⟨?_, ⟨eA⟩⟩
      apply star_model ρ hρ Q
      exact ⟨eA.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide)), eE, he⟩

omit [(V₁.subgroupOf (Source.UH H V₃)).Normal] in
/-- The actual 13.8.5 group and seven-point permutation-core models
needed by the A₇ and middle-node sieves, with their common actor marking. -/
theorem transvection_models (a : Source.Hstar H)
    (hc : fixedCodim ρ (zpowers a) = 1) : Seven.LocalGeometry.TransvectionModels ρ L := by
  obtain ⟨_, hm⟩ := SourceCompletion.transvection_recognition T d earlier
    localEarlier hG64 hH ρ hρ ⟨a, transvection_of_codimension_one ρ a hc⟩
  rcases hm with ⟨hm, _, _⟩ | ⟨hm, ⟨eL⟩⟩
  · rcases hm with ⟨eA, _⟩ | ⟨⟨eA, _⟩, _⟩ <;> exact Or.inl ⟨eA⟩
  · rcases hm with ⟨eA, eE, he⟩ | ⟨eA, _⟩
    · refine Or.inr (Or.inr ⟨triple_cover_of_hex eL, eA, eE.symm, ?_⟩)
      intro g v
      apply eE.injective
      simpa only [LinearEquiv.apply_symm_apply] using (he g (eE.symm v)).symm
    · exact Or.inr (Or.inl ⟨eA⟩)

omit [(V₁.subgroupOf (Source.UH H V₃)).Normal] in
/-- In the L₄(2) case the source transvection theorem recognizes the whole
four-dimensional module and the concrete local triple cover. The linear
actor equivalence is the one intertwined by the displayed module map. -/
theorem natural_four (e : Source.Hstar H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))
    (a : Source.Hstar H) (hc : fixedCodim ρ (zpowers a) = 1) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      ∃ (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
        (eU : SourceSpace H V₃ V₁ ≃ₗ[ZMod 2] NaturalSpace),
        (∀ b v, eU (ρ b v) = eH b (eU v)) ∧
        Module.finrank (ZMod 2) (SourceSpace H V₃ V₁) = 4 := by
  have hcard : Nat.card (Source.Hstar H) = 20160 := by
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have no_perm {n : ℕ} (hn : n = 6 ∨ n = 7)
      (f : Source.Hstar H ≃* Equiv.Perm (Fin n)) : False := by
    rw [Nat.card_congr f.toEquiv] at hcard
    rcases hn with rfl | rfl <;>
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hcard
  obtain ⟨_, hm⟩ := SourceCompletion.transvection_recognition T d earlier
    localEarlier hG64 hH ρ hρ ⟨a, transvection_of_codimension_one ρ a hc⟩
  rcases hm with ⟨hm, _, _⟩ | ⟨hm, hL⟩
  · rcases hm with ⟨eA, _⟩ | ⟨⟨eA, _⟩, _⟩ <;>
      exact (no_perm (Or.inl rfl) eA).elim
  · rcases hm with ⟨eA, _⟩ | ⟨eA, eU, he⟩
    · exact (no_perm (Or.inr rfl) eA).elim
    · refine ⟨hL, eA.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide)),
        eU, he, ?_⟩
      rw [eU.finrank_eq]
      simp

omit [(V₁.subgroupOf (Source.UH H V₃)).Normal] in
/-- The complete first-case conclusion of 13.8.25, including H = G₁.
The independent uniform A₇ and group-reduction inputs remain explicit;
the full-module and concrete covered-A₆ markings are constructed from
13.8.5. In particular none of the strict-case chief-factor, cohomology or
splitting inputs of `EarlierModuleGeometry` is required in this case. -/
theorem source_linear_alternative_of_transvection
    (L₁ L₀ X : Subgroup G)
    (groups : LinearReduction.SourceReduction.GroupFacts L L₁ (T : Subgroup G)
      V V₁ V₃ G₁ M)
    (seven : ∀ (J C : Subgroup G), J ∈ Source.Hz L₁ (T : Subgroup G) G₁ M → C ≤ J →
      (C.subgroupOf J).IsCComponent →
      Nonempty (Seven.SourceExclusion.LocalData L T J V C L₁ L₀ X G₁ M V₃ V₁))
    (modules : ∀ (J C : Subgroup G), J ∈ Source.Hz L₁ (T : Subgroup G) G₁ M → C ≤ J →
      (C.subgroupOf J).IsCComponent →
      Nonempty (LinearReduction.SourceReduction.LocalModuleData L T J V C L₁ G₁ M V₃ V₁))
    {𝒦 : GroupClass.{u}} (embeddings : LinearReduction.Overgroup.EarlierEmbeddings 𝒦)
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁))
    {K : Subgroup G} {n : ℕ} (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2)
    (a : Source.Hstar H) (hc : fixedCodim ρ (zpowers a) = 1) :
    n = 4 ∧ Chapter1.Section02.LocalModels.IsAlternatingCover (L ⧸ pCore 2 L) 6 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      Nonempty (Source.Hstar H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) ∧
      (∃ (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
        (eU : SourceSpace H V₃ V₁ ≃ₗ[ZMod 2] NaturalSpace),
        (∀ b v, eU (ρ b v) = eH b (eU v)) ∧
        Module.finrank (ZMod 2) (SourceSpace H V₃ V₁) = 4) ∧ H = G₁ := by
  have hH' : H ∈ Source.Hz L₁ (T : Subgroup G) G₁ M := by
    simpa only [groups.local_definition] using hH
  have hline : V₁ ≠ ⊥ := by
    intro he
    have hh := d.line_card
    rw [he, card_bot] at hh
    omega
  have hp : IsPGroup 2 V₁ := isPGroup_iff_card_dvd_pow.mpr
    ⟨1, by rw [d.line_card]; norm_num⟩
  have hVT : V₁ ≤ (T : Subgroup G) := hp.le_sylow_of_normalized T d.line_stable
  obtain ⟨hn, hcover, ⟨eH⟩, heq⟩ := LinearReduction.SourceReduction.source_linear_reduction
    L L₁ V V₁ V₃ G₁ M T groups modules embeddings hQ
    (fun hJ hCJ hC => SourceAssembly.not_alternatingSeven_uniform
      L L₁ L₀ X (T : Subgroup G) V V₁ V₃ G₁ M seven hJ hCJ hC)
    hline hp (hVT.trans le_sup_right) d.first_normalizer.le
    hH' hKH hK hn₀ hn₁ hmodel
  obtain ⟨hL, hnatur⟩ := natural_four d earlier localEarlier hG64 hH ρ hρ eH a hc
  exact ⟨hn, hcover, hL, ⟨eH⟩, hnatur, heq⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.TransvectionSource
