module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.HyperplanePreparation
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceComplete
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Ordinary-component models for the original G₂ cover sections

The genuine E.6.8 alternatives apply to an escaping cover hyperplane and every
codimension-one section of it. Their local centralizers centralize the whole
cover. This removes nonbinary Borel and symplectic models. An actual cubic
acting nontrivially on the section removes all remaining rank-two models by
A.3.18, leaving the precise Fermat/Mersenne PSL₂ models used by 12.4.8.

The local record below packages proved E.6 inputs; the final constructors
instantiate it on the original ambient hyperplanes and sections.
Source: Aschbacher--Smith, E.6.8 and 12.4.8, printed pp.247--248 and 815.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open CFSG.Quasithin.ChapterE.Section06.Components
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components
open Chapter1.Section02.LocalModels
open ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U U₀ : Subgroup G}

/-- The three genuine local inputs already proved for the actual cover sections. -/
structure LocalData (T : Sylow 2 G) (V A : Subgroup G) : Prop where
  hypothesisE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (V : Set G)) V
  member : A ∈ obstructionFamily (normalizer (V : Set G)) V
  localCentralizer : normalizer (V : Set G) ⊓ centralizer (A : Set G) ≤
    centralizer (V : Set G)

theorem LocalData.component_local (c : LocalData T V U₀)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U₀ : Set G))) :
    ¬ K ≤ normalizer (V : Set G) ∧
      K ⊓ normalizer (V : Set G) ≤ centralizer (V : Set G) := by
  exact ⟨component_not_le c.hypothesisE (source_earlierLocalFacts c.hypothesisE) c.member hK,
    (le_inf inf_le_right (inf_le_left.trans hK.1)).trans c.localCentralizer⟩

omit [Finite G] in
private theorem parameter_one_of_decomposition
    {K : Subgroup G} {n : ℕ} (hpos : 1 ≤ n)
    (hout : ¬ K ≤ normalizer (V : Set G))
    (hlocal : K ⊓ normalizer (V : Set G) ≤ centralizer (V : Set G))
    (hd : 1 < n → DirectDecomposition V ⁅V, K ⊓ normalizer (V : Set G)⁆
      (V ⊓ centralizer (K : Set G))) : n = 1 := by
  by_contra hn
  have he := (hd (by omega)).1
  have hc : ⁅V, K ⊓ normalizer (V : Set G)⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr hlocal)
  rw [hc, bot_sup_eq] at he
  apply hout
  exact (le_centralizer_iff.mpr (he ▸
    (inf_le_right : V ⊓ centralizer (K : Set G) ≤ centralizer (K : Set G)))).trans
      (Subgroup.centralizer_le_normalizer _)

omit [Finite G] in
private theorem borel_one_psl_three {K : Subgroup G} [IsQuasisimple K]
    (hm : BorelComponentModel K 1) : ClassicalGroup.IsPSL K 3 2 := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  cases hm with
  | linear_two hn iso =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := iso
    let := Theory.PSL2.OuterSolvable.isSolvable_of_card_two (by simpa using hF)
    exact (Group.IsPerfect.not_isSolvable K
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
  | suzuki m hm hn iso => omega
  | linear_three hn iso => simpa using iso
  | unitary_three hn iso =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := iso
    let := BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo.projective_isSolvable J
      (by simpa using hF) (by simpa using hconj)
    exact (Group.IsPerfect.not_isSolvable K
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
  | linear_three_cover hn hz iso => omega

/-- E.6.8 in the plane centralizer, retaining all actual model equivalences
before applying the cubic actor. -/
theorem LocalData.component_model_list (c : LocalData T V U₀)
    {K : Subgroup G}
    (hK : IsComponentIn K (centralizer (U₀ : Set G))) :
    (∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL K 2 p) ∨
      IsAlternating K 6 ∨ ClassicalGroup.IsPSL K 4 2 ∨
      (IsAlternating K 7 ∨ IsAlternatingCover K 6 ∨ IsAlternatingCover K 7) ∨
      ClassicalGroup.IsPSL K 3 3 ∨ Nonempty (K ≃* Sporadic.Mathieu.M11) := by
  have hE := c.hypothesisE
  obtain ⟨hout,hlocal⟩ := c.component_local hK
  rcases RemainingSieve.adequateComponentAlternatives_knownSimple hE c.member hK with
    ⟨n,hb⟩ | ⟨n,hs⟩ | h4 | ha | ho
  · have hpos : 1 ≤ n := by
      rw [hb.dimension]
      exact fixedSpace_corank_pos hE hout
    have hn := parameter_one_of_decomposition hpos hout hlocal hb.decomposition
    let := hK.quasisimple
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := borel_one_psl_three (hn ▸ hb.model)
    let : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = Fintype.card (ZMod 2) := by
      simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hc
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    let d := (e.trans (Atlas.fieldEquivPSL 3 (FiniteField.ringEquivOfCardEq hcard))).trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm
    exact Or.inl ⟨7,⟨by decide,Or.inr ⟨3,by decide⟩⟩,
      ZMod 7,inferInstance,inferInstance,by simp,⟨d⟩⟩
  · have hn := parameter_one_of_decomposition hs.model.1 hout hlocal hs.decomposition
    obtain ⟨_,F,_,_,hc,⟨e⟩⟩ := hs.model
    rw [hn,pow_one] at hc
    exact Or.inr (Or.inl
      ⟨e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hc)⟩)
  · exact Or.inr (Or.inr (Or.inl h4.1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha.model)))
  · rcases ho.1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- The actual cubic actor on the plane excludes every rank-two model,
leaving the Fermat/Mersenne PSL₂ model needed for component comparison. -/
theorem LocalData.component_fermatMersenne (c : LocalData T V U₀)
    {K : Subgroup G}
    (hK : IsComponentIn K (centralizer (U₀ : Set G)))
    {x : G} (hx : orderOf x = 3) (hxN : x ∈ normalizer (U₀ : Set G))
    (hxU₀ : x ∉ centralizer (U₀ : Set G)) :
    ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL K 2 p := by
  let N := normalizer (U₀ : Set G)
  have hKN : IsComponentIn K N := by
    let := normal_subgroupOf_centralizer_normalizer (U₀ : Set G)
    exact hK.of_subnormal (Subgroup.centralizer_le_normalizer _)
      (inferInstance : ((centralizer (U₀ : Set G)).subgroupOf N).Normal).isSubnormal
  let J := K.subgroupOf N
  let e : J ≃* K := subgroupOfEquivOfLe hKN.1
  have hJ : IsComponent N J := hKN.2
  let _ := c.hypothesisE.elementary
  let _ : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.of_le c.member.1
  have hN : IsSQTK KnownSimple.IsKnownSimple N := c.hypothesisE.simpleQTKE.twoLocal_sqtk
    ⟨U₀,c.member.2.1,IsElementaryAbelian.isPGroup 2 U₀,rfl⟩
  have hr : primeRank 3 N ≤ 2 := hN.stronglyQuasithin 3 Nat.prime_three (by decide)
  let a : N := ⟨x,hxN⟩
  have ha : orderOf a = 3 := (orderOf_coe a).symm.trans hx
  have hnot : a ∉ J := fun haJ => hxU₀ (hK.1 haJ)
  rcases c.component_model_list hK with hm | hm | hm | hm | hm | hm
  · exact hm
  · exact (hnot (cubic_mem_of_alternating_component hJ (by decide : 6 ≤ 6)
      ⟨e.trans hm.some⟩ hr ha)).elim
  · obtain ⟨F,_,_,hc,⟨d⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = Fintype.card (ZMod 2) := by
      simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hc
    let d' := ((e.trans d).trans (Atlas.fieldEquivPSL 4 (FiniteField.ringEquivOfCardEq hcard))).trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
    exact (hnot (cubic_mem_of_alternating_component hJ (by decide : 6 ≤ 8) ⟨d'⟩ hr ha)).elim
  · rcases hm with hm | hm
    · exact (hnot (cubic_mem_of_alternating_component hJ (by decide : 6 ≤ 7)
        ⟨e.trans hm.some⟩ hr ha)).elim
    · exact (hnot (cubic_mem_of_alternating_cover_component hJ e hm hr ha)).elim
  · obtain ⟨F,_,_,hc,⟨d⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
      simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hc
    let d' := (e.trans d).trans (Atlas.fieldEquivPSL 3 (FiniteField.ringEquivOfCardEq hcard))
    have he := (ChapterA.Section03.OddPrime.SourceModels.SmallComponents.component_eq_cubic_residual
      hN hJ (Or.inl ⟨d'⟩)).2
    apply (hnot ?_).elim
    rw [he]
    apply mem_primeToResidual_of_pow (n := 1)
    simpa only [pow_one,ha] using pow_orderOf_eq_one a
  · have he := (ChapterA.Section03.OddPrime.SourceModels.SmallComponents.component_eq_cubic_residual
      hN hJ (Or.inr ⟨e.trans hm.some⟩)).2
    apply (hnot ?_).elim
    rw [he]
    apply mem_primeToResidual_of_pow (n := 1)
    simpa only [pow_one,ha] using pow_orderOf_eq_one a

/-- Original G₂ hyperplane and all its codimension-one sections, with every
local-data premise discharged from the original hypotheses. -/
theorem cover_localData
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    LocalData T V U ∧ ∀ U₀ ≤ U, subgroupCorank U U₀ = 1 → LocalData T V U₀ := by
  have hE := cover_source_hypothesisE61 h D structural e hne
  have hg := escaping_cover_subspaces h D structural e hne hUV hcor hescape
  refine ⟨⟨hE,hg.2.2.2.1,hg.2.2.1.le⟩,?_⟩
  intro U₀ hU₀U hcor₀
  have hs := hg.2.2.2.2 U₀ hU₀U hcor₀
  exact ⟨hE,hs.2.2.2,hs.2.2.1.le⟩

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components
