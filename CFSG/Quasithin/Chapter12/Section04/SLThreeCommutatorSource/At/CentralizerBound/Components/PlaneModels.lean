module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Components.Models

/-!
# Components of the literal plane centralizer in 12.4.8

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

The local centralizer of a plane missing the fixed line centralizes all of V.
Consequently the nonbinary Borel and symplectic alternatives of E.6.8 cannot
occur: their direct decomposition would make the component centralize V.
An actual cubic normalizing the plane, and acting nontrivially on it, removes
all remaining rank-two alternatives by A.3.18. This supplies the source model
for the containing component in the comparison with the hyperplane seed.

Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815.
-/

public section
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open CFSG.Quasithin.ChapterE.Section06.Components
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
open Chapter1.Section02.LocalModels
open ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- Every ordinary component of this plane centralizer escapes the original
module normalizer, and its intersection with that normalizer centralizes V. -/
theorem Configuration.plane_component_local
    (c : Configuration T L V U) {U₀ K : Subgroup G}
    (hU₀U : U₀ ≤ U) (hcor : subgroupCorank U U₀ = 1)
    (hK : IsComponentIn K (centralizer (U₀ : Set G))) :
    ¬ K ≤ normalizer (V : Set G) ∧
      K ⊓ normalizer (V : Set G) ≤ centralizer (V : Set G) := by
  have hE := source_hypothesisE61 c.hypothesis c.structural c.extension c.fixed_nontrivial
  have hg := (escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape).2.2.2.2 U₀ hU₀U hcor
  exact ⟨component_not_le hE (source_earlierLocalFacts hE) hg.2.2.2 hK,
    (le_inf inf_le_right (inf_le_left.trans hK.1)).trans hg.2.2.1.le⟩

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
theorem Configuration.plane_component_model_list (c : Configuration T L V U)
    {U₀ K : Subgroup G} (hU₀U : U₀ ≤ U) (hcor : subgroupCorank U U₀ = 1)
    (hK : IsComponentIn K (centralizer (U₀ : Set G))) :
    (∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL K 2 p) ∨
      IsAlternating K 6 ∨ ClassicalGroup.IsPSL K 4 2 ∨
      (IsAlternating K 7 ∨ IsAlternatingCover K 6 ∨ IsAlternatingCover K 7) ∨
      ClassicalGroup.IsPSL K 3 3 ∨ Nonempty (K ≃* Sporadic.Mathieu.M11) := by
  have hE := source_hypothesisE61 c.hypothesis c.structural c.extension c.fixed_nontrivial
  have hg := (escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape).2.2.2.2 U₀ hU₀U hcor
  obtain ⟨hout,hlocal⟩ := c.plane_component_local hU₀U hcor hK
  rcases RemainingSieve.adequateComponentAlternatives_knownSimple hE hg.2.2.2 hK with
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
theorem Configuration.plane_component_fermatMersenne (c : Configuration T L V U)
    {U₀ K : Subgroup G} (hU₀U : U₀ ≤ U) (hcor : subgroupCorank U U₀ = 1)
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
  let _ := c.chosen.elementary
  let _ : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.of_le (hU₀U.trans c.le_module)
  have hg := (escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape).2.2.2.2 U₀ hU₀U hcor
  have hne : U₀ ≠ ⊥ := by
    intro he
    have hc := hg.1
    rw [he,card_bot] at hc
    omega
  have hN : IsSQTK KnownSimple.IsKnownSimple N := c.hypothesis.simpleQTKE.twoLocal_sqtk
    ⟨U₀,hne,IsElementaryAbelian.isPGroup 2 U₀,rfl⟩
  have hr : primeRank 3 N ≤ 2 := hN.stronglyQuasithin 3 Nat.prime_three (by decide)
  let a : N := ⟨x,hxN⟩
  have ha : orderOf a = 3 := (orderOf_coe a).symm.trans hx
  have hnot : a ∉ J := fun haJ => hxU₀ (hK.1 haJ)
  rcases c.plane_component_model_list hU₀U hcor hK with hm | hm | hm | hm | hm | hm
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

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
