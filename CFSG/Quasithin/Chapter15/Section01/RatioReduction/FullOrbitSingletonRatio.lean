module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitSingletonCyclic
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.PrimeSource

/-!
# The cubic ratio of the original singleton cyclic action

The actual singleton factor satisfies all cyclic D.2.17 hypotheses, including
its original full Fitting movement. The D.2.24 ratio-one branch has dimension
two. Its literal full-orbit support identification transfers that dimension to
the original local module; otherwise the original cubic ratio is two.

The second theorem consumes this alternative for the dimension-four and
dimension-six endpoints of 15.1.2, without changing the module or assuming
preservation of the minimum under a moved-space restriction.

Source: Aschbacher--Smith D.2.24 and 15.1.2, printed p.1086.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
open scoped IsMulCommutative ENNReal
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_singleton_cyclic_ratio
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (i : d.Index), (∀ j : d.Index,j=i) → U=⊤ →
      (∀ A ∈ QhatStar (d.factor i).action, IsCyclic A) →
      (cubicRatio ρ = 1 ∧ Module.finrank (ZMod 2) (Additive V) = 2) ∨
      cubicRatio ρ = 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd i hi hU hc
  let F₀ := d.factor i
  let F := c.ambientFactor d i
  let j := (Jhat ρ).subtype.comp F₀.embedding.groupMap
  let : Group.IsSolvable F₀.Carrier := Group.isSolvable_of_isSolvable_injective
    (f := j) ((Jhat ρ).subtype_injective.comp F₀.embedding.group_injective)
  have hqF : cubicRatio F₀.action ≤ 2 := by
    rw [F₀.embedding.ratio,c.ratio]
    exact source_centralizing_cubicRatio_le_two hG T hempty hM hmany hJ
  have h : CyclicSource.Hypotheses F₀.action :=
    ⟨⟨F₀.faithful,hqF,F₀.generated,generalizedFitting_eq_fitting_of_solvable F₀.Carrier,
      c.factor_twoCore d (source_localAction_twoCore hG T hM) i,
      fun A hA => CyclicSource.rank_one_of_cyclic F₀.action hA (hc A hA)⟩,
      F₀.indecomposable,hd i⟩
  have hr : cubicRatio F₀.action = cubicRatio ρ := F₀.embedding.ratio.trans c.ratio
  rcases h.toCoreHypotheses.ratio_one_or_two with hq | hq
  · obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff F₀.action).mpr hqF
    obtain ⟨_,_,_,h₂⟩ := CyclicSource.ratio_one_full_support F₀.action h hq hA
    have hs : F.space=⊤ := (c.unique_factor_space d i hi).trans hU
    let x : F.Space ≃ₗ[ZMod 2] Additive V := LinearEquiv.ofBijective F.embedding.spaceMap
      ⟨F.embedding.space_injective,LinearMap.range_eq_top.mp hs⟩
    exact Or.inl ⟨hr.symm.trans hq,(LinearEquiv.finrank_eq x).symm.trans h₂⟩
  · exact Or.inr (hr.symm.trans hq)

theorem source_localAction_singleton_cyclic_ratio_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (i : d.Index), (∀ j : d.Index,j=i) → U=⊤ →
      (∀ A ∈ QhatStar (d.factor i).action, IsCyclic A) →
      2 < Module.finrank (ZMod 2) (Additive V) → cubicRatio ρ = 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d hd i hi hU hc hdim
  rcases source_localAction_singleton_cyclic_ratio hG T hempty hM hmany hJ
    U c d hd i hi hU hc with ⟨_,h₂⟩ | hq
  · exact False.elim (by omega)
  · exact hq
end CFSG.Quasithin.Chapter15.Section01
