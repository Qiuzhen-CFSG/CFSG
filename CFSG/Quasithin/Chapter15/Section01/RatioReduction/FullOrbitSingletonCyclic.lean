module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ClassifiedFactors
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SingletonSupport
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Equivariant
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.DihedralMarking

/-!
# The original singleton cyclic full-orbit actor

The singleton factor has the original Jhat as its literal embedded actor
and the original local module as its support. Transporting the already
proved cyclic D.2.17 generation witness along those embeddings gives the
actual kernel and involution on the original action. Its endpoint theorem
then yields precisely the marked dihedral, elementary-nine and
extraspecial27 alternatives needed in original 15.1.2.

Source: Aschbacher--Smith 15.1.2, printed p.1086, singleton cyclic cases.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_singleton_cyclic_localGeneration
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (i : d.Index), (∀ j : d.Index,j=i) → U=⊤ →
      (∀ A ∈ QhatStar (d.factor i).action, IsCyclic A) →
      Nonempty (CyclicSource.LocalGeneration (ρ.comp (Jhat ρ).subtype)) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let f := actionHom M V (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd i hi hU hc
  obtain ⟨l⟩ := c.factor_cyclic_localGeneration d (source_localAction_twoCore hG T hM)
    (source_centralizing_cubicRatio_le_two hG T hempty hM hmany hJ) hd
    (Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1))
    f.rangeRestrict f.rangeRestrict_surjective i hc
  let F := c.ambientFactor d i
  let e : (d.factor i).Carrier ≃* Jhat ρ :=
    (MonoidHom.ofInjective F.embedding.group_injective).trans
      (MulEquiv.subgroupCongr (c.unique_factor_actor d i hi))
  have hs : F.space=⊤ := (c.unique_factor_space d i hi).trans hU
  let x : F.Space ≃ₗ[ZMod 2] Additive V := LinearEquiv.ofBijective F.embedding.spaceMap
    ⟨F.embedding.space_injective,LinearMap.range_eq_top.mp hs⟩
  have hx : ∀ g v, x ((d.factor i).action g v) =
      (ρ.comp (Jhat ρ).subtype) (e g) (x v) := by
    intro g v
    exact F.embedding.equivariant g v
  exact ⟨l.mapEquiv e x hx⟩

/-- The original singleton cyclic actor is a marked dihedral endpoint,
normal elementary-nine extension, or normal extraspecial27 extension. The
module and the kernel inclusions here are those of the original action. -/
theorem source_localAction_singleton_cyclic_endpoints
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
    ∃ l : CyclicSource.LocalGeneration (ρ.comp (Jhat ρ).subtype),
      letI := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
      letI : Finite (Additive V) := Module.finite_of_finite (ZMod 2)
      letI : IsElementaryAbelian 2 (Multiplicative (Additive V)) := BinaryGroupAction.elementary
      letI := l.normal
      (∃ p m, CyclicSource.PrimeDimensionOptions p m ∧ CyclicSource.DihedralMarking l p m) ∨
      ChapterD.Section02.ElementaryNineEndpoint (V := Multiplicative (Additive V))
        l.kernel l.involution ∨
      ChapterD.Section02.ExtraspecialEndpoint (V := Multiplicative (Additive V))
        l.kernel l.involution := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d hd i hi hU hc
  obtain ⟨l⟩ := source_localAction_singleton_cyclic_localGeneration hG T hempty hM hmany hJ
    U c d hd i hi hU hc
  let := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
  let : Finite (Additive V) := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative (Additive V)) := BinaryGroupAction.elementary
  let := l.normal
  have hf : Function.Injective (ρ.comp (Jhat ρ).subtype) :=
    (UniqueFactor.imageRepresentation_injective M V (le_normalizer_conjugateSpanBy _ _)).comp
      (Jhat ρ).subtype_injective
  refine ⟨l,?_⟩
  rcases l.endpoints hf with h3 | h5 | h9 | hex
  · obtain ⟨p,m,hpm,hm⟩ := l.marking_of_endpoints (Or.inl h3)
    exact Or.inl ⟨p,m,hpm,hm⟩
  · obtain ⟨p,m,hpm,hm⟩ := l.marking_of_endpoints (Or.inr h5)
    exact Or.inl ⟨p,m,hpm,hm⟩
  · exact Or.inr (Or.inl h9)
  · exact Or.inr (Or.inr hex)
end CFSG.Quasithin.Chapter15.Section01
