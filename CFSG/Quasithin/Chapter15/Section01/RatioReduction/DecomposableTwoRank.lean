module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SourceCases
public import Theory.Representation.BinaryOffender.SupportSeedCore
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.OddResidual
public import Theory.GroupTheory.PCoreProduct
public import Theory.Representation.SmallBinaryTwoRank
public import Theory.Representation.PermutedSupportTwoRank
/-!
# Two-rank of the original exchanged dihedral action

The original Sylow seed forces each symmetric-three support image to have
trivial two-core. The binary normalizer list and the source rank-two cover
then give two-rank at most one on each support. Normal five supports have
the same bound via their odd centralizers. An elementary subgroup fixing
both supports embeds in their product; one exchanging them has a kernel
which embeds faithfully in either support.

Source: Aschbacher–Smith15.1.7(6) and15.1.13, pp.1087 and1091.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Stellmacher Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_symmetricThree_support_twoCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      (∀ i : d.Index, Nonempty ((d.factor i).Carrier ≃* Equiv.Perm (Fin 3))) →
      ∀ i, pCore 2 (subspaceActionImage ρ (c.ambientFactor d i).space) = ⊥ := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let Q := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
  dsimp only
  intro U c d hd π hp hs he i
  have hc := source_localAction_symmetricThree_factor_count hG T hM U c d he
  obtain ⟨S,hS⟩ := c.exists_support_stabilizer_sylow_of_count d π hs hc Q i
  exact supportImage_twoCore_eq_bot_of_sylow_seed _ _ S
    (source_localAction_support_stabilizer_seed_full hG T hM U c d hd π hp hs he i S hS)
end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Stellmacher Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition

private theorem not_symmetricThree_times_two_of_twoCore {D : Type*} [Group D] [Finite D]
    (hcore : pCore 2 D = ⊥)
    (e : D ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) : False := by
  have he : pCore 2 (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) = ⊥ := by
    rw [←pCore_map_iso 2 e,hcore,Subgroup.map_bot]
  have htwo : IsPGroup 2 (Multiplicative (ZMod 2)) := IsPGroup.of_card (n := 1) (by simp)
  have hx : (1,Multiplicative.ofAdd (1 : ZMod 2)) ∈
      pCore 2 (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) := by
    rw [pCore_prod]
    exact ⟨one_mem _, (le_sSup ⟨inferInstance, htwo.of_equiv (Subgroup.topEquiv).symm⟩ : (⊤ : Subgroup (Multiplicative (ZMod 2))) ≤ pCore 2 _) (mem_top _)⟩
  rw [he] at hx
  have hh := congrArg (fun a : Equiv.Perm (Fin 3) × Multiplicative (ZMod 2) => a.2.toAdd)
    (mem_bot.mp hx)
  norm_num at hh

variable {G : Type*} [Group G] [Finite G]
theorem source_localAction_symmetricThree_support_twoRank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      (∀ i : d.Index, Nonempty ((d.factor i).Carrier ≃* Equiv.Perm (Fin 3))) →
      (∀ i, Module.finrank (ZMod 2) (d.factor i).Space = 2 ∨
        Module.finrank (ZMod 2) (d.factor i).Space = 4) →
      1 < Nat.card d.Index →
      ∀ i, primeRank 2 (subspaceActionImage ρ (c.ambientFactor d i).space) ≤ 1 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d hd π hp hs he hdim hcount i
  let F := c.ambientFactor d i
  obtain ⟨k,J,hk,_,_,hn,hfull⟩ := F.faithful_normal_support_image_data
    (c.support_stabilizer_normalizes_actor d π hp hs i)
  let : k.range.Normal := hn
  let : FiniteDimensional (ZMod 2) F.space := Module.Finite.of_surjective J.toLinearMap J.surjective
  let σ := subspaceImageRepresentation ρ F.space
  let e := (MonoidHom.ofInjective hk).symm.trans (he i).some
  rcases hdim i with hdim | hdim
  · exact Representation.SmallBinaryTwoRank.rank_le_one_of_dimension_two σ
      (subspaceImageRepresentation_injective ρ F.space) (J.finrank_eq.symm.trans hdim)
  apply Representation.SmallBinaryTwoRank.rank_le_one_of_four_not_dvd
  intro hfour
  have hmove : subspaceCommutator (σ.comp k.range.subtype) ⊤ ⊤ = ⊤ := by
    rw [subspaceCommutator_comp_map,←MonoidHom.range_eq_map,k.range.range_subtype]
    exact hfull
  let τ := σ.comp (k.range.subtype.comp e.symm.toMonoidHom)
  have hτ : subspaceCommutator τ ⊤ ⊤ = ⊤ := by
    change subspaceCommutator ((σ.comp k.range.subtype).comp e.symm.toMonoidHom) ⊤ ⊤ = ⊤
    rw [subspaceCommutator_comp_map,map_top_of_surjective _ e.symm.surjective]
    exact hmove
  rcases Representation.BinarySymmetricThreeNormalizer.normal_symmetricThree_cases σ
      (subspaceImageRepresentation_injective ρ F.space) (J.finrank_eq.symm.trans hdim)
      k.range e (Representation.BinarySymmetricThreeNormalizer.fixedFree_of_full τ hτ) hfour
    with ⟨esmall⟩ | ⟨epair⟩
  · exact not_symmetricThree_times_two_of_twoCore
      (source_localAction_symmetricThree_support_twoCore hG T hM U c d hd π hp hs he i) esmall.some
  · have hsingle := source_localAction_symmetricThree_pair_image_singleton
      hG T hM U c d π hp hs he i epair.some
    have hcard : Nat.card d.Index = 1 := Nat.card_eq_one_iff_exists.mpr ⟨i,hsingle⟩
    omega
end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.ChapterD.RatioDecomposition.Factor
universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} (F : Factor ρ)

theorem support_twoRank_le_one_of_five
    (hN : subspaceStabilizer ρ F.space ≤ normalizer (F.actor : Set D))
    (l : CyclicSource.LocalGeneration F.action) (hm : CyclicSource.DihedralMarking l 5 2) :
    primeRank 2 (subspaceActionImage ρ F.space) ≤ 1 := by
  obtain ⟨k,J,hk,_,_,hn,_⟩ := F.faithful_normal_support_image_data hN
  let H := k.range
  let : H.Normal := hn
  let : FiniteDimensional (ZMod 2) F.space := Module.Finite.of_surjective J.toLinearMap J.surjective
  let e : F.Carrier ≃* H := MonoidHom.ofInjective hk
  let P := (pResidual 2 H).map H.subtype
  apply Representation.SmallBinaryTwoRank.rank_le_one_of_normal_five
    (subspaceImageRepresentation ρ F.space) (subspaceImageRepresentation_injective ρ F.space)
    (J.finrank_eq.symm.trans hm.dimension) P
  rw [card_map_of_injective H.subtype_injective,
    ←map_pResidual_of_surjective 2 e.toMonoidHom e.surjective,
    card_map_of_injective (f := e.toMonoidHom) e.injective,←l.kernel_eq_twoResidual]
  exact hm.card_kernel
end CFSG.Quasithin.ChapterD.RatioDecomposition.Factor

namespace CFSG.Quasithin.Chapter15.Section01
open Stellmacher Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_decomposable_action_twoRank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      SourceCases.Decomposable ρ (T : Subgroup G) M f c d π → primeRank 2 D ≤ 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d hd π hp hs hcase
  obtain ⟨hcount,p,m,hpm,hmark,i,j,hij,hall,_,_,_,hcompl,_⟩ := hcase
  apply Representation.twoRank_le_two_of_permuted_pair ρ
    (imageRepresentation_injective M V (le_normalizer_conjugateSpanBy _ _))
    (fun k => (c.ambientFactor d k).space) i j hij hall hcompl.sup_eq_top π hs
  rcases (CyclicSource.primeDimensionOptions_iff p m).mp hpm with ⟨rfl,hm⟩ | ⟨rfl,rfl⟩
  · have he : ∀ k : d.Index, Nonempty ((d.factor k).Carrier ≃* Equiv.Perm (Fin 3)) := by
      intro k
      obtain ⟨l,hl⟩ := hmark k
      exact ⟨hl.dihedral.some.trans nonempty_dihedralThreeEquivPerm.some⟩
    have hdim : ∀ k, Module.finrank (ZMod 2) (d.factor k).Space = 2 ∨
        Module.finrank (ZMod 2) (d.factor k).Space = 4 := by
      intro k
      obtain ⟨l,hl⟩ := hmark k
      rcases hm with rfl | rfl
      · exact Or.inl hl.dimension
      · exact Or.inr hl.dimension
    exact source_localAction_symmetricThree_support_twoRank
      hG T hM U c d hd π hp hs he hdim (by omega)
  · intro k
    obtain ⟨l,hl⟩ := hmark k
    exact (c.ambientFactor d k).support_twoRank_le_one_of_five
      (c.support_stabilizer_normalizes_actor d π hp hs k) l hl
end CFSG.Quasithin.Chapter15.Section01
