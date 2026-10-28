module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveComparison
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveQuotient
public import Theory.Quasithin.TwoKernelImage

/-!
# Both original wreath cases produce a faithful mixed pair

Choose the actual wreath component K from the complete failed-parabolic
comparison. If W=⟨YRc,K,S⟩ has trivial two-core, its original local pair
satisfies F.1.1. Otherwise the comparison proves characteristic two for
both literal quotient parabolics; the quotient configuration uses the
same K and the map W → W/O₂(W). Quasithinness passes through that map
by the normal-two-kernel theorem.

Thus the original wreath assumption produces a finite quasithin ambient
group with the genuine F.1.1 hypotheses, the D₁₀/Sz(2) and A₅ quotient
markings, and its first Borel contained in S. All core cases and the
quotient-parabolic comparison are discharged. Excluding this mixed pair
is the remaining DGS85/F.1.12 source theorem; this module does not assume
an exhaustive classifier or assert that exclusion.

Source: Aschbacher--Smith, original 15.2.4, printed pp.1106--1107, and
F.1.12, printed pp.262--264.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original wreath local yields an actual faithful mixed F.1.1 pair,
with quasithinness and both quotient markings proved in either core case. -/
theorem source_HStar_wreath_five_faithful_mixed_pair
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hcases : SourceCases.Dihedral (imageRepresentation M V hV.normalized) ∨
      SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    ∃ (A : Type u) (_ : Group A) (_ : Finite A)
      (L : Fin 2 → Subgroup A) (S : Subgroup A),
      IsQuasithin A ∧ ChapterF.Source.HypothesisF11 L S ∧
      S ⊔ ChapterF.Source.borel (L 0) S = S ∧
      (Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
        Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
      Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨K,hK,heK,hout,hi,hJS,hpar⟩ :=
    source_HStar_wreath_five_quotient_parabolics
      hG T hempty hM hJ hu hmany hV hcases hH he
  obtain ⟨l,hd,_⟩ := source_HStar_wreath_five_reduction
    hG T hempty hM hJ hu hmany hV hcases hH he
  let L₀ := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
    (M ⊓ Mc).pCoreIn 2
  let L := ![L₀,K]
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  let W := ChapterF.Source.generated L S
  by_cases hcore : pCore 2 W = ⊥
  · have hd₀ := source_dihedral_five_mixed_local_data
      hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi
    have hRS : (M ⊓ Mc).pCoreIn 2 ≤ S :=
      source_HStar_wreath_intersection_core_le_component_normalizer hG T hM hJ hu hV hH he hK
    refine ⟨G,inferInstance,inferInstance,L,S,hG.quasithin,hd₀.2.2 hcore,?_,?_,heK⟩
    · apply sup_eq_left.mpr
      exact hd₀.1.le.trans hRS
    · exact source_HStar_wreath_residual_join_quotient
        hG T hempty hM hJ hu hmany hV hcases hH he
  · let q := QuotientGroup.mk' (pCore 2 W)
    let Lhat := fun i => ((L i).subgroupOf W).map q
    let Shat := (S.subgroupOf W).map q
    obtain ⟨hF,hQ₀,hQ₁,hB⟩ := source_dihedral_five_core_quotient_configuration
      hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi hout hJS hcore (hpar hcore)
    have hQT : IsQuasithin (W ⧸ pCore 2 W) :=
      (hG.quasithin.subgroup W).quotient_twoSubgroup _ pCore_isPGroup
    exact ⟨W ⧸ pCore 2 W,inferInstance,inferInstance,Lhat,Shat,hQT,hF,hB,hQ₀,hQ₁⟩

end CFSG.Quasithin.Chapter15.Section02
