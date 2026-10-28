module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveOvercomponent
public import CFSG.Quasithin.ChapterF.Section01.CoreQuotient

/-!
# The literal quotient mixed pair in original 15.2.4

Keep the same chosen residual Y, intersection core Rc, wreath component K,
and S=N_T(K). In W=⟨YRc,K,S⟩ with nontrivial two-core, the proved source
Sylow argument gives S∈Syl₂(W). Hence the original map W→W/O₂(W) preserves
the local-core quotients D₁₀/Sz(2) and A₅ and maps both local Borels exactly.
When the two image parabolics have characteristic two, this verifies every
original F.1.1 clause for the quotient pair. Its first Borel is contained
in the image of S, supplying the source one-sided normality.

The final consumer selects the actual component from the original H-star
wreath assumption and retains both core cases. The mixed DGS85 compatibility
is a separate input; no global residual normality is used here.
Source: Aschbacher--Smith, original 15.2.4, printed p.1106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- The same marked five pair supplies the literal quotient F.1.1 configuration. -/
theorem source_dihedral_five_core_quotient_configuration
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H K : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype))
    (hd : DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hK : K ∈ Chapter1.cComponentsIn H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hi : ((T : Subgroup G) ⊓ normalizer (K : Set G)).relIndex (T : Subgroup G) = 2)
    (hout : ¬ K ≤ M)
    (hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) ⊓ normalizer (K : Set G)) :
    let L₀ := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
      (M ⊓ Mc).pCoreIn 2
    let L := ![L₀,K]
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    let W := ChapterF.Source.generated L S
    let q := QuotientGroup.mk' (pCore 2 W)
    let Lhat := fun i => ((L i).subgroupOf W).map q
    let Shat := (S.subgroupOf W).map q
    pCore 2 W ≠ ⊥ →
    (∀ i, generalizedFitting (((ChapterF.Source.parabolic L S i).subgroupOf W).map q) =
      pCore 2 (((ChapterF.Source.parabolic L S i).subgroupOf W).map q)) →
    ChapterF.Source.HypothesisF11 Lhat Shat ∧
      (Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃* DihedralGroup 5) ∨
        Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
      Nonempty ((Lhat 1 ⧸ pCore 2 (Lhat 1)) ≃* alternatingGroup (Fin 5)) ∧
      Shat ⊔ ChapterF.Source.borel (Lhat 0) Shat = Shat := by
  intro L₀ L S W q Lhat Shat hcore hc
  let R := (M ⊓ Mc).pCoreIn 2
  have hB0 : ChapterF.Source.borel L₀ S = R :=
    (source_dihedral_five_mixed_local_data hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi).1
  have hRS : R ≤ S := source_HStar_wreath_intersection_core_le_component_normalizer
    hG T hM hJ hu hV hH he hK
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hSylR : Chapter1.IsSylowIn 2 R L₀ :=
    source_dihedral_five_intersection_core_sylow hG T hempty hM hJ hu hmany hV l hp hd
  have hS : IsPGroup 2 S := T.isPGroup'.to_le inf_le_left
  have hSL : S ⊓ L₀ = R := (Chapter1.isSylowIn_iff.mp hSylR).2.2 _
    (hS.to_le inf_le_left) (le_inf hRS le_sup_right) inf_le_right
  have hquot := source_dihedral_five_join_quotient hG T hempty hM hJ hu hmany hV l hp hd
  have hSK : S ⊓ K = (T : Subgroup G) ⊓ K := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans K.le_normalizer)) inf_le_right
  have hKsy : Chapter1.IsSylowIn 2 (S ⊓ K) K := by
    rw [hSK]
    have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
    exact Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
      ⟨T.subtype hTH,map_subgroupOf_eq_of_le hTH⟩ hK.1 hK.2.subnormal
  have hSyl : ∀ i : Fin 2, Chapter1.IsSylowIn 2 (S ⊓ L i) (L i) := by
    intro i
    fin_cases i
    · exact hSL.symm ▸ hSylR
    · exact hKsy
  have hN : ∀ i : Fin 2, S ≤ normalizer (L i : Set G) := by
    intro i
    fin_cases i
    · exact inf_le_left.trans (le_sup_right.trans
        (source_chosen_centralizer_sylow_normalizes_residual T hM.1.2 hu hV).2)
    · exact inf_le_right
  have hQ : ∀ i : Fin 2, ChapterF.Source.IsRankOneModel (L i ⧸ pCore 2 (L i)) := by
    intro i
    fin_cases i
    · exact hquot.elim ChapterF.Source.IsRankOneModel.dihedral
        (ChapterF.Source.IsRankOneModel.suzuki 0)
    · obtain ⟨e⟩ := heK
      apply ChapterF.Source.IsRankOneModel.linear 2 (by decide)
      refine ⟨GaloisField 2 2,inferInstance,inferInstance,?_,
        ⟨e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩
      rw [GaloisField.card 2 2 (by decide)]
  have hX : ∀ i : Fin 2,
      ChapterF.Source.borel (L (ChapterF.Source.other i)) S ≤ normalizer (L i : Set G) := by
    intro i
    fin_cases i
    · change ChapterF.Source.borel K S ≤ normalizer (L₀ : Set G)
      have hB := source_HStar_symmetricFive_wreath_borel hG T hM hJ hH he hK
      have hTI : (T : Subgroup G) ≤ H ⊓ M := le_inf hH.1.1.2 hM.1.2
      have hs := congrArg (Subgroup.map (H ⊓ M).subtype)
        (pResidual_sup_sylow_eq_top (T.subtype hTI))
      rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI,
        ←MonoidHom.range_eq_map,range_subtype] at hs
      have hIC : H ⊓ M ≤ (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
        rw [←hs]
        exact sup_le_sup (le_inf ((map_subtype_le _).trans inf_le_right)
          (hV.intersection_residual H hH)) le_rfl
      exact hB.trans (hIC.trans
        (source_chosen_centralizer_sylow_normalizes_residual T hM.1.2 hu hV).2)
    · change ChapterF.Source.borel L₀ S ≤ normalizer (K : Set G)
      rw [hB0]
      exact hRS.trans inf_le_right
  have hSylW := source_dihedral_five_nontrivial_core_sylow
    hG T hempty hM hJ hu hmany hV l hd hout hi hJS hcore
  obtain ⟨hF,hE,hB,_⟩ := ChapterF.Source.localPair_coreQuotient L S hSylW hN hSyl hQ hX hc
  obtain ⟨e₀⟩ := hE 0
  obtain ⟨e₁⟩ := hE 1
  refine ⟨hF,?_,⟨e₁.symm.trans heK.some⟩,?_⟩
  · exact hquot.elim (fun hh => Or.inl ⟨e₀.symm.trans hh.some⟩)
      (fun hh => Or.inr ⟨e₀.symm.trans hh.some⟩)
  · apply sup_eq_left.mpr
    rw [hB 0]
    exact map_mono (comap_mono (hB0.le.trans hRS))

/-- The actual chosen source module supplies both mixed F.1.1 applications. -/
theorem source_HStar_wreath_five_core_quotient_configuration
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
    let L₀ := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
      (M ⊓ Mc).pCoreIn 2
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![L₀,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let Lhat := fun i => ((L i).subgroupOf W).map q
      let Shat := (S.subgroupOf W).map q
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      ChapterF.Source.borel L₀ S = (M ⊓ Mc).pCoreIn 2 ∧
      (pCore 2 W = ⊥ → ChapterF.Source.HypothesisF11 L S) ∧
      (pCore 2 W ≠ ⊥ →
        (∀ i, generalizedFitting (((ChapterF.Source.parabolic L S i).subgroupOf W).map q) =
          pCore 2 (((ChapterF.Source.parabolic L S i).subgroupOf W).map q)) →
        ChapterF.Source.HypothesisF11 Lhat Shat ∧
          (Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃* DihedralGroup 5) ∨
            Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
          Nonempty ((Lhat 1 ⧸ pCore 2 (Lhat 1)) ≃* alternatingGroup (Fin 5)) ∧
          Shat ⊔ ChapterF.Source.borel (Lhat 0) Shat = Shat) := by
  obtain ⟨l,K,hd,hK,heK,_,hout,hi,hJS,_⟩ :=
    source_HStar_wreath_five_configuration_with_Rc_le_S
      hG T hempty hM hJ hu hmany hV hcases hH he
  have hd₀ := source_dihedral_five_mixed_local_data
    hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi
  exact ⟨K,hK,heK,hout,hi,hJS,hd₀.1,hd₀.2.2,
    source_dihedral_five_core_quotient_configuration
      hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi hout hJS⟩

end CFSG.Quasithin.Chapter15.Section02
