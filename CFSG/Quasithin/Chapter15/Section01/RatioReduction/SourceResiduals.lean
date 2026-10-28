module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SourceCases
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitOddResidual
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperSeedCentralizer
/-!
# Central-seed and intersection residuals in all six source cases

The original centralizing 15.1.2 dispatcher supplies a literal partition and
one of six action cases. In the five full-module cases, the normal dihedral
bound, permuted support bound, orthogonal embeddings, or residual order 27
prove that the full image has odd two-residual. In the proper case the chosen
module is the original moved subgroup, whose seed residual theorem applies.

The conclusions for O²(C_M(Z)) and each O²(H∩M) retain the same chosen ambient
subgroup. The source-only wrapper constructs the partition, leaving no image
oddness or residual-centralization assumption to discharge.

Source: Aschbacher–Smith 15.1.4, 15.1.6 and 15.1.9(4), pp.1087–1089.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_centralizing_cases_seed_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let S := (T.subtype hM.1.2 : Subgroup M).map f
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      (SourceCases.Dihedral ρ ∨ SourceCases.Omega ρ ∨
        SourceCases.Decomposable ρ (T : Subgroup G) M f c d π ∨
        SourceCases.Extraspecial ρ S ∨ SourceCases.Nine ρ S ∨
        SourceCases.Proper T M Mc V ρ U) →
      ∃ W : Subgroup G,
        (W = V ∨ (SourceCases.Proper T M Mc V ρ U ∧
          W = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype)) ∧
        W ≤ M ∧ M ≤ normalizer (W : Set G) ∧ IsElementaryAbelian 2 W ∧
        (pResidual 2 (M ⊓ centralizer (centralInvolutions T : Set G) : Subgroup G)).map
          (M ⊓ centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (W : Set G) ∧
        ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
          (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (W : Set G) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d hd π hp hs hcase
  have hwhole (hodd : Odd (Nat.card (pResidual 2 D))) :
      ∃ W : Subgroup G,
        (W = V ∨ (SourceCases.Proper T M Mc V ρ U ∧
          W = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype)) ∧
        W ≤ M ∧ M ≤ normalizer (W : Set G) ∧ IsElementaryAbelian 2 W ∧
        (pResidual 2 (M ⊓ centralizer (centralInvolutions T : Set G) : Subgroup G)).map
          (M ⊓ centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (W : Set G) ∧
        ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
          (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (W : Set G) := by
    exact ⟨V,Or.inl rfl,localModule_le T hM.1.2,le_normalizer_conjugateSpanBy _ _,
      inferInstance,chosen_seed_centralizer_residual_of_odd_residual T hM.1.2
        (localModule_le T hM.1.2) (le_normalizer_conjugateSpanBy _ _) hodd,
      fun H hH => source_15_1_9_4_of_odd_residual hG T hM hH hJ
        (localModule_le T hM.1.2) (le_normalizer_conjugateSpanBy _ _) hodd⟩
  rcases hcase with hdi | ho | hdc | hex | h9 | hproper
  · obtain ⟨l,p,m,hpm,hm⟩ := hdi
    exact hwhole (source_localAction_full_orbit_dihedral_odd_twoResidual hG T hM l p m hpm hm)
  · obtain ⟨_,_,_,_,x,e,_⟩ := ho
    exact hwhole (OrthogonalFourBinary.TerminalLines.odd_twoResidual_of_injective
      (OrthogonalFourBinary.omega.subtype.comp e.toMonoidHom)
      (OrthogonalFourBinary.omega.subtype_injective.comp e.injective))
  · obtain ⟨hc,p,m,hpm,hmark,i,j,_,_,_,_,_,hcompl,_⟩ := hdc
    have hU : U = ⊤ := by
      apply top_unique
      rw [←hcompl.sup_eq_top]
      apply sup_le
      · exact (le_iSup (fun k => (c.ambientFactor d k).space) i).trans
          (c.ambient_spaces_generate d).le
      · exact (le_iSup (fun k => (c.ambientFactor d k).space) j).trans
          (c.ambient_spaces_generate d).le
    exact hwhole (c.odd_twoResidual_of_two_dihedral_factors d
      (imageRepresentation_injective M V (le_normalizer_conjugateSpanBy _ _))
      hU hc π hp hs hpm hmark)
  · obtain ⟨l,_,_,_,hcard,_⟩ := hex
    apply hwhole
    rw [hcard]
    decide
  · obtain ⟨l,_,_,_,_,_,_,x,f,hf,_⟩ := h9
    exact hwhole (OrthogonalFourBinary.TerminalLines.odd_twoResidual_of_injective f hf)
  · have hnt : ¬ (U = ⊤ ∧ ∀ i j, ∃ g : D, π g i = j) :=
      fun h => hproper.2.2.2.2.2.1 h.1
    obtain ⟨hWM,_,hnW,hEW,_⟩ := source_localAction_proper_orbit_chosen_seed
      hG T hempty hM hmany hJ hu hne U c d hd π hp hs hnt
    have hres := source_localAction_proper_orbit_seed_residual
      hG T hempty hM hmany hJ hu hne U c d hd π hp hs hnt
    exact ⟨_,Or.inr ⟨hproper,rfl⟩,hWM,hnW,hEW,hres⟩
/-- Original chosen-module residual conclusions, with every source case discharged. -/
theorem source_lemma_15_1_6_and_15_1_9_4_centralizing
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∃ (U : Submodule (ZMod 2) (Additive V)) (W : Subgroup G),
      (W = V ∨ (SourceCases.Proper T M Mc V ρ U ∧
        W = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype)) ∧
      W ≤ M ∧ M ≤ normalizer (W : Set G) ∧ IsElementaryAbelian 2 W ∧
      (pResidual 2 (M ⊓ centralizer (centralInvolutions T : Set G) : Subgroup G)).map
        (M ⊓ centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (W : Set G) ∧
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
        (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (W : Set G) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  obtain ⟨U,c,d,π,hd,_,_,hp,hcases⟩ :=
    source_lemma_15_1_2_centralizing hG T hempty hM hmany hJ hu hne
  obtain ⟨W,hW⟩ := source_centralizing_cases_seed_residual hG T hempty hM hmany hJ hu hne
    U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hcases
  exact ⟨U,W,hW⟩
end CFSG.Quasithin.Chapter15.Section01
