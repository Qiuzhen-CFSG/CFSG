module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.Decomposable
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.Projection

/-!
# The three original large-action branches of 15.1.15

The branch predicate retains the full classified partition, equivariant
permutation action and Sylow marking on the original module. Only the
ratio-two decomposable action belongs to it. Its dimension conclusion is
proved here; the component reduction and natural-module contradiction are
separate outstanding source arguments, not fields asserting exclusion.

Source: Aschbacher--Smith 15.1.7(4),(6),(7) and 15.1.15--29,
printed pp.1087--1104.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal three large actions, with all partition and action data. -/
def LargeSourceAction (T : Sylow 2 G) (M V : Subgroup G)
    (hn : M ≤ normalizer (V : Set G)) [IsElementaryAbelian 2 V] : Prop :=
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f := (actionHom M V hn).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  ∃ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
    (d : Decomposition c.representation) (π : D →* Equiv.Perm d.Index),
    d.FittingFull ∧ (⋃ i, c.ambientBlock d i) = QhatStar ρ ∧ Jhat ρ ≤ π.ker ∧
    (∀ g i,
      Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i = c.ambientBlock d (π g i) ∧
      (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor ∧
      (c.ambientFactor d i).space.map (ρ g) = (c.ambientFactor d (π g i)).space) ∧
    (SourceCases.Nine ρ S ∨ SourceCases.Extraspecial ρ S ∨
      (SourceCases.Decomposable ρ (T : Subgroup G) M f c d π ∧ cubicRatio ρ = 2))

/-- The three source rows have dimensions four, six, and eight. -/
theorem LargeSourceAction.dimensions {T : Sylow 2 G} {M V : Subgroup G}
    {hn : M ≤ normalizer (V : Set G)} [IsElementaryAbelian 2 V]
    (h : LargeSourceAction T M V hn) :
    Module.finrank (ZMod 2) (Additive V) = 4 ∨
      Module.finrank (ZMod 2) (Additive V) = 6 ∨
      Module.finrank (ZMod 2) (Additive V) = 8 := by
  obtain ⟨U,c,d,π,_,_,_,_,hcases⟩ := h
  rcases hcases with h9 | he | ⟨hd,hq⟩
  · obtain ⟨l,_,hdim,_⟩ := h9
    exact Or.inl hdim
  · obtain ⟨l,_,_,_,_,_,hdim,_⟩ := he
    exact Or.inr (Or.inl hdim)
  · exact Or.inr (Or.inr (hd.ratio_two_dimensions hq).1)

/-- Actual full-module application; no smaller chosen support is substituted. -/
theorem PreparedChosenModule.large_source_dimensions
    (T : Sylow 2 G) {M : Subgroup G}
    (h : PreparedChosenModule T M (localModule T M))
    (ha : letI := h.elementary
      LargeSourceAction T M (localModule T M) h.normalized) :
    letI := h.elementary
    Module.finrank (ZMod 2) (Additive (localModule T M)) = 4 ∨
      Module.finrank (ZMod 2) (Additive (localModule T M)) = 6 ∨
      Module.finrank (ZMod 2) (Additive (localModule T M)) = 8 := by
  let := h.elementary
  exact ha.dimensions

/-- Apply the branch separation to the actual source classification.
The decomposable action of ratio different from two is retained explicitly. -/
theorem source_centralizing_small_or_large
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
    let hn := le_normalizer_conjugateSpanBy (centralInvolutions T) M
    let D := internalActionImage M V hn
    let ρ := imageRepresentation M V hn
    let f := (actionHom M V hn).rangeRestrict
    ∃ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation) (π : D →* Equiv.Perm d.Index),
      d.FittingFull ∧ (⋃ i, c.ambientBlock d i) = QhatStar ρ ∧ Jhat ρ ≤ π.ker ∧
      (∀ g i,
        Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i = c.ambientBlock d (π g i) ∧
        (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
          (c.ambientFactor d (π g i)).actor ∧
        (c.ambientFactor d i).space.map (ρ g) = (c.ambientFactor d (π g i)).space) ∧
      (SourceCases.Dihedral ρ ∨ SourceCases.Omega ρ ∨ SourceCases.Proper T M Mc V ρ U ∨
        (SourceCases.Decomposable ρ (T : Subgroup G) M f c d π ∧ cubicRatio ρ ≠ 2) ∨
        LargeSourceAction T M V hn) := by
  classical
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  obtain ⟨U,c,d,π,hd,hstars,hker,hperm,hcases⟩ :=
    source_lemma_15_1_2_centralizing hG T hempty hM hmany hJ hu hne
  refine ⟨U,c,d,π,hd,hstars,hker,hperm,?_⟩
  rcases hcases with hD | hO | hdec | hE | hN | hP
  · exact Or.inl hD
  · exact Or.inr (Or.inl hO)
  · by_cases hq : cubicRatio (imageRepresentation M (localModule T M)
        (le_normalizer_conjugateSpanBy _ _)) = 2
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨U,c,d,π,hd,hstars,hker,hperm,Or.inr (Or.inr ⟨hdec,hq⟩)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hdec,hq⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨U,c,d,π,hd,hstars,hker,hperm,Or.inr (Or.inl hE)⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨U,c,d,π,hd,hstars,hker,hperm,Or.inl hN⟩)))
  · exact Or.inr (Or.inr (Or.inl hP))

end CFSG.Quasithin.Chapter15.Section01
