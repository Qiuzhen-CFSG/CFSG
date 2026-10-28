module
public import CFSG.Quasithin.Chapter15.Section01.ChosenSeedCentralizer
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperChosenSource
public import Theory.SpecificGroups.OrthogonalFourBinary.OddResidual
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SupportAction
/-!
# Central-seed residuals for the actual chosen Omega four-space

The proper source branch supplies Ω₄⁺(2) coordinates on its support image.
The literal subgroup/subspace action equivalence identifies that support
image with the conjugation image on the chosen ambient four-space W.
The odd residual of the concrete isometry group then discharges the image
hypothesis in 15.1.6 and 15.1.9(4), preserving the chosen W throughout.

Source: Aschbacher–Smith 15.1.2(6), 15.1.4–6 and 15.1.9(4), pp.1085–1089.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]


/-- The actual proper-case chosen subgroup satisfies both residual centralizations. -/
theorem source_localAction_proper_orbit_seed_residual
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
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      ¬ (U = ⊤ ∧ ∀ i j, ∃ g : D, π g i = j) →
      let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
      (pResidual 2 (M ⊓ centralizer (centralInvolutions T : Set G) : Subgroup G)).map
        (M ⊓ centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (W : Set G) ∧
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
        (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (W : Set G) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d hd π hp hs hnt
  obtain ⟨hWM,_,hnW,hEW,_⟩ := source_localAction_proper_orbit_chosen_seed
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hnt
  let := hEW
  obtain ⟨_,_,hstable,_⟩ := source_localAction_proper_orbit_support
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hnt
  obtain ⟨_,e,_⟩ := source_localAction_proper_orbit_omega
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hnt
  let a := supportActionEquiv M V (le_normalizer_conjugateSpanBy _ _) U hstable hnW
  let f := OrthogonalFourBinary.omega.subtype.comp (e.toMonoidHom.comp a.toMonoidHom)
  have hf := OrthogonalFourBinary.omega.subtype_injective.comp (e.injective.comp a.injective)
  have hodd := OrthogonalFourBinary.TerminalLines.odd_twoResidual_of_injective f hf
  exact ⟨chosen_seed_centralizer_residual_of_odd_residual T hM.1.2 hWM hnW hodd,
    fun H hH => source_15_1_9_4_of_odd_residual hG T hM hH hJ hWM hnW hodd⟩

/-- Concrete isometry coordinates discharge oddness for the literal chosen action image. -/
theorem chosen_seed_centralizer_residual_of_orthogonal_embedding
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    (hMV : M ≤ normalizer (V : Set G))
    (f : internalActionImage M V hMV →* OrthogonalFourBinary.TerminalLines.IsometryGroup)
    (hf : Function.Injective f) :
    (pResidual 2 (M ⊓ centralizer (centralInvolutions T : Set G) : Subgroup G)).map
      (M ⊓ centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (V : Set G) :=
  chosen_seed_centralizer_residual_of_odd_residual T hTM hVM hMV
    (OrthogonalFourBinary.TerminalLines.odd_twoResidual_of_injective f hf)

/-- The same isometry coordinates give the actual HStar residual centralization. -/
theorem source_15_1_9_4_of_orthogonal_embedding
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hVM : V ≤ M) (hMV : M ≤ normalizer (V : Set G))
    (f : internalActionImage M V hMV →* OrthogonalFourBinary.TerminalLines.IsometryGroup)
    (hf : Function.Injective f) :
    (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (V : Set G) :=
  source_15_1_9_4_of_odd_residual hG T hM hH hJ hVM hMV
    (OrthogonalFourBinary.TerminalLines.odd_twoResidual_of_injective f hf)

end CFSG.Quasithin.Chapter15.Section01
