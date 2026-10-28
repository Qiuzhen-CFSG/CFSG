module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitDecomposable
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitDihedral
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.OddResidual
/-!
# Odd two-residual of the original dihedral and decomposable images

The actual selected M-action retains its faithful image representation.
A marked singleton dihedral endpoint has odd ambient two-residual by the
small binary normalizer bounds. In the decomposable source branch, the
existing classification supplies precisely two marked factors; their literal
permuted support images give the same conclusion for the original full image.

This discharges the two-nilpotence premise used in original 15.1.6, and hence
in the chosen-seed centralizer argument for 15.1.9(4).
Source: Aschbacher–Smith, printed pp.1084–1087, 15.1.2(1),(3) and 15.1.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_full_orbit_dihedral_odd_twoResidual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (l : CyclicSource.LocalGeneration (ρ.comp (Jhat ρ).subtype)) (p m : ℕ),
      CyclicSource.PrimeDimensionOptions p m → CyclicSource.DihedralMarking l p m →
      Odd (Nat.card (pResidual 2 D)) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro l p m hp hm
  exact hm.odd_ambient_twoResidual
    (imageRepresentation_injective M (localModule T M) (le_normalizer_conjugateSpanBy _ _))
    (Jhat ρ) hp

theorem source_localAction_full_orbit_decomposable_odd_twoResidual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull → U = ⊤ →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      (∀ i j, ∃ g : D, π g i = j) → 1 < Nat.card d.Index →
      Odd (Nat.card (pResidual 2 D)) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d hd hU π hp hs ht hmore
  obtain ⟨hc,p,m,hpm,hmark,_⟩ := source_localAction_full_orbit_decomposable
    hG T hempty hM hmany hJ U c d hd hU π hp hs ht hmore
  exact c.odd_twoResidual_of_two_dihedral_factors d
    (imageRepresentation_injective M (localModule T M) (le_normalizer_conjugateSpanBy _ _))
    hU hc π hp hs hpm hmark
end CFSG.Quasithin.Chapter15.Section01
