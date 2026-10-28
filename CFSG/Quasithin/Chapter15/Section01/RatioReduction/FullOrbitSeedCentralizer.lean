module
public import CFSG.Quasithin.Chapter15.Section01.ChosenSeedCentralizer
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitNine
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitExtraspecial
/-!
# Odd-image discharge at the E9 and extraspecial source endpoints

The existing source full-orbit theorems identify the marked kernel with
the literal action image's two-residual. Its endpoint order is nine or 27,
so the oddness premise of the central-seed theorem is proved here.
Both O²(C_M(Z)) and every original O²(H∩M) therefore centralize the unchanged V.

Source: Aschbacher–Smith 15.1.2(4–5), 15.1.6 and 15.1.9(4), pp.1086–1089.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

/-- The extraspecial source endpoint discharges the odd-residual premise. -/
theorem source_localAction_extraspecial_seed_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ l : CyclicSource.LocalGeneration (ρ.comp (Jhat ρ).subtype),
      letI := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
      letI : Finite (Additive V) := Module.finite_of_finite (ZMod 2)
      letI : IsElementaryAbelian 2 (Multiplicative (Additive V)) := BinaryGroupAction.elementary
      letI := l.normal
      ChapterD.Section02.ExtraspecialEndpoint (V := Multiplicative (Additive V))
        l.kernel l.involution →
      (pResidual 2 (M ⊓ centralizer (centralInvolutions T : Set G) : Subgroup G)).map
        (M ⊓ centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (V : Set G) ∧
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
        (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (V : Set G) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro l
  let := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
  let : Finite (Additive V) := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative (Additive V)) := BinaryGroupAction.elementary
  let := l.normal
  intro hex
  have hres := source_localAction_extraspecial_residual hG T hM l hex
  have hodd : Odd (Nat.card (pResidual 2 (internalActionImage M V
      (le_normalizer_conjugateSpanBy _ _)))) := by
    rw [←hres,card_map_of_injective (Jhat ρ).subtype_injective,hex.card_kernel]
    decide
  exact ⟨chosen_seed_centralizer_residual_of_odd_residual T hM.1.2
    (localModule_le T hM.1.2) (le_normalizer_conjugateSpanBy _ _) hodd,
    fun H hH => source_15_1_9_4_of_odd_residual hG T hM hH hJ
      (localModule_le T hM.1.2) (le_normalizer_conjugateSpanBy _ _) hodd⟩

/-- The full-orbit elementary-nine source endpoint discharges the same premise. -/
theorem source_localAction_full_orbit_nine_seed_residual
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
    ∀ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (i : d.Index), (∀ j : d.Index,j=i) → U=⊤ →
      (∀ A ∈ QhatStar (d.factor i).action, IsCyclic A) →
    ∀ l : CyclicSource.LocalGeneration (ρ.comp (Jhat ρ).subtype),
      letI := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
      letI : Finite (Additive V) := Module.finite_of_finite (ZMod 2)
      letI : IsElementaryAbelian 2 (Multiplicative (Additive V)) := BinaryGroupAction.elementary
      letI := l.normal
      ChapterD.Section02.ElementaryNineEndpoint (V := Multiplicative (Additive V))
        l.kernel l.involution →
      (pResidual 2 (M ⊓ centralizer (centralInvolutions T : Set G) : Subgroup G)).map
        (M ⊓ centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (V : Set G) ∧
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
        (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (V : Set G) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d hd i hi hU hc l
  let := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
  let : Finite (Additive V) := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative (Additive V)) := BinaryGroupAction.elementary
  let := l.normal
  intro h9
  obtain ⟨_,_,hres,_⟩ := source_localAction_full_orbit_nine hG T hempty hM hmany hJ hu hne
    U c d hd i hi hU hc l h9
  have hodd : Odd (Nat.card (pResidual 2 (internalActionImage M V
      (le_normalizer_conjugateSpanBy _ _)))) := by
    rw [←hres,card_map_of_injective (Jhat ρ).subtype_injective,h9.card_kernel]
    decide
  exact ⟨chosen_seed_centralizer_residual_of_odd_residual T hM.1.2
    (localModule_le T hM.1.2) (le_normalizer_conjugateSpanBy _ _) hodd,
    fun H hH => source_15_1_9_4_of_odd_residual hG T hM hH hJ
      (localModule_le T hM.1.2) (le_normalizer_conjugateSpanBy _ _) hodd⟩
end CFSG.Quasithin.Chapter15.Section01
