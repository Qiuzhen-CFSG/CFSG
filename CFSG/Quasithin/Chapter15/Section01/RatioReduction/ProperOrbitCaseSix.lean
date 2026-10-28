module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperOrbitSingle
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperOrbitIndexThree

/-!
# Source case (6) of 15.1.2 from the original proper-orbit partition

The proper-orbit analysis gives a unique S3 actor and its invariant moved
four-space, with nonzero complementary fixed space and image S3 × S3.
The two literal action kernels lift to the centralizers of these subgroups
of V. Their product with the original Sylow subgroup equals M ∩ Mc and
has index three. All seed, factor-classification and index hypotheses are
discharged from the original selected local action.

Source: Aschbacher--Smith 15.1.2, printed p.1085, conclusion (6).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_proper_orbit_case_six
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
      let Wg := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
      let Fg := (Subgroup.toAddSubgroup.symm (fixedSpace ρ (Jhat ρ)).toAddSubgroup).map V.subtype
      U = subspaceCommutator ρ ⊤ (Jhat ρ) ∧
      Nonempty (Jhat ρ ≃* Equiv.Perm (Fin 3)) ∧
      Module.finrank (ZMod 2) U = 4 ∧
      (⊤ : Subgroup D) ≤ subspaceStabilizer ρ U ∧ U ≠ ⊥ ∧ U ≠ ⊤ ∧
      fixedSpace ρ (Jhat ρ) ≠ ⊥ ∧ IsCompl U (fixedSpace ρ (Jhat ρ)) ∧
      Nonempty (subspaceActionImage ρ U ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      ((M ⊓ centralizer (Wg : Set G) : Subgroup G) : Set G) *
        ((M ⊓ centralizer (Fg : Set G) : Subgroup G) : Set G) * (T : Set G) =
        (M ⊓ Mc : Subgroup G) ∧ (M ⊓ Mc).relIndex M = 3 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d hd π hp hs hnt
  obtain ⟨he,hdim,hstable,hU0,hUt,hF0,hcompl,himage⟩ :=
    source_localAction_proper_orbit_support hG T hempty hM hmany hJ hu hne
      U c d hd π hp hs hnt
  have hHcard : Nat.card (Jhat ρ) = 6 := by
    rcases he with ⟨e⟩
    rw [Nat.card_congr e.toEquiv]
    simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  have hIcard : Nat.card (subspaceActionImage ρ U) = 36 := by
    rcases himage with ⟨e⟩
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  let := Jhat_normal ρ
  obtain ⟨hproduct,hindex⟩ := source_localAction_proper_orbit_centralizer_factorization
    hG T hM hu hne (Jhat ρ) U hstable hU0 hF0 hcompl.sup_eq_top hHcard hIcard
  exact ⟨c.support.symm,he,hdim,hstable,hU0,hUt,hF0,hcompl,himage,hproduct,hindex⟩

/-- The original selected partition gives either the full-orbit branch or all
literal support, centralizer-product and index-three clauses of source case (6). -/
theorem source_centralizing_full_orbit_or_case_six
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
    ∃ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation) (π : D →* Equiv.Perm d.Index),
      d.FittingFull ∧
      (⋃ i, c.ambientBlock d i) = QhatStar ρ ∧ Jhat ρ ≤ π.ker ∧
      (∀ g i,
        Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i = c.ambientBlock d (π g i) ∧
        (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
          (c.ambientFactor d (π g i)).actor ∧
        (c.ambientFactor d i).space.map (ρ g) = (c.ambientFactor d (π g i)).space) ∧
      ((U = ⊤ ∧ ∀ i j, ∃ g : D, π g i = j) ∨
        (let Wg := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
        let Fg := (Subgroup.toAddSubgroup.symm (fixedSpace ρ (Jhat ρ)).toAddSubgroup).map V.subtype
        U = subspaceCommutator ρ ⊤ (Jhat ρ) ∧
        Nonempty (Jhat ρ ≃* Equiv.Perm (Fin 3)) ∧
        Module.finrank (ZMod 2) U = 4 ∧
        (⊤ : Subgroup D) ≤ subspaceStabilizer ρ U ∧ U ≠ ⊥ ∧ U ≠ ⊤ ∧
        fixedSpace ρ (Jhat ρ) ≠ ⊥ ∧ IsCompl U (fixedSpace ρ (Jhat ρ)) ∧
        Nonempty (subspaceActionImage ρ U ≃*
          (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
        ((M ⊓ centralizer (Wg : Set G) : Subgroup G) : Set G) *
          ((M ⊓ centralizer (Fg : Set G) : Subgroup G) : Set G) * (T : Set G) =
          (M ⊓ Mc : Subgroup G) ∧ (M ⊓ Mc).relIndex M = 3)) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  obtain ⟨U,c,d,hd,π,hstars,hker,hp⟩ :=
    source_centralizing_classified_partition hG T hempty hM hmany hJ
  refine ⟨U,c,d,π,hd,hstars,hker,hp,?_⟩
  by_cases hfull : U = ⊤ ∧ ∀ i j, ∃ g, π g i = j
  · exact Or.inl hfull
  · exact Or.inr (source_localAction_proper_orbit_case_six hG T hempty hM hmany hJ hu hne
      U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull)

end CFSG.Quasithin.Chapter15.Section01
