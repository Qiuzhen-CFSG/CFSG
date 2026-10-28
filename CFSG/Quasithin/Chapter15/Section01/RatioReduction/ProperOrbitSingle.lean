module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SupportProjectionSeed
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.OrbitSeedAssembly
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SingletonSupport

/-!
# The unique moved four-space in the proper-orbit case of 15.1.2

The original centralizing action supplies its ratio partition. Outside the
single full-orbit branch, the proper seed analysis and original quasithin
rank bound force a unique factor. Its literal embedded actor is J-hat and
its support is the original moved support. Consequently J-hat is S3, the
support is a globally invariant four-space, and the support image is S3 × S3.
The complement fixed by J-hat is nonzero; the Fitting-moved factor makes the
two spaces complementary. No additional local seed or classification premise
is retained.

Source: Aschbacher--Smith 15.1.2, printed p.1085, conclusion (6) before the
index-three intersection calculation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_proper_orbit_support
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
      Nonempty (Jhat ρ ≃* Equiv.Perm (Fin 3)) ∧
      Module.finrank (ZMod 2) U = 4 ∧
      (⊤ : Subgroup D) ≤ subspaceStabilizer ρ U ∧ U ≠ ⊥ ∧ U ≠ ⊤ ∧
      fixedSpace ρ (Jhat ρ) ≠ ⊥ ∧ IsCompl U (fixedSpace ρ (Jhat ρ)) ∧
      Nonempty (subspaceActionImage ρ U ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d hd π hp hs hnt
  have hproper := (source_localAction_orbit_seed_cases hG T hempty hM hJ hu hne
    U c d π hp).resolve_left hnt
  obtain ⟨i,hi,hdim,himage⟩ := source_localAction_proper_orbits_unique_factor
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hproper
  have he := source_localAction_all_symmetricThree_of_proper_orbits
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hproper
  have ha := c.unique_factor_actor d i hi
  have hw := c.unique_factor_space d i hi
  let := Jhat_normal ρ
  have hc := c.ambient_space_fixed_compl d (source_localAction_twoCore hG T hM) hd i
  have hc' : IsCompl U (fixedSpace ρ (Jhat ρ)) := by
    simpa only [ha,hw] using hc
  refine ⟨⟨(c.unique_factor_equiv d i hi).symm.trans (he i).some⟩,
    (c.unique_factor_finrank d i hi).trans hdim,?_,?_,?_,
    c.unique_factor_fixed_space_ne_bot d i hi π hnt,hc',?_⟩
  · have ht := c.unique_factor_support_stabilizer d i hi π hs
    simpa only [hw,ht] using (show (⊤ : Subgroup _) ≤
      subspaceStabilizer ρ (c.ambientFactor d i).space from ht.symm ▸ le_rfl)
  · intro hb
    exact c.ambient_space_ne_bot d i (hw.trans hb)
  · intro ht
    exact c.unique_factor_space_ne_top_of_not_full_orbit d i hi π hnt (hw.trans ht)
  · exact Eq.mp (congrArg (fun W : Submodule (ZMod 2) (Additive (localModule T M)) =>
      Nonempty (subspaceActionImage ρ W ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) hw) himage

/-- The actual original partition is a single full orbit, or supplies the
S3 moved four-space and nonzero fixed complement in source case (6). -/
theorem source_centralizing_full_orbit_or_case_six_support
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
        (Nonempty (Jhat ρ ≃* Equiv.Perm (Fin 3)) ∧
        Module.finrank (ZMod 2) U = 4 ∧
        (⊤ : Subgroup D) ≤ subspaceStabilizer ρ U ∧ U ≠ ⊥ ∧ U ≠ ⊤ ∧
        fixedSpace ρ (Jhat ρ) ≠ ⊥ ∧ IsCompl U (fixedSpace ρ (Jhat ρ)) ∧
        Nonempty (subspaceActionImage ρ U ≃*
          (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  obtain ⟨U,c,d,hd,π,hstars,hker,hp⟩ :=
    source_centralizing_classified_partition hG T hempty hM hmany hJ
  refine ⟨U,c,d,π,hd,hstars,hker,hp,?_⟩
  by_cases hfull : U = ⊤ ∧ ∀ i j, ∃ g, π g i = j
  · exact Or.inl hfull
  · exact Or.inr (source_localAction_proper_orbit_support hG T hempty hM hmany hJ hu hne
      U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull)

end CFSG.Quasithin.Chapter15.Section01
