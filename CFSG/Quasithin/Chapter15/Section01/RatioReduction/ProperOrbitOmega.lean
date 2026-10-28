module
public import Theory.Representation.BinarySymmetricThreeNormalizer.Omega
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperOrbitCaseSix

/-!
# The natural Ω-four action in original case (6) of 15.1.2

The proper-orbit source supplies a normal S3, its fully moved binary four-space,
a fixed supplement and a support image of order36. Tensor coordinates on the
marked S3 identify the literal support-image representation with the natural
action of the Siegel-generated Ω4+(2). The supplement is used only to retain
faithfulness of the marked subgroup after restriction; it need not be fixed by
all of the ambient group.

Source: Aschbacher--Smith 15.1.2, printed p.1085, conclusion (6), and the
application in 15.1.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

/-- The literal support action in the proper-orbit source branch is the
natural action of genuine Ω4+(2), with its linear coordinates intertwined. -/
theorem source_localAction_proper_orbit_omega
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
      ∃ (x : U ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
        (e : subspaceActionImage ρ U ≃* OrthogonalFourBinary.omega),
        ∀ g u, x (subspaceImageRepresentation ρ U g u) =
          (e g).val.val (x u) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d hd π hp hs hnt
  obtain ⟨he,hdim,hstable,hU0,hUt,hF0,hcompl,himage⟩ :=
    source_localAction_proper_orbit_support hG T hempty hM hmany hJ hu hne
      U c d hd π hp hs hnt
  let := Jhat_normal ρ
  have hIcard : Nat.card (subspaceActionImage ρ U) = 36 := by
    rcases himage with ⟨e⟩
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  exact BinarySymmetricThreeNormalizer.support_exists_omega_coordinates ρ
    (imageRepresentation_injective _ _ _) (Jhat ρ) he.some U hstable c.support
    hcompl.sup_eq_top hdim hIcard


/-- The original selected local action supplies either the full transitive
partition or the actual natural Ω action of source case (6). -/
theorem source_centralizing_full_orbit_or_omega
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
        ∃ (x : U ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
          (e : subspaceActionImage ρ U ≃* OrthogonalFourBinary.omega),
          ∀ g u, x (subspaceImageRepresentation ρ U g u) =
            (e g).val.val (x u)) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  obtain ⟨U,c,d,hd,π,hstars,hker,hp⟩ :=
    source_centralizing_classified_partition hG T hempty hM hmany hJ
  refine ⟨U,c,d,π,hd,hstars,hker,hp,?_⟩
  by_cases hfull : U = ⊤ ∧ ∀ i j, ∃ g, π g i = j
  · exact Or.inl hfull
  · exact Or.inr (source_localAction_proper_orbit_omega hG T hempty hM hmany hJ hu hne
      U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull)

end CFSG.Quasithin.Chapter15.Section01
