module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperChosenSource
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SupportAction
public import Theory.SpecificGroups.OrthogonalFourBinary.OmegaRatios

/-!
# Both source ratios on the actual proper chosen module

The proper-orbit classification gives coordinates on the invariant support U.
The literal inclusion U → W identifies this support with the chosen ambient
subgroup W, and the quotient action equivalence preserves every original
conjugating element. These coordinates therefore intertwine the actual action
on W with the genuine Siegel-generated omega action. Its computed cubic and
quadratic ratios are three halves and two, respectively.

Source: Aschbacher–Smith, original 15.1.2(6), 15.1.4 and 15.1.8, pp.1085–1088.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

/-- Original proper-branch hypotheses discharge all coordinate and numeric premises
for the action on the literal chosen ambient subgroup. -/
theorem source_localAction_proper_orbit_chosen_omega_ratios
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
      ∃ hEW : IsElementaryAbelian 2 W,
        letI := hEW
        ∃ hMW : M ≤ normalizer (W : Set G),
          ∃ (x : Additive W ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
            (e : internalActionImage M W hMW ≃* OrthogonalFourBinary.omega),
            (∀ g w, x (imageRepresentation M W hMW g w) = (e g).val.val (x w)) ∧
            cubicRatio (imageRepresentation M W hMW) = 3 / 2 ∧
            quadraticRatio (imageRepresentation M W hMW) = 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d hd π hp hs hnt
  let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
  obtain ⟨_,_,hMW,hEW,_⟩ := source_localAction_proper_orbit_chosen_seed
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hnt
  let := hEW
  obtain ⟨_,_,hstable,_⟩ := source_localAction_proper_orbit_support
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hnt
  obtain ⟨x,e,he⟩ := source_localAction_proper_orbit_omega
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hnt
  let a := supportActionEquiv M V (le_normalizer_conjugateSpanBy _ _) U hstable hMW
  let l := supportLinearEquiv V U
  let xW := l.symm.trans x
  let eW := a.trans e
  have hcoord : ∀ g w, xW (imageRepresentation M W hMW g w) =
      (eW g).val.val (xW w) := by
    intro g w
    change x (l.symm (imageRepresentation M W hMW g w)) =
      (e (a g)).val.val (x (l.symm w))
    exact (congrArg x (supportActionEquiv_intertwines_symm M V
      (le_normalizer_conjugateSpanBy _ _) U hstable hMW g w)).trans (he _ _)
  exact ⟨hEW,hMW,xW,eW,hcoord,
    OrthogonalFourBinary.ratios_of_omega_coordinates (imageRepresentation M W hMW) xW eW hcoord⟩

end CFSG.Quasithin.Chapter15.Section01
