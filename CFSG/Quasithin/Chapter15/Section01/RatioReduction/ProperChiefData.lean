module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperOmegaRatios
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperWholeRatio
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ChosenSourceInputs
/-!
# Chief-factor data for the original proper chosen module

The proper source partition supplies its actual moved subgroup W and
natural omega coordinates. Its quadratic ratio is two. Independently, the
ratio-preserving factor datum gives cubic ratio two on the whole original
module, which places W in every relevant local two-core.

Applying the chosen-module minimal-actor equality theorem to these derived
inputs gives exactly two noncentral chief factors on the literal H-conjugate
span of W. No core, numeric ratio, solvability, coordinate or dual-FF premise
is retained. The complete minimal-actor equality family remains available at
the stable chosen-module interface in ChosenSourceInputs.

Source: Aschbacher--Smith 15.1.2(6), 15.1.4, 15.1.8,
15.1.11 and 15.1.12(1--2), printed pp.1085--1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Theory.GroupTheory Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]
theorem source_localAction_proper_orbit_chief_data
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
        cubicRatio (imageRepresentation M W hMW) = 3 / 2 ∧
        quadraticRatio (imageRepresentation M W hMW) = 2 ∧
        ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
          W ≤ twoCoreIn H ∧
          IsElementaryAbelian 2 (conjugateSpan H W) ∧
          ∀ s : NoncentralChiefRefinement.SeriesOn ((conjugateSpan H W).subgroupOf H),
            s.noncentralCount = 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  dsimp only
  intro U c d hd π hp hs hnt
  let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
  obtain ⟨hEW,hMW,x,e,hcoord,hcub,hquad⟩ := source_localAction_proper_orbit_chosen_omega_ratios
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hnt
  let := hEW
  obtain ⟨hWM,hWne,_,_,hspan⟩ := source_localAction_proper_orbit_chosen_seed
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hnt
  refine ⟨hEW,hMW,hcub,hquad,?_⟩
  intro H hH
  obtain ⟨_,hcore,hE⟩ := source_localAction_proper_orbit_inside_all_cores
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hnt H hH
  refine ⟨hcore,?_,?_⟩
  · exact source_chosen_elementary_span hG T hempty hM hH hJ
      hWM hWne hMW hspan hcore hquad
  · intro s
    obtain ⟨hqN,hdual,A,hA,hout,hquadratic,hmin,hseries⟩ :=
      source_chosen_minimal_actor_equalities hG T hempty hM hH hJ
        hWM hWne hMW hspan (map_subtype_le _) hcore hquad
    exact (hseries s).1

end CFSG.Quasithin.Chapter15.Section01
