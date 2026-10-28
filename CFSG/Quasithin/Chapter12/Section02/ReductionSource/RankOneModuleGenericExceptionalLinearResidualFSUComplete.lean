module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowOffender
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit.SourceComplete
public import CFSG.Quasithin.Chapter3.Section02.LinearThreeFourGraphFixedSpace
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualFSURecognition

/-!
# The complete PSL₃(4) FSU diagram exclusion

The original seed has zero fixed space by the source Thompson argument and
is therefore irreducible on its component. Its faithful component image is
exactly PSL₃(4), so the quadratic-ratio theorem excludes FF action. If T moved
the seed, the proved D.3.5 cubic-orbit calculation would make that same seed
FF. Thus T fixes it, and the FSU component action is irreducible. Hermitian
recognition and the literal graph-actor contradiction finish the exclusion.

These deductions need only Hypothesis12.2.1 and the multiple-overgroup guard;
no ambient rank-two or sporadic exclusion is used. The universal FSU theorem
selects a homogeneous seed for the same G, T and K using the earlier source
selection theorem. It then discharges the exact shared
`LinearFourFSUDiagramExclusion` interface.

The final residual applications remove the FSU callback completely.
Maximality, equivalently the remaining containing-component exclusion on
this route, stays with qt-d-1222-linear-residual-maximal-nonfaithful. Final
5.1.14 assembly remains with qt-d-1222-rankone-exceptional-linear-analysis.
Source: Aschbacher–Smith D.3.5(2), 3.2.3–9 and5.1.14, printed pp.195–196,
580–583 and638 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {K V : Subgroup G}
  (D : ChosenModule T K V)
include D

private theorem componentImage_linearThreeFour
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    ClassicalGroup.IsPSL D.componentImage 3 4 := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hlinear
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,
      Group.IsPerfect.center_quotient_center_eq_bot SL(3,F), Subgroup.card_bot]
  let : IsSimpleGroup ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) := IsQuasisimple.simple
  let : IsSimpleGroup (K ⧸ pCore 2 K) :=
    (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm).isSimpleGroup
  have hi : Function.Injective D.componentQuotientHom := by
    apply (MonoidHom.ker_eq_bot_iff D.componentQuotientHom).mp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D.componentQuotientHom.ker inferInstance with hb | ht
    · exact hb
    · have htr : ∀ x : D.componentImage, x = 1 := by
        intro x
        obtain ⟨y,rfl⟩ := D.componentQuotientHom_surjective x
        exact ht.ge (mem_top y)
      have hs : Subsingleton D.componentImage := ⟨fun x y => (htr x).trans (htr y).symm⟩
      exact (not_subsingleton D.componentImage hs).elim
  let q := MulEquiv.ofBijective D.componentQuotientHom ⟨hi,D.componentQuotientHom_surjective⟩
  exact ⟨F,hF,hfin,hcard,⟨q.symm.trans e⟩⟩

/-- The original irreducible seed is non-FF under its actual stabilizer action. -/
theorem linearThreeFour_seed_notFF
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T K)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    ¬ IsFFModule D.seedRepresentation := by
  have hc : V ⊓ centralizer (K : Set G) = ⊥ := by
    simpa only [D.fundamentalSetup_seed h] using
      (D.fundamentalSetup h).linearThreeFour_seed_centralizer_eq_bot
        hmany D.sylow_normalizes_component hlinear
  exact ChapterK.Linear.Recognition.PSL3FourExclusion.not_isFFModule
    (D.seed_sqtk h (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X)))
    (D.seed_fitting h.quasisimple) (D.componentImage_linearThreeFour hlinear)
    (subspaceImageRepresentation_injective _ _) (D.seed_irreducible hc)

/-- A moved seed would be FF by the cubic-orbit theorem; hence T fixes it. -/
theorem linearThreeFour_sylowOrbit_eq
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T K)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    componentOrbit V (T : Subgroup G) = V := by
  have hc : V ⊓ centralizer (K : Set G) = ⊥ := by
    simpa only [D.fundamentalSetup_seed h] using
      (D.fundamentalSetup h).linearThreeFour_seed_centralizer_eq_bot
        hmany D.sylow_normalizes_component hlinear
  by_contra hn
  exact D.linearThreeFour_seed_notFF h hmany hlinear
    (D.seed_ff_of_moved h
      (D.orbit_cubicRatio_le_source h (Chapter3.hasMaximalOutside_of_many T hmany)) hc
      (lt_of_le_of_ne (le_componentOrbit _ _) (Ne.symm hn)))

/-- The now invariant seed supplies the forbidden irreducible graph-acting FSU. -/
theorem linearThreeFour_not_graph
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T K)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ¬ HasLinearFourGraphAction (T : Subgroup G) K := by
  intro hg
  have hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 := by
    obtain ⟨F,hF,hfin,hcard,e,_⟩ := hg
    exact ⟨F,hF,hfin,hcard,⟨e⟩⟩
  have he : (D.fundamentalSetup h).seed = (D.fundamentalSetup h).moduleSubgroup := by
    rw [D.fundamentalSetup_seed,D.fundamentalSetup_module,D.linearThreeFour_sylowOrbit_eq h hmany hlinear]
  exact linear_four_graph_fsu_not_irreducible (D.fundamentalSetup h) hmany
    D.sylow_normalizes_component hg
    ((D.fundamentalSetup h).linearThreeFour_irreducible_of_seed_eq_module hmany
      D.sylow_normalizes_component hlinear he)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The literal FSU excludes diagram actors; all seed alternatives are discharged. -/
theorem linearFourFSUDiagramExclusion : LinearFourFSUDiagramExclusion G := by
  intro T K hmany D hn
  let h : Hypothesis1221 KnownSimple.IsKnownSimple T K :=
    ⟨D.simpleQTKE,⟨D.maximal,D.faithful⟩,D.quasisimple⟩
  obtain ⟨V,⟨F⟩⟩ := h.exists_chosen_of_normalizes hn
  exact F.linearThreeFour_not_graph h hmany

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- For the actual H-star residual, maximality is now the only remaining premise. -/
theorem linear_residual_nonfaithful_of_maximal
    {T : Sylow 2 G} {M H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G)) :
    ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H) := by
  intro hf
  obtain ⟨D⟩ := linear_residual_fundamentalSetup hG hlinear hmax hf
  exact linearFourFSUDiagramExclusion T (residual H) hmany D
    (hH.1.1.2.trans (le_normalizer_residual H))
    (linear_residual_graph_action T hTM hH hlinear)

/-- The literal assembly with the FSU exclusion discharged. -/
theorem linear_residual_maximal_nonfaithful_of_embedding_exclusion
    {T : Sylow 2 G} {M H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hemb : LinearFourEmbeddingExclusion G) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∧
      ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H) :=
  linear_residual_maximal_nonfaithful_of_exclusions hG hmany hTM hH hlinear hemb
    linearFourFSUDiagramExclusion

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
